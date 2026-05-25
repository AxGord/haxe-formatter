package formatter;

#if (sys || nodejs)
import sys.FileSystem;
import sys.io.File;
#end
import formatter.codedata.CodeLines;
import formatter.codedata.FormatterInputData;
import formatter.codedata.ParsedCode;
import formatter.config.Config;
import formatter.marker.Indenter;
import formatter.marker.MarkAdditionalIndentation;
import formatter.marker.MarkEmptyLines;
import formatter.marker.MarkLineEnds;
import formatter.marker.MarkSameLine;
import formatter.marker.MarkTokenText;
import formatter.marker.MarkWhitespace;
import formatter.marker.wrapping.MarkWrapping;
import haxe.CallStack;
import haxe.io.Path;
import tokentree.TokenTree;
import tokentree.TokenTree.FilterResult;
import tokentree.TokenTreeBuilder.TokenTreeEntryPoint;
import tokentree.utils.TokenTreeCheckUtils;
import tokentree.utils.TokenTreeCheckUtils.BrOpenType;

enum Result {
	Success(formattedCode:String);
	Failure(errorMessage:String);
	Disabled;
}

class Formatter {
	static inline var FORMATTER_JSON:String = "hxformat.json";

	public static function format(input:FormatterInput, ?config:Config, ?lineSeparator:String, ?entryPoint:TokenTreeEntryPoint, ?range:FormatterInputRange,
			?indentOffset:Int):Result {
		if (config == null) {
			config = new Config();
		}
		var inputData:FormatterInputData;
		switch (input) {
			#if (sys || nodejs)
			case FileInput(fileName):
				if (!FileSystem.exists(fileName)) {
					Sys.println('Skipping \'$fileName\' (path does not exist)');
					return Failure('File "$fileName" not found');
				}
				var content:Bytes = File.getBytes(fileName);
				inputData = {
					fileName: fileName,
					content: content,
					config: config,
					lineSeparator: lineSeparator,
					entryPoint: entryPoint,
					range: range,
					indentOffset: indentOffset
				};
				return formatInputData(inputData);
			#end
			case Code(code, origin):
				var content:Bytes = Bytes.ofString(code);
				inputData = {
					fileName: switch (origin) {
						case SourceFile(fileName): fileName;
						case Snippet: "code snippet";
					},
					content: content,
					config: config,
					lineSeparator: lineSeparator,
					entryPoint: entryPoint,
					range: range,
					indentOffset: indentOffset
				};
				return formatInputData(inputData);
			case Tokens(tokenList, tokenTree, code, origin):
				inputData = {
					fileName: switch (origin) {
						case SourceFile(fileName): fileName;
						case Snippet: "code snippet";
					},
					content: code,
					tokenList: tokenList,
					tokenTree: tokenTree,
					config: config,
					lineSeparator: lineSeparator,
					entryPoint: entryPoint,
					range: range,
					indentOffset: indentOffset
				};
				return formatInputData(inputData);
		}
		return Failure("implement me");
	}

	#if (sys || nodejs)
	/**
		Determines the config to be used for a particular `path` (either a directory or a file),
		based on the `hxformat.json` that is closest to it.

		If there is no `hxformat.json`, `null` is returned.
	**/
	public static function loadConfig(path:String):Null<Config> {
		var configFileName:Null<String> = determineConfig(path);
		if (configFileName == null) {
			return null;
		}
		var config = new Config();
		config.readConfig(configFileName);
		return config;
	}
	#end

	static function formatInputData(inputData:FormatterInputData):Result {
		try {
			var config:Config = inputData.config;
			if (config.disableFormatting) {
				return Disabled;
			}
			if (config.isExcluded(inputData.fileName)) {
				return Disabled;
			}

			tokentree.TokenStream.MODE = Relaxed;
			var parsedCode = new ParsedCode(inputData);
			FormatStats.addOrigLines(parsedCode.lines.length);

			var indenter = new Indenter(config.indentation);
			indenter.setParsedCode(parsedCode);
			if (inputData.indentOffset != null) {
				indenter.setIndentOffset(inputData.indentOffset);
			}

			var markTokenText = new MarkTokenText(config, parsedCode, indenter);
			var markWhitespace = new MarkWhitespace(config, parsedCode, indenter);
			var markLineEnds = new MarkLineEnds(config, parsedCode, indenter);
			var markSameLine = new MarkSameLine(config, parsedCode, indenter);
			var markWrapping = new MarkWrapping(config, parsedCode, indenter);
			var markEmptyLines = new MarkEmptyLines(config, parsedCode, indenter);
			var markAdditionalIndent = new MarkAdditionalIndentation(config, parsedCode, indenter);

			markTokenText.run();
			fixupAmbiguousBrOpenTypes(parsedCode);
			reparentMisplacedFieldTrailingComments(parsedCode);
			markWhitespace.run();
			markLineEnds.run();
			markSameLine.run();
			markWrapping.run();
			markEmptyLines.run();

			markTokenText.finalRun();
			markAdditionalIndent.run();

			var outputLineEnds:String = MarkLineEnds.outputLineSeparator(config.lineEnds, parsedCode);
			var lines:CodeLines = new CodeLines(parsedCode, indenter, inputData.range);
			lines.applyWrapping(config.wrapping, outputLineEnds);
			markEmptyLines.finalRun(lines);

			var formatted:String = lines.print(outputLineEnds);
			FormatStats.addFormattedLines(formatted.split(outputLineEnds).length);
			return Success(formatted);
		} catch (e:Any) {
			var callstack = CallStack.toString(CallStack.exceptionStack());
			return Failure(e + "\n" + callstack + "\n\n");
		}
	}

	/**
	 * tokentree 1.2.18 classifies `{...}` inside `for body ({...})` as `Unknown`
	 * because the enclosing POpen's parent is `for` → POpenType=ForLoop → BrOpenType=Unknown.
	 * Downstream passes then treat the struct as `unknownBraces` instead of
	 * `objectLiteralBraces`, breaking whitespace / line-end / wrapping.
	 *
	 * Walk all BrOpen tokens once, before any pass runs, and rewrite Unknown to the
	 * shape suggested by the children. The result is cached on the TokenTree, so every
	 * subsequent `getBrOpenType` call picks up the corrected type.
	 */
	@:access(tokentree.TokenTree)
	static function fixupAmbiguousBrOpenTypes(parsedCode:ParsedCode):Void {
		final brOpens:Array<TokenTree> = parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			return token.tok.match(BrOpen) ? FoundGoDeeper : GoDeeper;
		});
		for (brOpen in brOpens) {
			if (TokenTreeCheckUtils.getBrOpenType(brOpen) != Unknown) continue;
			final inferred:BrOpenType = inferBrOpenTypeFromChildren(brOpen);
			if (inferred == Unknown) continue;
			brOpen.tokenTypeCache.brOpenType = inferred;
		}
	}

	/**
	 * tokentree 1.2.18 mis-parents standalone trailing comments after an `abstract
	 *  function name():(args)->Ret;`-style field — the comment ends up as a child
	 *  of the function name CIdent (deep inside the field subtree) instead of as
	 *  a sibling of the field in the enclosing class body. Downstream this confuses
	 *  Indenter (extra +1 indent) and MarkEmptyLines (empty line ends up AFTER the
	 *  comment instead of between `;` and `//`).
	 *
	 *  Walk every comment whose enclosing tree chain reaches a `Kwd(KwdFunction)`/
	 *  `Kwd(KwdVar)`/`Kwd(KwdFinal)` field BEFORE hitting a `BrOpen` (so comments
	 *  inside function bodies are excluded), the comment's source index sits AFTER
	 *  the field's terminating `Semicolon`, and the field's parent is a `BrOpen`.
	 *  Then move the comment out of the field subtree into the field's parent at
	 *  the slot right after the field.
	 */
	@:access(tokentree.TokenTree)
	static function reparentMisplacedFieldTrailingComments(parsedCode:ParsedCode):Void {
		final comments:Array<TokenTree> = parsedCode.root.filterCallback(function(t:TokenTree, i:Int):FilterResult {
			return switch t.tok {
				case Comment(_), CommentLine(_): FoundGoDeeper;
				case _: GoDeeper;
			}
		});
		for (cmt in comments) {
			if (!parsedCode.isOriginalNewlineBefore(cmt)) continue;
			var p:Null<TokenTree> = cmt.parent;
			var fieldKwd:Null<TokenTree> = null;
			while (p != null && p.tok != Root) {
				switch (p.tok) {
					case Kwd(KwdFunction), Kwd(KwdVar), Kwd(KwdFinal):
						fieldKwd = p;
						break;
					case BrOpen:
						break;
					default:
						p = p.parent;
				}
			}
			if (fieldKwd == null) continue;
			final newParent:Null<TokenTree> = fieldKwd.parent;
			if (newParent == null) continue;
			if (!newParent.tok.match(BrOpen)) continue;
			final fieldSemicolon:Null<TokenTree> = findDeepestSemicolon(fieldKwd, cmt.index);
			if (fieldSemicolon == null) continue;
			if (cmt.index <= fieldSemicolon.index) continue;
			final origParent:Null<TokenTree> = cmt.parent;
			if (origParent == null || origParent.children == null) continue;
			if (newParent.children == null) continue;
			final fieldIdx:Int = newParent.children.indexOf(fieldKwd);
			if (fieldIdx < 0) continue;
			origParent.children.remove(cmt);
			final origPrevSib:Null<TokenTree> = cmt.previousSibling;
			final origNextSib:Null<TokenTree> = cmt.nextSibling;
			if (origPrevSib != null) origPrevSib.nextSibling = origNextSib;
			if (origNextSib != null) origNextSib.previousSibling = origPrevSib;
			cmt.parent = newParent;
			// Insert after the field; earlier iterations may already have moved other
			// trailing comments here — keep them in textual (index) order.
			var insertAt:Int = fieldIdx + 1;
			while (insertAt < newParent.children.length) {
				final sib:TokenTree = newParent.children[insertAt];
				if (sib.index > cmt.index) break;
				insertAt++;
			}
			newParent.children.insert(insertAt, cmt);
			final newPrev:TokenTree = newParent.children[insertAt - 1];
			final newNext:Null<TokenTree> = (insertAt + 1 < newParent.children.length) ? newParent.children[insertAt + 1] : null;
			cmt.previousSibling = newPrev;
			cmt.nextSibling = newNext;
			newPrev.nextSibling = cmt;
			if (newNext != null) newNext.previousSibling = cmt;
		}
	}

	static function findDeepestSemicolon(root:TokenTree, beforeIndex:Int):Null<TokenTree> {
		var found:Null<TokenTree> = null;
		function walk(t:TokenTree):Void {
			if (t.children == null) return;
			for (c in t.children) {
				if (c.index >= beforeIndex) continue;
				if (c.tok.match(Semicolon)) {
					if (found == null || c.index > found.index) found = c;
				}
				walk(c);
			}
		}
		walk(root);
		return found;
	}

	static function inferBrOpenTypeFromChildren(token:TokenTree):BrOpenType {
		if (token.children == null || token.children.length == 0) return Unknown;
		for (child in token.children) {
			switch (child.tok) {
				case BrClose:
					return ObjectDecl;
				case Const(CIdent(_)), Const(CString(_)):
					return child.access().firstChild().matches(DblDot).exists() ? ObjectDecl : Block;
				case At, Comment(_), CommentLine(_), Sharp(_):
				default:
					return Block;
			}
		}
		return ObjectDecl;
	}

	#if (sys || nodejs)
	static function determineConfig(fileName:String):Null<String> {
		var path:String = FileSystem.absolutePath(fileName);
		if (!FileSystem.isDirectory(path)) {
			path = Path.directory(path);
		}
		while (path.length > 0) {
			var configFile:String = Path.join([path, FORMATTER_JSON]);
			if (sys.FileSystem.exists(configFile)) {
				return configFile;
			}
			path = Path.normalize(Path.join([path, ".."]));
		}
		return null;
	}
	#end

	#if (js && !nodejs)
	public static function main() {
		var result:Result = Formatter.format(Code(" trace ( 'foo' ) ; ", Snippet), new Config(), ExpressionLevel);
		switch (result) {
			case Success(formattedCode):
				js.Browser.console.log("Success: " + formattedCode);
			case Failure(errorMessage):
				js.Browser.console.log("Failed to format: " + errorMessage);
			case Disabled:
				js.Browser.console.log("Formatting disabled");
		}
	}
	#end
}

enum FormatterInput {
	#if (sys || nodejs)
	FileInput(fileName:String);
	#end
	Code(code:String, origin:CodeOrigin);
	Tokens(tokenList:Array<Token>, tokenTree:TokenTree, code:Bytes, origin:CodeOrigin);
}

enum CodeOrigin {
	SourceFile(fileName:String);
	Snippet;
}
