package formatter.marker.wrapping;

import formatter.codedata.ParsedCode;
import formatter.config.Config;
import formatter.config.WrapConfig;
#if debugWrapping
import haxe.PosInfos;
import sys.io.File;
import sys.io.FileOutput;
#end

#if (!macro && !debugWrapping)
@:build(formatter.debug.PosInfosMacro.clean())
#end
class MarkWrappingBase extends MarkerBase {
	var wrappingQueue:Array<WrappingPlace>;

	public function new(config:Config, parsedCode:ParsedCode, indenter:Indenter) {
		super(config, parsedCode, indenter);
		wrappingQueue = [];
	}

	public function noWrap(open:TokenTree, close:TokenTree) {
		var colon:Null<TokenTree> = open.access().matches(BrOpen).parent().matches(DblDot).token;
		if (colon != null) {
			var type:ColonType = TokenTreeCheckUtils.getColonType(colon);
			switch (type) {
				case SwitchCase:
				case TypeHint:
				case TypeCheck:
				case Ternary:
				case ObjectLiteral:
					noLineEndBefore(open);
				case At:
				case Unknown:
			}
		}
		noWrappingBetween(open, close);
		if (open.children != null) {
			for (child in open.children) {
				switch (child.tok) {
					case PClose, BrClose, BkClose:
						break;
					case Binop(OpGt):
						continue;
					case Semicolon, Comma:
						continue;
					default:
				}
				var lastChild:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(child);
				if (lastChild == null) {
					continue;
				} else {
					switch (lastChild.tok) {
						case Comma, Semicolon:
							noLineEndAfter(lastChild);
						default:
					}
				}
			}
		}
		noLineEndBefore(close);
	}

	public function keep2(open:TokenTree, close:Null<TokenTree>, items:Array<WrappableItem>, addIndent:Int, location:WrappingLocation) {
		var tokens:Array<TokenTree> = [];
		// BeforeLast wrapping location
		tokens = [for (item in items) item.last];
		if (items.length > 0) {
			tokens.unshift(items[0].first);
		}
		// AfterLast wrapping location
		tokens = tokens.concat([for (item in items) item.first]);
		if (close != null) {
			tokens.push(close);
		}

		tokens.push(close);
		for (token in tokens) {
			if (parsedCode.isOriginalNewlineBefore(token)) {
				lineEndBefore(token);
				additionalIndent(token, addIndent);
			} else {
				noLineEndBefore(token);
				wrapBefore(token, false);
			}
		}
	}

	public function keep(open:TokenTree, close:TokenTree, addIndent:Int) {
		noWrappingBetween(open, close);

		if (open.children != null) {
			for (child in open.children) {
				var last:Bool = false;
				switch (child.tok) {
					case PClose, BrClose, BkClose:
						last = true;
					case Binop(OpGt):
						continue;
					case Semicolon, Comma:
						continue;
					default:
				}
				if (parsedCode.isOriginalNewlineBefore(child)) {
					lineEndBefore(child);
					additionalIndent(child, addIndent);
				} else {
					noLineEndBefore(child);
					wrapBefore(child, false);
				}
				if (last) {
					break;
				}
			}
		}
		if (!parsedCode.isOriginalNewlineBefore(open)) {
			noLineEndBefore(open);
		}
	}

	public function wrapChildOneLineEach2(open:TokenTree, close:TokenTree, items:Array<WrappableItem>, addIndent:Int = 0, location:WrappingLocation,
			keepFirst:Bool = false) {
		if (items.length <= 0) {
			return;
		}
		switch (location) {
			case BeforeLast:
				var item:WrappableItem = items[0];
				additionalIndent(item.first, addIndent);
				lineEndBefore(item.first);
				item = items.pop();
				for (it in items) {
					additionalIndent(it.last, addIndent);
					lineEndBefore(it.last);
				}
				items.push(item);
			case AfterLast:
				for (item in items) {
					additionalIndent(item.first, addIndent);
					lineEndBefore(item.first);
				}
		}
		if (keepFirst) {
			if (open != null) {
				noLineEndAfter(open);
			}
			var lastToken:TokenTree = items[items.length - 1].last;
			switch (lastToken.tok) {
				case Semicolon:
				default:
					var next:TokenInfo = getNextToken(lastToken);
					if (next == null) {
						noLineEndAfter(lastToken);
						return;
					}
					switch (next.token.tok) {
						case Kwd(KwdThis), Kwd(KwdNull), Kwd(KwdNew):
							noLineEndAfter(lastToken);
						case Kwd(_):
						case Semicolon:
						default:
							noLineEndAfter(lastToken);
					}
			}
		} else {
			var lastToken:TokenTree = items[items.length - 1].last;
			if (close != null && lastToken.index == close.index) {
				return;
			}
			var next:TokenInfo = getNextToken(lastToken);
			if (next == null) {
				lineEndAfter(lastToken);
				return;
			}
			switch (next.token.tok) {
				case Kwd(KwdThis) | Kwd(KwdNull) | Kwd(KwdNew):
					lineEndAfter(lastToken);
				case Kwd(_):
				case BrOpen | POpen | BkOpen:
				case Semicolon:
				case Comma:
				default:
					lineEndAfter(lastToken);
			}
		}
	}

	public function wrapChildOneLineEach(open:TokenTree, close:TokenTree, addIndent:Int = 0, keepFirst:Bool = false) {
		if (!keepFirst) {
			lineEndAfter(open);
		}
		if (open.children == null) {
			return;
		}
		for (child in open.children) {
			switch (child.tok) {
				case PClose, BrClose, BkClose:
					if (keepFirst) {
						noLineEndBefore(child);
					}
					return;
				case Binop(OpGt):
					if (keepFirst) {
						noLineEndBefore(child);
					}
					return;
				case Sharp(_):
					wrapChildOneLineEachSharp(child, addIndent, keepFirst);
				case CommentLine(_):
					var prev:Null<TokenInfo> = getPreviousToken(child);
					if (prev != null) {
						if (parsedCode.isOriginalSameLine(child, prev.token)) {
							noLineEndBefore(child);
						}
					}
					lineEndAfter(child);
					additionalIndent(child, addIndent);
					continue;
				default:
					additionalIndent(child, addIndent);
			}
			var lastChild:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(child);
			if (lastChild == null) {
				lineEndAfter(child);
			} else {
				lineEndAfter(lastChild);
			}
		}
		if (close == null) {
			return;
		}
		switch (close.tok) {
			case BrClose, BkClose, PClose:
				lineEndBefore(close);
			default:
		}
	}

	public function wrapChildOneLineEachSharp(sharp:TokenTree, addIndent:Int = 0, keepFirst:Bool = false) {
		var children:Array<TokenTree> = sharp.children;
		var skipFirst:Bool = false;
		lineEndBefore(sharp);
		switch (sharp.tok) {
			case Sharp(MarkLineEnds.SHARP_IF):
				lineEndAfter(TokenTreeCheckUtils.getLastToken(sharp.getFirstChild()));
				skipFirst = true;
			case Sharp(MarkLineEnds.SHARP_ELSE_IF):
				lineEndAfter(TokenTreeCheckUtils.getLastToken(sharp.getFirstChild()));
				skipFirst = true;
			case Sharp(MarkLineEnds.SHARP_ELSE):
				lineEndAfter(sharp);
			case Sharp(MarkLineEnds.SHARP_END):
				lineEndAfter(sharp);
				return;
			default:
		}
		for (child in children) {
			if (skipFirst) {
				skipFirst = false;
				continue;
			}
			switch (child.tok) {
				case PClose, BrClose, BkClose:
					if (keepFirst) {
						whitespace(child, NoneBefore);
					}
					return;
				case Binop(OpGt):
					if (keepFirst) {
						whitespace(child, NoneBefore);
					}
					return;
				case Sharp(_):
					wrapChildOneLineEachSharp(child, addIndent, keepFirst);
				case CommentLine(_):
					var prev:Null<TokenInfo> = getPreviousToken(child);
					if (prev != null) {
						if (parsedCode.isOriginalSameLine(child, prev.token)) {
							noLineEndBefore(child);
						}
					}
					lineEndAfter(child);
					additionalIndent(child, addIndent);
					continue;
				default:
					additionalIndent(child, addIndent);
			}
		}
	}

	public function wrapFillLine2AfterLast(open:TokenTree, close:TokenTree, items:Array<WrappableItem>, maxLineLength:Int, addIndent:Int = 0,
			useTrailing:Bool = false) {
		if (items.length <= 0) {
			return;
		}
		var lineStart:Null<TokenTree> = open;
		if (lineStart == null) {
			lineStart = items[0].first;
		}
		lineStart = findLineStartToken(lineStart);
		if (lineStart == null) {
			return;
		}

		var indent:Int = indenter.calcIndent(lineStart);
		var lineLength:Int = calcLineLengthBefore(open) + indenter.calcAbsoluteIndent(indent) + calcTokenLength(open);
		var first:Bool = false; // true;
		for (item in items) {
			var tokenLength:Int = item.firstLineLength;
			if (!first && (lineLength + tokenLength >= maxLineLength)) {
				lineEndBefore(item.first);
				additionalIndent(item.first, addIndent);
				lineLength = indenter.calcAbsoluteIndent(indent + 1 + addIndent);
				if (item.multiline) {
					lineLength = item.lastLineLength;
				} else {
					lineLength += item.firstLineLength;
				}
				continue;
			} else {
				noLineEndBefore(item.first);
				lineLength += tokenLength;
				first = false;
				if (item.multiline) {
					lineLength = item.lastLineLength;
				}
			}
		}
		if (useTrailing) {
			var lastItem:WrappableItem = items[items.length - 1];
			var lengthAfter:Int = calcLineLengthAfter(lastItem.last);
			if (lineLength + lengthAfter > maxLineLength) {
				lineEndBefore(lastItem.first);
				additionalIndent(lastItem.first, addIndent);
			}
		}
		// Don't remove leading break on Call POpen — callParameter wrapping placed it intentionally
		noLineEndAfter(open);
		wrapAfter(open, false);
	}

	public function wrapFillLineWithLeading2AfterLast(open:TokenTree, close:TokenTree, items:Array<WrappableItem>, maxLineLength:Int, addIndent:Int = 0) {
		if (items.length <= 0) {
			return;
		}
		var lineStart:Null<TokenTree> = open;
		if (lineStart == null) {
			lineStart = items[0].first;
		}
		lineStart = findLineStartToken(lineStart);
		if (lineStart == null) {
			return;
		}

		var indent:Int = indenter.calcIndent(lineStart);
		var lineLength:Int = indenter.calcAbsoluteIndent(indent + 1 + addIndent);
		var first:Bool = true;
		for (item in items) {
			var tokenLength:Int = item.firstLineLength;
			if (lineLength + tokenLength >= maxLineLength) {
				lineEndBefore(item.first);
				additionalIndent(item.first, addIndent);
				lineLength = indenter.calcAbsoluteIndent(indent + 1 + addIndent);
				if (item.multiline) {
					lineLength = item.lastLineLength;
				} else {
					lineLength += item.firstLineLength;
				}
				// Overflow break IS the leading break; subsequent items must pack normally,
				// not be treated as "first" (which would force a redundant leading break
				// before the first item that finally fits — breaking fillLine packing).
				first = false;
				continue;
			} else {
				if (!first) {
					noLineEndBefore(item.first);
				} else {
					lineEndBefore(item.first);
				}
				lineLength += tokenLength;
				first = false;
				if (item.multiline) {
					lineLength = item.lastLineLength;
				}
			}
		}
		var lastItem:WrappableItem = items[items.length - 1];
		switch (lastItem.last.tok) {
			case Semicolon:
			case DblDot:
			case BkClose, BrClose, PClose:
				if (isNewLineAfter(lastItem.last)) {
					lineEndAfter(lastItem.last);
				}
			default:
				lineEndAfter(lastItem.last);
		}
	}

	public function wrapFillLine2BeforeLast(open:TokenTree, close:TokenTree, items:Array<WrappableItem>, maxLineLength:Int, addIndent:Int = 0,
			useTrailing:Bool = false) {
		if (items.length <= 0) {
			return;
		}
		// Block-rooted chain: `findOpAddItemStart` lands on a Block `{` when the parser
		// splits a Sharp-containing chain into siblings at block level. We still need
		// the per-item wrapping (post-#end siblings can easily push the line over
		// maxLineLength), but the "open" here is the function body `{` and the first
		// item is the statement keyword (e.g. KwdReturn). The usual joining ops at
		// open/first-item boundary would collapse `{ return` onto the signature line.
		// Skip just those two; let the rest of the loop wrap post-#end content.
		var blockOpen:Bool = open != null && open.tok.match(BrOpen) && TokenTreeCheckUtils.getBrOpenType(open) == Block;
		var lineStart:Null<TokenTree> = open;
		if (lineStart == null) {
			lineStart = items[0].first;
		}
		lineStart = findLineStartToken(lineStart);
		if (lineStart == null) {
			return;
		}
		var indent:Int = indenter.calcIndent(lineStart);
		var lineLength:Int = calcLineLengthBefore(open) + indenter.calcAbsoluteIndent(indent) + calcTokenLength(open);
		if (blockOpen) {
			// Reset to the first item's own indent — the chain effectively starts there,
			// not on the signature line, and the signature-line length is irrelevant
			// for deciding whether subsequent items overflow. Use the item's indent for
			// `indent` too, so the +1 continuation indent for break lines is computed
			// relative to the in-block chain rather than the function signature.
			indent = indenter.calcIndent(items[0].first);
			lineLength = indenter.calcAbsoluteIndent(indent) + items[0].firstLineLength;
			// Force +1 continuation indent on subsequent break points so post-#end
			// chain items align with the in-#if chain rather than with `{`.
			if (addIndent <= 0) addIndent = 1;
		}
		var first:Bool = true;
		for (item in items) {
			var tokenLength:Int = item.firstLineLength;
			// When a POpen item follows && or || and the parenthesized content
			// wouldn't fit even on a new line, keep "|| (" on the current line
			// and let expression wrapping break inside the parens later.
			var effectiveLength:Int = tokenLength;
			if (item.first.tok.match(POpen)) {
				var prevInfo:Null<TokenInfo> = getPreviousToken(item.first);
				if (prevInfo != null) {
					switch (prevInfo.token.tok) {
						case Binop(OpBoolAnd), Binop(OpBoolOr):
							var wrappedLineLen:Int = indenter.calcAbsoluteIndent(indent + 1 + addIndent) + prevInfo.text.length + tokenLength;
							if (wrappedLineLen >= maxLineLength) {
								effectiveLength = calcTokenLength(item.first);
							}
						default:
					}
				}
			}
			if (!first && (lineLength + effectiveLength >= maxLineLength)) {
				lineLength = indenter.calcAbsoluteIndent(indent + 1 + addIndent);
				var prev:TokenInfo = getPreviousToken(item.first);
				if (prev != null) {
					lineEndBefore(prev.token);
					additionalIndent(prev.token, addIndent);
					lineLength += prev.text.length;
				}
				if (item.multiline) {
					lineLength += item.lastLineLength;
				} else {
					lineLength += item.firstLineLength;
				}
				continue;
			} else {
				if (first) {
					// For a block-rooted chain, the first item is the statement keyword
					// (e.g. KwdReturn). Joining it back onto `open` would collapse
					// `{ return` onto the signature line — leave that break alone.
					if (!blockOpen) {
						noLineEndBefore(item.first);
					}
				} else {
					var prev:TokenInfo = getPreviousToken(item.first);
					if (prev != null) {
						noLineEndBefore(prev.token);
					}
				}
				lineLength += effectiveLength;
				first = false;
				if (item.multiline) {
					lineLength = indenter.calcAbsoluteIndent(indent + 1 + addIndent) + item.lastLineLength;
				}
				// POpen kept on current line in opBoolChain: break after ( and before )
				// so inner chains see the correct line length when they run next.
				if (effectiveLength != tokenLength) {
					lineEndAfter(item.first);
					var pClose:Null<TokenTree> = getCloseToken(item.first);
					if (pClose != null) {
						lineEndBefore(pClose);
					}
					lineLength = indenter.calcAbsoluteIndent(indent + 1 + addIndent);
				}
			}
		}
		if (useTrailing) {
			var lastItem:WrappableItem = items[items.length - 1];
			var lengthAfter:Int = calcLineLengthAfter(lastItem.last);
			var prev:TokenInfo = getPreviousToken(lastItem.first);
			if ((prev != null) && (lineLength + lengthAfter > maxLineLength)) {
				// Only add the trailing break if the original input had a break
				// before prev.token — don't create new breaks just for trailing comments.
				var prevPrev:Null<TokenInfo> = getPreviousToken(prev.token);
				if (prevPrev != null && !parsedCode.isOriginalSameLine(prevPrev.token, prev.token)) {
					lineEndBefore(prev.token);
					additionalIndent(prev.token, addIndent + 1);
				}
			}
		}
		// For block-rooted chains, `open` is the function body `{`; joining whatever
		// follows would also collapse `{ return` onto the signature.
		if (!blockOpen) {
			noLineEndAfter(open);
		}
		wrapAfter(open, false);
	}

	public function wrapFillLine(open:TokenTree, close:TokenTree, maxLineLength:Int, addIndent:Int = 0, useTrailing:Bool = false) {
		var lineStart:Null<TokenTree> = findLineStartToken(open);
		if (lineStart == null) {
			return;
		}

		var indent:Int = indenter.calcIndent(lineStart);
		var lineLength:Int = calcLineLengthBefore(open) + indenter.calcAbsoluteIndent(indent + addIndent);
		var first:Bool = true;
		if (open.children == null) {
			return;
		}
		for (child in open.children) {
			switch (child.tok) {
				case PClose, BrClose, BkClose:
					whitespace(child, NoneBefore);
					if (useTrailing) {
						var trailing:Int = calcLineLengthAfter(child);
						if (trailing + lineLength > maxLineLength) {
							var prev:TokenTree = child.previousSibling;
							if (prev == null) {
								return;
							}
							lineEndBefore(prev);
							additionalIndent(prev, addIndent);
						}
					}

					return;
				case Binop(OpGt):
					whitespace(child, NoneBefore);
					return;
				case CommentLine(_):
					var prev:Null<TokenInfo> = getPreviousToken(child);
					if (prev != null) {
						if (parsedCode.isOriginalSameLine(child, prev.token)) {
							noLineEndBefore(child);
						}
					}
					lineEndAfter(child);
					additionalIndent(child, addIndent);
					continue;
				case Kwd(KwdFunction):
					continue;
				case BrOpen:
					continue;
				default:
					additionalIndent(child, addIndent);
			}
			var tokenLength:Int = calcLength(child);
			var lastChild:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(child);
			if (lastChild == null) {
				lastChild = child;
			}
			lineLength += tokenLength;
			if (lineLength > maxLineLength) {
				lineEndBefore(child);
				noLineEndAfter(lastChild);
				indent = indenter.calcIndent(child);
				lineLength = tokenLength + indenter.calcAbsoluteIndent(indent);
			} else {
				noLineEndAfter(lastChild);
			}
			if (first) {
				first = false;
				noLineEndBefore(child);
			}
		}
	}

	override function calcLineLength(token:TokenTree):Int {
		var indent:Int = indenter.calcIndent(token);
		return super.calcLineLength(token) + indenter.calcAbsoluteIndent(indent);
	}

	function hasEmptyFunctionBody(token:TokenTree):Bool {
		var last:Null<TokenTree> = token.getLastChild();
		switch (last.tok) {
			case Semicolon:
				return true;
			default:
		}
		var body:TokenTree = token.nextSibling;
		if (body == null) {
			return true;
		}
		if (body.tok.match(DblDot)) {
			body = body.nextSibling;
		}
		while (body != null && body.tok.match(At)) {
			body = body.nextSibling;
		}
		if (body == null) {
			return true;
		}
		switch (body.tok) {
			case Semicolon:
				return true;
			case BrOpen:
				var brClose:Null<TokenTree> = body.getFirstChild();
				if (brClose == null) {
					return false;
				}
				return brClose.tok.match(BrClose);
			default:
				return false;
		}
	}

	function makeWrappableItems(token:TokenTree):Array<WrappableItem> {
		var items:Array<WrappableItem> = [];
		if (token.children == null) {
			return items;
		}
		collectWrappableItems(token.children, items);
		return items;
	}

	function collectWrappableItems(children:Array<TokenTree>, items:Array<WrappableItem>, skipFirst:Bool = false) {
		var lastIndex:Int = -1;
		for (child in children) {
			if (skipFirst) {
				skipFirst = false;
				continue;
			}
			switch (child.tok) {
				case PClose, BkClose, BrClose:
					return;
				case Binop(OpGt):
					return;
				case Sharp(_):
					if (!isInlineSharp(child)) {
						collectWrappableItemsFromSharp(child, items);
						continue;
					}
				// Inline Sharp — exit switch, process as single item below
				default:
			}
			if (child.index <= lastIndex) {
				continue;
			}
			var endToken:Null<TokenTree> = findItemEnd(child);
			if (endToken == null) {
				continue;
			}
			// Inside Sharp blocks, commas are siblings (not children of the expression).
			// Extend the item to include the trailing comma so wrapping keeps it attached.
			if (!endToken.tok.match(Comma)) {
				var nextInfo:Null<TokenInfo> = getNextToken(endToken);
				if (nextInfo != null && nextInfo.token.tok.match(Comma)) {
					endToken = nextInfo.token;
				}
			}
			lastIndex = endToken.index;

			var sameLine:Bool = isSameLineBetween(child, endToken, false);
			var firstLineLength:Int = calcLengthUntilNewline(child, endToken);

			if (isMultilineToken(endToken)) {
				sameLine = false;
			}
			var lastLineLength:Int = 0;
			if (!sameLine) {
				lastLineLength = calcLineLengthAfter(endToken);
			}
			items.push({
				first: child,
				last: endToken,
				multiline: !sameLine,
				firstLineLength: firstLineLength,
				lastLineLength: lastLineLength
			});
		}
	}

	function collectWrappableItemsFromSharp(sharp:TokenTree, items:Array<WrappableItem>) {
		if (sharp.children == null) return;
		switch (sharp.tok) {
			case Sharp(MarkLineEnds.SHARP_END):
				return;
			case Sharp(MarkLineEnds.SHARP_IF), Sharp(MarkLineEnds.SHARP_ELSE_IF):
				collectWrappableItems(sharp.children, items, true);
			case Sharp(MarkLineEnds.SHARP_ELSE):
				collectWrappableItems(sharp.children, items);
			default:
				collectWrappableItems(sharp.children, items);
		}
	}

	/** Check if a Sharp block has its content on the same line as the directive. */
	function isInlineSharp(sharp:TokenTree):Bool {
		if (sharp.children == null || sharp.children.length <= 0) return true;
		switch (sharp.tok) {
			case Sharp(MarkLineEnds.SHARP_IF), Sharp(MarkLineEnds.SHARP_ELSE_IF):
				if (sharp.children.length > 1) {
					return parsedCode.isOriginalSameLine(sharp, sharp.children[1]);
				}
				return true;
			case Sharp(MarkLineEnds.SHARP_ELSE):
				return parsedCode.isOriginalSameLine(sharp, sharp.children[0]);
			case Sharp(MarkLineEnds.SHARP_END):
				return true;
			default:
				return false;
		}
	}

	function findItemEnd(child:TokenTree):Null<TokenTree> {
		var endToken:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(child);
		if (endToken == null) {
			return null;
		}
		if (endToken.index == child.index) {
			switch (child.tok) {
				case Comment(_) | CommentLine(_):
					var next:Null<TokenTree> = child.nextSibling;
					if (next != null) {
						return findItemEnd(next);
					}
				default:
			}
		}
		switch (endToken.tok) {
			case Comma:
				var next:Null<TokenInfo> = getNextToken(endToken);
				if (next == null) {
					return endToken;
				}
				switch (next.token.tok) {
					case Comment(s), CommentLine(s):
						if (parsedCode.isOriginalSameLine(endToken, next.token)) {
							return next.token;
						}
					default:
				}
				return endToken;
			default:
		}
		var next:Null<TokenInfo> = getNextToken(endToken);
		if (next == null) {
			return endToken;
		}
		switch (next.token.tok) {
			case Binop(OpGt):
				if (next.token.access().parent().matches(Binop(OpLt)).exists()) {
					return endToken;
				}
				return findItemEnd(next.token);
			case Binop(_), Question, Unop(_):
				return findItemEnd(next.token);
			case CommentLine(_), Comment(_):
				return findItemEnd(next.token);
			default:
		}
		return endToken;
	}

	function determineWrapType2(rules:WrapRules, token:TokenTree, items:Array<WrappableItem>, ?pos:PosInfos):WrapRule {
		var itemCount:Int = items.length;
		#if debugWrapping
		logWrappingStart();
		log("itemCount", '$itemCount', pos);
		#end
		if (items.length <= 0) {
			#if debugWrapping
			log("rule", "default", pos);
			#end
			return {
				conditions: [],
				type: rules.defaultWrap,
				location: rules.defaultLocation,
				additionalIndent: rules.defaultAdditionalIndent
			};
		}
		var minItemLength:Int = 9999;
		var maxItemLength:Int = 0;
		var totalItemLength:Int = 0;
		var lineLength:Int = calcLineLength(token);
		var hasMultiLineItem:Bool = false;
		var hasMultiLineItem:Bool = false;
		var hasEqualItemLengths:Bool = true;
		var itemLength:Int = -1;
		var count:Int = 0;
		for (item in items) {
			count++;
			// Check line length at each item — a comment or forced break
			// can split the chain across lines, hiding long continuations.
			var itemLineLen:Int = calcLineLength(item.first);
			if (itemLineLen > lineLength) {
				lineLength = itemLineLen;
			}
			totalItemLength += item.firstLineLength + item.lastLineLength;
			if (item.multiline) {
				hasMultiLineItem = true;
			}
			var length:Int = Math.floor(Math.max(item.firstLineLength, item.lastLineLength));
			if (length < minItemLength) {
				minItemLength = length;
			}
			if (length > maxItemLength) {
				maxItemLength = length;
			}
			if (itemLength < 0) {
				itemLength = length;
				continue;
			}
			if (itemLength != length) {
				if (count == items.length && (length + 2) == itemLength) {
					// allow last item to be two characters short e.g. [1,2,3] turns into "1 ,", "2 ,", "3"
					continue;
				}
				hasEqualItemLengths = false;
			}
		}
		#if debugWrapping
		log("maxItemLength", '$minItemLength', pos);
		log("maxItemLength", '$maxItemLength', pos);
		log("totalItemLength", '$totalItemLength', pos);
		log("lineLength", '$lineLength', pos);
		log("hasMultiLineItem", '$hasMultiLineItem', pos);
		log("hasEqualItemLengths", '$hasEqualItemLengths', pos);
		#end
		for (rule in rules.rules) {
			if (matchesRule(rule, itemCount, minItemLength, maxItemLength, totalItemLength, lineLength, hasMultiLineItem, hasEqualItemLengths)) {
				return rule;
			}
		}
		#if debugWrapping
		log("rule", "default", pos);
		#end
		return {
			conditions: [],
			type: rules.defaultWrap,
			location: rules.defaultLocation,
			additionalIndent: rules.defaultAdditionalIndent
		};
	}

	function determineWrapType(rules:WrapRules, itemCount:Int, minItemLength:Int, maxItemLength:Int, totalItemLength:Int, lineLength:Int):WrapRule {
		for (rule in rules.rules) {
			if (matchesRule(rule, itemCount, minItemLength, maxItemLength, totalItemLength, lineLength, false, false)) {
				return rule;
			}
		}
		return {
			conditions: [],
			type: rules.defaultWrap,
			location: rules.defaultLocation,
			additionalIndent: rules.defaultAdditionalIndent
		};
	}

	function matchesRule(rule:WrapRule, itemCount:Int, minItemLength:Int, maxItemLength:Int, totalItemLength:Int, lineLength:Int, hasMultiLineItem:Bool,
			hasEqualItemLenghts:Bool):Bool {
		for (cond in rule.conditions) {
			switch (cond.cond) {
				case ItemCountLargerThan:
					if (itemCount < cond.value) {
						return false;
					}
				case ItemCountLessThan:
					if (itemCount > cond.value) {
						return false;
					}
				case AnyItemLengthLargerThan:
					if (maxItemLength < cond.value) {
						return false;
					}
				case AllItemLengthsLessThan:
					if (maxItemLength > cond.value) {
						return false;
					}
				case AllItemLengthsLargerThan:
					if (minItemLength < cond.value) {
						return false;
					}
				case AnyItemLengthLessThan:
					if (minItemLength > cond.value) {
						return false;
					}
				case TotalItemLengthLargerThan:
					if (totalItemLength < cond.value) {
						return false;
					}
				case TotalItemLengthLessThan:
					if (totalItemLength > cond.value) {
						return false;
					}
				case LineLengthLargerThan:
					if (lineLength < cond.value) {
						return false;
					}
				case LineLengthLessThan:
					if (lineLength > cond.value) {
						return false;
					}
				case HasMultiLineItems:
					if (cond.value == 1) {
						if (!hasMultiLineItem) {
							return false;
						}
					} else {
						if (hasMultiLineItem) {
							return false;
						}
					}
				case ExceedsMaxLineLength:
					if (cond.value == 1) {
						if (lineLength <= config.wrapping.maxLineLength) {
							return false;
						}
					} else {
						if (lineLength > config.wrapping.maxLineLength) {
							return false;
						}
					}
				case EqualItemLengths:
					if (cond.value == 1) {
						if (!hasEqualItemLenghts) {
							return false;
						}
					} else {
						if (hasEqualItemLenghts) {
							return false;
						}
					}
			}
		}
		return true;
	}

	function applyRule(origin:WrappingOrigin, rule:WrapRule, open:TokenTree, close:TokenTree, items:Array<WrappableItem>, addIndent:Int, useTrailing:Bool,
			?pos:PosInfos) {
		var location:WrappingLocation = AfterLast;
		if (rule.location != null) {
			location = rule.location;
		}
		#if debugWrapping
		log("origin", originToText(origin), pos);
		log("rule", '$rule', pos);
		if (open != null) {
			log("open", '`$open` (${open.pos.min})', pos);
		}
		if (close != null) {
			log("close", '`$close` (${close.pos.min})', pos);
		}
		for (item in items) {
			log("item", '$item', pos);
		}
		for (item in items) {
			logWrappableItem(item);
		}
		#end
		switch (rule.type) {
			case OnePerLine:
				wrapChildOneLineEach2(open, close, items, addIndent, location);
			case OnePerLineAfterFirst:
				wrapChildOneLineEach2(open, close, items, addIndent, location, true);
			case Keep:
				keep2(open, close, items, addIndent, location);
			case EqualNumber:
			case FillLine:
				switch (location) {
					case AfterLast:
						wrapFillLine2AfterLast(open, close, items, config.wrapping.maxLineLength, addIndent, useTrailing);
					case BeforeLast:
						wrapFillLine2BeforeLast(open, close, items, config.wrapping.maxLineLength, addIndent, useTrailing);
				}
			case FillLineWithLeadingBreak:
				switch (location) {
					case AfterLast:
						wrapFillLineWithLeading2AfterLast(open, close, items, config.wrapping.maxLineLength, addIndent);
					case BeforeLast:
						wrapFillLine2BeforeLast(open, close, items, config.wrapping.maxLineLength, addIndent, useTrailing);
				}
			case NoWrap:
				switch (origin) {
					case OpBoolChainWrapping, OpAddChainWrapping, MethodChainWrapping, MultiVarWrapping, CasePatternWrapping:
						// Chain NoWrap: don't touch anything — other wrappings (callParameter)
						// may have set soft wraps that need to be preserved.
					case CallParameterWrapping:
						noWrappingBetween(open, close, false);
					case _:
						noWrappingBetween(open, close, false);
				}
		}
	}

	/** Check if there are Dot tokens preceded by PClose between open and close — method chain pattern. */
	function hasMethodChainDots(open:TokenTree, close:TokenTree):Bool {
		var idx:Int = open.index + 1;
		var depth:Int = 0;
		while (idx < close.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case POpen, BkOpen, BrOpen:
					depth++;
				case PClose, BkClose, BrClose:
					depth--;
				case Dot:
					if (depth == 0) {
						var prev:Null<TokenInfo> = parsedCode.tokenList.tokens[idx - 2];
						if (prev != null && prev.token.tok.match(PClose)) return true;
					}
				default:
			}
		}
		return false;
	}

	function clearSoftWraps(open:TokenTree, close:TokenTree) {
		if (open == null || close == null) return;
		var idx:Int = open.index;
		while (idx < close.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			info.wrapAfter = false;
		}
	}

	public function applyWrappingQueue() {
		var applied:Array<Bool> = [for (_ in wrappingQueue) false];
		for (i in 0...wrappingQueue.length) {
			if (applied[i]) {
				continue;
			}
			var place:WrappingPlace = wrappingQueue[i];
			// Before applying opBool chain, apply inner callParameter wrapping that contains
			// the last opBool item — this callParameter break shortens the effective line length
			// and may prevent unnecessary opBool wrapping.
			if (place.origin == OpBoolChainWrapping && place.items != null && place.items.length > 0) {
				var lastItem:WrappableItem = place.items[place.items.length - 1];
				var lastItemEnd:Null<TokenTree> = lastItem.last;
				if (lastItemEnd != null) {
					for (j in (i + 1)...wrappingQueue.length) {
						if (applied[j]) {
							continue;
						}
						var inner:WrappingPlace = wrappingQueue[j];
						if (inner.origin == CallParameterWrapping && inner.start != null) {
							if (inner.start.index >= lastItem.first.index && inner.start.index <= lastItemEnd.index) {
								applyWrappingPlace(inner);
								applied[j] = true;
							}
						}
					}
				}
			}
			applyWrappingPlace(place);
			applied[i] = true;
		}
	}

	public function applyWrappingPlace(place:WrappingPlace) {
		// Skip OpSub-only chains inside call parameters when callParameter already wrapped
		// (any wrapping style — fillLine, fillLineWithLeadingBreak, etc.).
		// If callParameter didn't wrap (single param noWrap), let opSub chain handle it.
		// OpAdd chains (string concat) are always kept as valid split points.
		switch (place.origin) {
			case OpAddChainWrapping:
				if (place.start != null && place.start.tok.match(POpen)) {
					var pType:Null<POpenType> = TokenTreeCheckUtils.getPOpenType(place.start);
					if (pType == Call) {
						var hasAdd:Bool = false;
						for (item in place.items) {
							if (item.last.tok.match(Binop(OpAdd))) {
								hasAdd = true;
								break;
							}
						}
						if (!hasAdd) {
							var pClose:Null<TokenTree> = getCloseToken(place.start);
							if (pClose != null) {
								// Check if callParameter placed any breaks inside
								var hasBreak:Bool = false;
								var idx:Int = place.start.index;
								while (idx < pClose.index) {
									var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
									idx++;
									if (info != null && info.whitespaceAfter == Newline) {
										hasBreak = true;
										break;
									}
								}
								if (hasBreak) return;
								// No breaks but line exceeds: wrap as fillLineWithLeadingBreak
								if (calcLineLength(place.start) > config.wrapping.maxLineLength) {
									lineEndAfter(place.start);
									lineEndBefore(pClose);
									return;
								}
							}
						}
					}
				}
			case _:
		}
		var rule:WrapRule = determineWrapType2(place.rules, place.start, place.items);
		var additionalIndent:Int = rule.additionalIndent;
		if (place.overrideAdditionalIndent != null) {
			additionalIndent = place.overrideAdditionalIndent;
		}
		// Save POpen leading break — chain wrappings (opAdd/opBool) call noLineEndAfter
		// which removes callParameter's break. Find the POpen: it's place.start for opAdd
		// chains, or the next token for opBool chains (whose start is the CIdent before POpen).
		var savedPOpen:Null<TokenTree> = null;
		if (place.origin != CallParameterWrapping && place.start != null) {
			if (place.start.tok.match(POpen) && isNewLineAfter(place.start)) {
				savedPOpen = place.start;
			} else {
				var nxt:TokenInfo = getNextToken(place.start);
				if (nxt != null && nxt.token.tok.match(POpen) && isNewLineAfter(nxt.token)) savedPOpen = nxt.token;
			}
		}
		// OpAdd chain inside a call with a leading break: no extra indent —
		// continuation `+ 'text'` aligns with the first content line.
		applyRule(place.origin, rule, place.start, place.end, place.items, additionalIndent, place.useTrailing);
		// Restore POpen leading break if removed
		if (savedPOpen != null) {
			if (!isNewLineAfter(savedPOpen)) {
				lineEndAfter(savedPOpen);
			}
		}
		// After fillLineWithLeadingBreak, immediately move PClose to its own line
		// so inner items see correct line length (without trailing close parens).
		if (rule.type == FillLineWithLeadingBreak && place.end != null && isNewLineAfter(place.start)) {
			lineEndBefore(place.end);
		}
	}

	function queueWrapping(place:WrappingPlace, name:String) {
		if ((place.items == null) || (place.items.length <= 0)) {
			return;
		}
		var startIndex:Int = getPlaceStartIndex(place);
		var endIndex:Int = getPlaceEndIndex(place);
		if ((startIndex < 0) || (endIndex < 0)) {
			return;
		}
		var index:Int = 0;
		for (index in 0...wrappingQueue.length) {
			var p:WrappingPlace = wrappingQueue[index];
			var itemStart:Int = getPlaceStartIndex(p);
			if (startIndex > itemStart) {
				continue;
			}
			if (startIndex == itemStart) {
				var itemEnd:Int = getPlaceEndIndex(p);
				if (endIndex > itemEnd) {
					wrappingQueue.insert(index, place);
					return;
				}
				continue;
			}
			wrappingQueue.insert(index, place);
			return;
		}
		wrappingQueue.push(place);
	}

	function getPlaceStartIndex(place:WrappingPlace):Int {
		if ((place.items == null) || (place.items.length <= 0)) {
			return -1;
		}
		if (place.start != null) {
			return place.start.index;
		} else {
			return place.items[0].first.index;
		}
	}

	function getPlaceEndIndex(place:WrappingPlace):Int {
		if ((place.items == null) || (place.items.length <= 0)) {
			return -1;
		}
		if (place.end != null) {
			return place.end.index;
		} else {
			return place.items[place.items.length - 1].last.index;
		}
	}

	#if debugWrapping
	function logWrappingStart() {
		#if !js
		var file:FileOutput = File.append("hxformat.log", false);
		file.writeString("\n".lpad("-", 202));
		file.close();
		#end
	}

	function log(what:String, value:String, ?pos:PosInfos) {
		#if !js
		var func:String = '${pos.fileName}:${pos.lineNumber}:${pos.methodName}';
		var text:String = '${func.rpad(" ", 90)} ${what.rpad(" ", 20)} ${value.rpad(" ", 90)}';
		var file:FileOutput = File.append("hxformat.log", false);
		file.writeString(text + "\n");
		file.close();
		#end
	}

	function logWrappableItem(item:WrappableItem, ?pos:PosInfos) {
		if (item.last == null) {
			return;
		}
		var text:String = "";
		for (index in item.first.index...item.last.index + 1) {
			if (text != "") {
				text += " ";
			}
			text += '${parsedCode.tokens[index]}';
		}
		log("code", text, pos);
	}

	function originToText(origin:WrappingOrigin):String {
		return switch (origin) {
			case AnonTypeWrapping:
				"AnonTypeWrapping";
			case ArrayWrapping:
				"ArrayWrapping";
			case CallParameterWrapping:
				"CallParameterWrapping";
			case CasePatternWrapping:
				"CasePatternWrapping";
			case ConditionWrapping:
				"ConditionWrapping";
			case ExpressionWrapping:
				"ExpressionWrapping";
			case FunctionSignatureWrapping:
				"FunctionSignatureWrapping";
			case ImplementsWrapping:
				"ImplementsWrapping";
			case MapWrapping:
				"MapWrapping";
			case MetadataCallParameterWrapping:
				"MetadataCallParameterWrapping";
			case MethodChainWrapping:
				"MethodChainWrapping";
			case MultiVarWrapping:
				"MultiVarWrapping";
			case OpAddChainWrapping:
				"OpAddChainWrapping";
			case OpBoolChainWrapping:
				"OpBoolChainWrapping";
			case TernaryWrapping:
				"TernaryWrapping";
			case TypeParameterWrapping:
				"TypeParameterWrapping";
		}
	}
	#end
}

typedef WrappingPlace = {
	var origin:WrappingOrigin;
	var start:TokenTree;
	var end:Null<TokenTree>;
	var items:Array<WrappableItem>;
	var rules:WrapRules;
	var useTrailing:Bool;
	var overrideAdditionalIndent:Null<Int>;
}

enum WrappingOrigin {
	AnonTypeWrapping;
	ArrayWrapping;
	MapWrapping;
	CallParameterWrapping;
	CasePatternWrapping;
	ConditionWrapping;
	ExpressionWrapping;
	FunctionSignatureWrapping;
	ImplementsWrapping;
	MetadataCallParameterWrapping;
	MethodChainWrapping;
	MultiVarWrapping;
	OpAddChainWrapping;
	OpBoolChainWrapping;
	TernaryWrapping;
	TypeParameterWrapping;
}
