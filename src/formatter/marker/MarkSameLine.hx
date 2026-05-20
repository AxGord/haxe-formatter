package formatter.marker;

import formatter.config.SameLineConfig;

class MarkSameLine extends MarkerBase {
	final _forceFitLineNext:Array<TokenTree> = [];

	public function run() {
		markDollarSameLine();

		parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			if ((token.parent != null) && (token.parent.tok.match(At))) {
				return GoDeeper;
			}
			switch (token.tok) {
				case Kwd(KwdIf):
					markIf(token);
				case Kwd(KwdElse):
					markElse(token);
				case Kwd(KwdFor):
					markFor(token);
				case Kwd(KwdWhile):
					if ((token.parent != null) && (token.parent.tok.match(Kwd(KwdDo)))) {
						return GoDeeper;
					}
					markWhile(token);
				case Kwd(KwdDo):
					markDoWhile(token);
				case Kwd(KwdTry):
					markTry(token);
				case Kwd(KwdCatch):
					markCatch(token);
				case Kwd(KwdCase):
					markCase(token);
				case Kwd(KwdDefault):
					markCase(token);
				case Kwd(KwdFunction):
					markFunction(token);
				case Kwd(KwdMacro):
					markMacro(token);
				case Kwd(KwdReturn):
					markReturn(token);
				case Kwd(KwdUntyped):
					markUntyped(token);
				default:
			}
			return GoDeeper;
		});
	}

	function isExpression(token:Null<TokenTree>):Bool {
		if (token == null) {
			return false;
		}
		var parent:TokenTree = token.parent;
		switch (parent.tok) {
			case Kwd(KwdReturn):
				return true;
			case BkOpen:
				return true;
			case BrOpen:
				if (parent.parent.tok.match(Kwd(KwdFor))) {
					// Comprehension if with else and no {} body = expression-if (returns value)
					// Comprehension if without else = filter (use ifBody policy)
					// Comprehension if with {} body = regular if-else (not expression)
					if (token.tok.match(Kwd(KwdIf))) {
						var body:Null<TokenTree> = getBodyAfterCondition(token);
						if (body != null && body.tok.match(BrOpen)) return false;
						var hasElse:Bool = false;
						if (token.children != null) {
							for (child in token.children) {
								if (child.tok.match(Kwd(KwdElse))) {
									hasElse = true;
									break;
								}
							}
						}
						return hasElse;
					}
					return isExpression(parent);
				}
				var prev:Null<TokenTree> = token.previousSibling;
				if (prev != null && prev.tok.match(Binop(OpAssign))) {
					return true;
				}
			case Kwd(KwdMacro):
				return isExpression(parent);
			case Arrow:
				return true;
			case Kwd(KwdUntyped):
				return isExpression(parent);
			case Kwd(KwdFor), Kwd(KwdWhile):
				if (parent.parent.tok.match(BkOpen)) {
					return true;
				}
			case Binop(_):
				return true;
			case POpen:
				var pos:Position = parent.getPos();
				if ((pos.min < token.pos.min) && (pos.max > token.pos.max)) {
					return true;
				}
			case Kwd(KwdElse):
				return shouldElseBeSameLine(parent);
			case DblDot:
				var lastChild:Null<TokenTree> = parent.getLastChild();
				if (lastChild == null) {
					return false;
				}
				if (lastChild.index != token.index) {
					return false;
				}
				return isReturnExpression(parent);
			default:
		}

		return false;
	}

	function isReturnExpression(token:TokenTree):Bool {
		var parent:TokenTree = token;
		while (parent.parent.tok != Root) {
			parent = parent.parent;
			switch (parent.tok) {
				case Binop(_):
					return true;
				case Kwd(KwdReturn):
					return true;
				case Arrow:
					return true;
				case Kwd(KwdFunction):
					return false;
				case POpen:
					return true;
				case DblDot:
					return true;
				case BkOpen:
					return false;
				case BrOpen:
					var type:BrOpenType = TokenTreeCheckUtils.getBrOpenType(parent);
					switch (type) {
						case Block:
						case TypedefDecl:
						case ObjectDecl:
							return true;
						case AnonType:
						case Unknown:
					}
				default:
			}
		}
		return false;
	}

	function shouldIfBeSameLine(token:Null<TokenTree>):Bool {
		if (token == null) {
			return false;
		}
		if (!token.tok.match(Kwd(KwdIf))) {
			return false;
		}
		var body:Null<TokenTree> = getBodyAfterCondition(token);
		if (body == null) {
			return false;
		}

		return isExpression(token);
	}

	function shouldElseBeSameLine(token:Null<TokenTree>):Bool {
		if (token == null) {
			return false;
		}
		if (!token.tok.match(Kwd(KwdElse))) {
			return false;
		}

		return shouldIfBeSameLine(token.parent);
	}

	function shouldTryBeSameLine(token:Null<TokenTree>):Bool {
		if (token == null) {
			return false;
		}
		if (!token.tok.match(Kwd(KwdTry))) {
			return false;
		}
		return isExpression(token);
	}

	function shouldCatchBeSameLine(token:Null<TokenTree>):Bool {
		if (token == null) {
			return false;
		}
		if (!token.tok.match(Kwd(KwdCatch))) {
			return false;
		}
		var prev:TokenInfo = getPreviousToken(token);
		if (prev != null) {
			switch (prev.token.tok) {
				case BrClose:
					return false;
				default:
			}
		}
		return shouldTryBeSameLine(token.parent);
	}

	function markIf(token:TokenTree) {
		if (shouldIfBeSameLine(token)) {
			switch (config.sameLine.expressionIf) {
				case Same:
					markBodyAfterPOpen(token, Same, config.sameLine.expressionIfWithBlocks);
					return;
				case Keep:
					markBodyAfterPOpen(token, Keep, config.sameLine.expressionIfWithBlocks);
					return;
				case Next:
					// Arrow body if: use ifBody (fitLine) instead of expressionIf (next)
					if (token.parent != null && token.parent.tok.match(Arrow)) {
						markBodyAfterPOpen(token, resolveFitLine(token, config.sameLine.ifBody), false);
						return;
					}
					// Comprehension filter-if (no else): use ifBody, not expressionIf.
					// expressionIf: "next" should only apply to value-returning if/else expressions.
					if (isComprehensionFilterIf(token)) {
						markBodyAfterPOpen(token, resolveFitLine(token, config.sameLine.ifBody), false);
						return;
					}
					markBodyAfterPOpen(token, Next, config.sameLine.expressionIfWithBlocks);
					var prev:Null<TokenInfo> = getPreviousToken(token);
					if ((prev != null) && (prev.token.tok.match(Kwd(KwdElse)))) {
						applySameLinePolicy(token, config.sameLine.elseIf);
						wrapBefore(token, false);
					}
					return;
				case FitLine:
			}
		}
		markBodyAfterPOpen(token, resolveFitLine(token, config.sameLine.ifBody), false);
		var prev:Null<TokenInfo> = getPreviousToken(token);
		if ((prev != null) && (prev.token.tok.match(Kwd(KwdElse)))) {
			applySameLinePolicy(token, config.sameLine.elseIf);
		}
	}

	function markElse(token:TokenTree) {
		if (shouldElseBeSameLine(token)) {
			switch (config.sameLine.expressionIf) {
				case Same:
					markBody(token, Same, config.sameLine.expressionIfWithBlocks);
					var prev:Null<TokenInfo> = getPreviousToken(token);
					if (prev == null) {
						return;
					}
					if (prev.token.tok.match(BrClose) && TokenTreeCheckUtils.getBrOpenType(prev.token.parent) != ObjectDecl) {
						applySameLinePolicyChained(token, config.sameLine.ifBody, config.sameLine.ifElse);
					}
					return;
				case Keep:
					markBody(token, Keep, config.sameLine.expressionIfWithBlocks);
					if (parsedCode.isOriginalNewlineBefore(token)) {
						lineEndBefore(token);
					}
					var prev:Null<TokenInfo> = getPreviousToken(token);
					if (prev == null) {
						return;
					}
					if (prev.token.tok.match(BrClose) && TokenTreeCheckUtils.getBrOpenType(prev.token.parent) != ObjectDecl) {
						applySameLinePolicyChained(token, Keep, Keep);
					}
					return;
				case Next:
					var body:Null<TokenTree> = token.access().firstChild().token;
					if (body == null || !body.tok.match(Kwd(KwdIf))) {
						markBody(token, Next, config.sameLine.expressionIfWithBlocks);
					}
					lineEndBefore(token);
					var prev:Null<TokenInfo> = getPreviousToken(token);
					if (prev != null && prev.token.tok.match(BrClose) && TokenTreeCheckUtils.getBrOpenType(prev.token.parent) != ObjectDecl) {
						applySameLinePolicyChained(token, config.sameLine.ifBody, config.sameLine.ifElse);
					}
					return;
				case FitLine:
			}
		}

		markBody(token, resolveFitLine(token, config.sameLine.elseBody), false);
		var policy:SameLinePolicy = config.sameLine.ifElse;
		var prev:Null<TokenInfo> = getPreviousToken(token);
		if (prev != null) {
			switch (prev.token.tok) {
				case BrClose:
					if (!prev.token.access().parent().matches(BrOpen).parent().matches(Kwd(KwdIf)).exists()) {
						switch (policy) {
							case Same | FitLine:
								policy = Next;
							case Next:
							case Keep:
						}
					}
				case Semicolon:
					if (config.sameLine.ifElseSemicolonNextLine) {
						switch (policy) {
							case Same | FitLine:
								policy = Next;
							case Next:
							case Keep:
						}
					}
				default:
			}
		}
		applySameLinePolicyChained(token, config.sameLine.ifBody, policy);
	}

	function markTry(token:TokenTree) {
		if (shouldTryBeSameLine(token) && config.sameLine.expressionTry == Same) {
			markBody(token, Same, false);
			return;
		}
		markBody(token, resolveFitLine(token, config.sameLine.tryBody), false);
	}

	function markCatch(token:TokenTree) {
		if (shouldCatchBeSameLine(token) && config.sameLine.expressionTry == Same) {
			markBodyAfterPOpen(token, Same, false);
			applySameLinePolicy(token, config.sameLine.expressionTry);
			return;
		}
		markBodyAfterPOpen(token, resolveFitLine(token, config.sameLine.catchBody), false);
		applySameLinePolicyChained(token, config.sameLine.tryBody, config.sameLine.tryCatch);
	}

	function markCase(token:TokenTree) {
		if (token == null) {
			return;
		}
		var dblDot:TokenTree = token.access().firstOf(DblDot).token;
		if (dblDot == null) {
			return;
		}
		if (isReturnExpression(token)) {
			markExpressionCase(token, dblDot);
			return;
		}

		if ((dblDot.children == null) || (dblDot.children.length > 1)) {
			return;
		}
		switch (config.sameLine.caseBody) {
			case Same | FitLine:
			case Keep:
				if (!parsedCode.isOriginalSameLine(dblDot, dblDot.getFirstChild())) {
					return;
				}
			case Next:
				return;
		}
		var first:Null<TokenTree> = dblDot.getFirstChild();
		var last:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(first);
		if (parsedCode.linesBetweenOriginal(first, last) > 2) {
			return;
		}
		noLineEndAfter(dblDot);
	}

	function markExpressionCase(token:TokenTree, dblDot:TokenTree) {
		if (dblDot.children == null) {
			return;
		}

		switch (config.sameLine.expressionCase) {
			case Same | FitLine:
			case Keep:
				if (!parsedCode.isOriginalSameLine(dblDot, dblDot.getFirstChild())) {
					return;
				}
			case Next:
				return;
		}
		if (dblDot.children.length == 2) {
			var second:Null<TokenTree> = dblDot.children[1];
			switch (second.tok) {
				case CommentLine(_):
					var prev:Null<TokenInfo> = getPreviousToken(second);
					if (prev != null) {
						if (!parsedCode.isOriginalSameLine(dblDot, prev.token)) {
							return;
						}
					}
				default:
					return;
			}
		}
		if (dblDot.children.length > 2) {
			return;
		}
		noLineEndAfter(dblDot);
	}

	function isArrayComprehension(token:TokenTree):Bool {
		if (token == null) {
			return false;
		}
		var parent:Null<TokenTree> = token.parent;
		while (parent != null) {
			switch (parent.tok) {
				case Kwd(KwdFor), Kwd(KwdWhile), Kwd(KwdIf), Kwd(KwdElse):
					parent = parent.parent;
				case BkOpen:
					return true;
				default:
					return false;
			}
		}
		return false;
	}

	/** Check if token is a comprehension filter-if (inside for, no else). */
	function isComprehensionFilterIf(token:TokenTree):Bool {
		if (!token.tok.match(Kwd(KwdIf))) return false;
		var parent:Null<TokenTree> = token.parent;
		if (parent == null) return false;
		// Parent can be KwdFor directly or BrOpen with KwdFor grandparent
		var isInFor:Bool = switch (parent.tok) {
			case Kwd(KwdFor):
				parent.parent != null && parent.parent.tok.match(BkOpen);
			case BrOpen:
				parent.parent != null && parent.parent.tok.match(Kwd(KwdFor));
			case _: false;
		};
		if (!isInFor) return false;
		// Filter-if has no else
		if (token.children != null) {
			for (child in token.children) {
				if (child.tok.match(Kwd(KwdElse))) return false;
			}
		}
		return true;
	}

	function markFor(token:TokenTree) {
		if (token == null) {
			return;
		}
		var parent:Null<TokenTree> = token.parent;
		if ((parent == null) || (parent.tok == Root)) {
			return;
		}
		if (isArrayComprehension(token)) {
			markArrayComprehension(token, parent);
			return;
		}
		switch (parent.tok) {
			case Kwd(KwdMacro):
				var lastToken:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(token);
				if (lastToken == null) {
					return;
				}
				if (parsedCode.isOriginalSameLine(token, lastToken)) {
					markBodyAfterPOpen(token, Same, false);
					return;
				}
			default:
		}
		markBodyAfterPOpen(token, resolveFitLine(token, config.sameLine.forBody), false);
	}

	function markWhile(token:TokenTree) {
		if (token == null) {
			return;
		}
		var parent:Null<TokenTree> = token.parent;
		if ((parent == null) || (parent.tok == Root)) {
			return;
		}
		if (isArrayComprehension(token)) {
			markArrayComprehension(token, parent);
			return;
		}
		markBodyAfterPOpen(token, resolveFitLine(token, config.sameLine.whileBody), false);
	}

	function markArrayComprehension(token:TokenTree, bkOpen:TokenTree) {
		var bkClose:Null<TokenTree> = getCloseToken(bkOpen);
		switch (config.sameLine.comprehensionFor) {
			case Keep:
				if (parsedCode.isOriginalNewlineBefore(token)) {
					lineEndBefore(token);
				}
				markBodyAfterPOpen(token, config.sameLine.comprehensionFor, false);
				if ((bkClose != null) && (parsedCode.isOriginalNewlineBefore(bkClose))) {
					lineEndBefore(bkClose);
				}
			case Same:
				var origSame:Bool = false;
				if (bkClose != null) {
					origSame = parsedCode.isOriginalSameLine(bkOpen, bkClose);
				} else {
					var lastToken:TokenTree = TokenTreeCheckUtils.getLastToken(bkOpen);
					if (lastToken != null) {
						origSame = parsedCode.isOriginalSameLine(bkOpen, lastToken);
					}
				}
				if (origSame) {
					markBodyAfterPOpen(token, config.sameLine.comprehensionFor, false);
					if (bkClose != null) {
						if (!config.whitespace.bracketConfig.comprehensionBrackets.openingPolicy.has(After)) {
							whitespace(token, NoneBefore);
						}
						if (!config.whitespace.bracketConfig.comprehensionBrackets.closingPolicy.has(Before)) {
							whitespace(bkClose, NoneBefore);
						}
					}
				} else {
					var resolved:SameLinePolicy = resolveFitLine(token, config.sameLine.forBody);
					// When forBody is fitLine and the body is an ObjectDecl struct literal,
					// keep { on the for line even if the full struct doesn't fit —
					// struct fields wrap naturally inside the braces.
					if (resolved == Next && config.sameLine.forBody == FitLine) {
						var body:Null<TokenTree> = getBodyAfterCondition(token);
						if (body != null && body.tok.match(BrOpen) && TokenTreeCheckUtils.getBrOpenType(body) == ObjectDecl) {
							resolved = Same;
						}
					}
					// resolveFitLine Phase 1 measures only up to the body's `{`. For comprehension
					// we pass includeBrOpen=true (below) which asks markBlockBody to collapse the
					// whole block onto the for line — but block contents may exceed maxLineLength
					// even though the first line fits. Verify the full block fits before committing.
					if (resolved == Same && config.sameLine.forBody == FitLine) {
						var body:Null<TokenTree> = getBodyAfterCondition(token);
						if (body != null && body.tok.match(BrOpen) && TokenTreeCheckUtils.getBrOpenType(body) == Block) {
							var blockClose:Null<TokenTree> = getCloseToken(body);
							if (blockClose != null) {
								var indent:Int = indenter.calcIndent(token);
								var indentLen:Int = indenter.calcAbsoluteIndent(indent);
								var fullLen:Int = calcLengthBetween(token, blockClose) + calcTokenLength(blockClose);
								if ((indentLen + fullLen) > config.wrapping.maxLineLength) {
									resolved = Next;
								}
							}
						}
					}
					// In comprehension, for body is an implicit BrOpen(Block).
					// markBodyAfterPOpen with includeBrOpen=false skips it.
					// Pass true so markBlockBody can collapse the block onto one line.
					markBodyAfterPOpen(token, resolved, resolved == Same);
				}
			case FitLine:
				// FitLine: glue `[ for` and `]` to adjacent content (like Same+origSame), but
				// the body's collapse depends on whether the FULL `[for ... ]` fits one line.
				// If it does → collapse everything onto one line.
				// If not → keep `[ for` glued; `]` glued+symmetric only when body is a Block
				// (`{ ... } ]`); for non-block bodies (bare-if comprehension) `]` breaks to
				// its own line because the staircase has no closing brace to pair with.
				var fullFits:Bool = false;
				if (bkClose != null) {
					var bkIndent:Int = indenter.calcIndent(bkOpen);
					var bkIndentLen:Int = indenter.calcAbsoluteIndent(bkIndent);
					var fullLen:Int = calcLengthBetween(bkOpen, bkClose) + calcTokenLength(bkClose);
					fullFits = (bkIndentLen + fullLen) <= config.wrapping.maxLineLength;
				}
				var bodyIsBlock:Bool = false;
				{
					var body:Null<TokenTree> = getBodyAfterCondition(token);
					bodyIsBlock = body != null && body.tok.match(BrOpen) && TokenTreeCheckUtils.getBrOpenType(body) == Block;
				}
				if (fullFits) {
					markBodyAfterPOpen(token, Same, true);
				} else {
					var resolved:SameLinePolicy = resolveFitLine(token, config.sameLine.forBody);
					if (resolved == Next && config.sameLine.forBody == FitLine) {
						var body:Null<TokenTree> = getBodyAfterCondition(token);
						if (body != null && body.tok.match(BrOpen) && TokenTreeCheckUtils.getBrOpenType(body) == ObjectDecl) {
							resolved = Same;
						}
					}
					// Same full-block fit guard as the Same/!origSame branch above.
					if (resolved == Same && config.sameLine.forBody == FitLine) {
						var body:Null<TokenTree> = getBodyAfterCondition(token);
						if (body != null && body.tok.match(BrOpen) && TokenTreeCheckUtils.getBrOpenType(body) == Block) {
							var blockClose:Null<TokenTree> = getCloseToken(body);
							if (blockClose != null) {
								var indent:Int = indenter.calcIndent(token);
								var indentLen:Int = indenter.calcAbsoluteIndent(indent);
								var fullLen:Int = calcLengthBetween(token, blockClose) + calcTokenLength(blockClose);
								if ((indentLen + fullLen) > config.wrapping.maxLineLength) {
									resolved = Next;
								}
							}
						}
					}
					// Non-block body inside multi-line glued comprehension: force staircase.
					// Phase 2's "Same when `for (in) if (cond)` partial fits" makes sense for
					// chains in regular control-flow context, but here it joins `for` and `if`
					// on the line with `[`, undermining the `]`-on-its-own-line layout below.
					if (!bodyIsBlock) {
						resolved = Next;
					}
					markBodyAfterPOpen(token, resolved, resolved == Same);
				}
				if (bkClose != null) {
					// Uniform `[ for ... ]` spacing for the FitLine policy — both single-line and
					// multi-line glued forms get a space, so the array boundary stays visible in
					// dense expressions.
					if (!config.whitespace.bracketConfig.comprehensionBrackets.openingPolicy.has(After)) {
						whitespace(token, Before);
					}
					if (!config.whitespace.bracketConfig.comprehensionBrackets.closingPolicy.has(Before)) {
						if (!fullFits && !bodyIsBlock) {
							// Bare body (`[ for (...) if (cond) expr ]`) staircases to multiple
							// lines; `]` belongs on its own line, not glued to the last expr.
							lineEndBefore(bkClose);
						} else {
							whitespace(bkClose, Before);
						}
					}
				}
			case Next:
				// do nothing
		}
	}

	function getBodyAfterCondition(token:TokenTree):Null<TokenTree> {
		var pClose:Null<TokenTree> = token.access().firstOf(POpen).firstOf(PClose).token;
		if (pClose != null) {
			var next:TokenInfo = getNextToken(pClose);
			if (next != null) {
				switch (next.token.tok) {
					case DblDot:
					default:
						return next.token;
				}
			}
		}
		if (token.children == null) {
			return null;
		}
		for (child in token.children) {
			switch (child.tok) {
				case BrOpen:
					return child;
				case At:
				case Const(CIdent(_)):
					return child.nextSibling;
				case Kwd(KwdTrue), Kwd(KwdFalse), Kwd(KwdNull):
					return child.nextSibling;
				default:
			}
		}
		return null;
	}

	function markBodyAfterPOpen(token:TokenTree, policy:SameLinePolicy, includeBrOpen:Bool) {
		var body:Null<TokenTree> = getBodyAfterCondition(token);
		while (body != null) {
			switch (body.tok) {
				case BrOpen:
					var type:BrOpenType = TokenTreeCheckUtils.getBrOpenType(body);
					switch (type) {
						case Block:
							if (includeBrOpen) {
								markBlockBody(body, policy);
							}
							return;
						case TypedefDecl:
						case ObjectDecl:
							applySameLinePolicy(body, policy);
						case AnonType:
						case Unknown:
					}
					body = body.nextSibling;
				case Sharp(MarkLineEnds.SHARP_ELSE_IF), Sharp(MarkLineEnds.SHARP_ELSE), Sharp(MarkLineEnds.SHARP_END):
					return;
				case CommentLine(_):
					var prev:Null<TokenInfo> = getPreviousToken(body);
					if (prev != null) {
						if (!parsedCode.isOriginalSameLine(body, prev.token)) {
							applySameLinePolicy(body, policy);
							return;
						}
					}
					body = body.nextSibling;
				default:
					break;
			}
		}
		if (body == null) {
			return;
		}

		applySameLinePolicy(body, policy);
	}

	function markBody(token:TokenTree, policy:SameLinePolicy, includeBrOpen:Bool) {
		var body:Null<TokenTree> = token.access().firstChild().token;
		if (body == null) {
			return;
		}
		if (body.tok.match(BrOpen)) {
			var type:BrOpenType = TokenTreeCheckUtils.getBrOpenType(body);
			switch (type) {
				case Block:
					if (includeBrOpen) {
						markBlockBody(body, policy);
					}
					return;
				case TypedefDecl:
				case ObjectDecl:
					applySameLinePolicy(body, policy);
				case AnonType:
				case Unknown:
			}
			return;
		}
		applySameLinePolicy(body, policy);
	}

	function markBlockBody(token:TokenTree, policy:SameLinePolicy) {
		if (token == null) {
			return;
		}
		if (!token.tok.match(BrOpen)) {
			return;
		}
		if (token.children == null) {
			return;
		}

		var lastChild:Null<TokenTree> = token.getLastChild();
		if (lastChild.tok.match(Semicolon)) {
			if (token.children.length > 3) {
				return;
			}
		} else {
			if (token.children.length > 2) {
				return;
			}
		}
		noLineEndAfter(token);
		for (child in token.children) {
			switch (child.tok) {
				case BrClose:
					var next:Null<TokenInfo> = getNextToken(child);
					switch (next.token.tok) {
						case Kwd(KwdElse):
							noLineEndAfter(child);
						case Kwd(KwdCatch):
							noLineEndAfter(child);
						case Semicolon:
							whitespace(child, NoneAfter);
						case Comma:
							whitespace(child, NoneAfter);
						default:
					}
					return;
				default:
					var lastToken:TokenTree = TokenTreeCheckUtils.getLastToken(child);
					if (lastToken == null) {
						return;
					}
					noLineEndAfter(lastToken);
			}
		}
	}

	function applySameLinePolicyChained(token:TokenTree, previousBlockPolicy:SameLinePolicy, policy:SameLinePolicy) {
		if (policy == Same) {
			var prev:Null<TokenInfo> = getPreviousToken(token);
			if (prev == null) {
				policy = Next;
			}
			if ((!prev.token.tok.match(BrClose)) && (previousBlockPolicy != Same)) {
				policy = Next;
			}
		}
		applySameLinePolicy(token, policy);
	}

	inline function isChainBodyKwd(body:Null<TokenTree>):Bool {
		if (body == null) {
			return false;
		}
		return switch (body.tok) {
			case Kwd(KwdFor) | Kwd(KwdIf) | Kwd(KwdWhile) | Kwd(KwdDo): true;
			case _: false;
		}
	}

	function resolveFitLine(keyword:TokenTree, policy:SameLinePolicy):SameLinePolicy {
		if (policy != FitLine) {
			return policy;
		}
		// Cascade propagation: an outer chain link already decided this keyword
		// must break its body too. Continue forcing Next down the chain while
		// the body is still a control-flow Kwd whose own body is also a Kwd
		// (deepest chain link stops the cascade so its non-Kwd body can stay inline).
		if (_forceFitLineNext.contains(keyword)) {
			var body:Null<TokenTree> = getBodyAfterCondition(keyword);
			if (isChainBodyKwd(body) && isChainBodyKwd(getBodyAfterCondition(body))) {
				_forceFitLineNext.push(body);
			}
			return Next;
		}
		// Skip fitLine for if/else constructs unless explicitly allowed
		if (!config.sameLine.fitLineIfWithElse && isPartOfIfElse(keyword)) {
			return Next;
		}
		var indent:Int = indenter.calcIndent(keyword);
		var indentLen:Int = indenter.calcAbsoluteIndent(indent);

		// Phase 1: check if the entire statement fits on one line
		var lastToken:Null<TokenTree> = findFirstLineLastToken(keyword);
		if (lastToken != null) {
			var contentLen:Int = calcLengthBetween(keyword, lastToken) + calcTokenLength(lastToken);
			if ((indentLen + contentLen) <= config.wrapping.maxLineLength) {
				return Same;
			}
		}

		// Phase 2: if body is a nested keyword (for/if/while), check if just this level fits
		// (up to the nested keyword's closing paren) — let the inner level decide for itself.
		// Exception for 3+ chain links: every inner level's Phase 1 then succeeds at its own
		// tree-based indent and no level breaks, leaving an un-broken chain that feeds
		// conditionWrapping a maxLen-exceeding line which wraps each condition paren
		// `(\n cond \n)`. Detect via `body.body` also being a Kwd chain link — cascade
		// to staircase by forcing Next down the chain.
		var body:Null<TokenTree> = getBodyAfterCondition(keyword);
		if (body != null) {
			switch (body.tok) {
				case Kwd(KwdFor), Kwd(KwdIf), Kwd(KwdWhile), Kwd(KwdDo):
					var pClose:Null<TokenTree> = body.access().firstOf(POpen).firstOf(PClose).token;
					if (pClose != null) {
						var partialLen:Int = calcLengthBetween(keyword, pClose) + calcTokenLength(pClose);
						if ((indentLen + partialLen) <= config.wrapping.maxLineLength) {
							if (isChainBodyKwd(getBodyAfterCondition(body))) {
								_forceFitLineNext.push(body);
								return Next;
							}
							return Same;
						}
					}
				default:
			}
		}

		// Phase 3: if full line exceeds only due to trailing comment AND body is
		// a call/expression (not simple return/throw), keep Same — callParameter wrapping handles it.
		if (lastToken != null && lastToken.tok.match(CommentLine(_)) && body != null) {
			var isSimpleBody:Bool = switch (body.tok) {
				case Kwd(KwdReturn), Kwd(KwdThrow), Kwd(KwdBreak), Kwd(KwdContinue): true;
				case _: false;
			};
			if (!isSimpleBody) {
				var codeLastToken:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(keyword);
				if (codeLastToken != null) {
					var codeLen:Int = calcLengthBetween(keyword, codeLastToken) + calcTokenLength(codeLastToken);
					if ((indentLen + codeLen) <= config.wrapping.maxLineLength) {
						return Same;
					}
				}
			}
		}

		return Next;
	}

	function isPartOfIfElse(keyword:TokenTree):Bool {
		if (keyword.tok.match(Kwd(KwdElse))) {
			return true;
		}
		if (!keyword.tok.match(Kwd(KwdIf))) {
			return false;
		}
		// "if" with "else"
		if (keyword.children != null) {
			for (child in keyword.children) {
				if (child.tok.match(Kwd(KwdElse))) {
					return true;
				}
			}
		}
		// "if" inside "else" (i.e. "else if" construct)
		return (keyword.parent != null) && keyword.parent.tok.match(Kwd(KwdElse));
	}

	/**
		Walk the token tree from `token` and find the last token that would be on the first line.
		Stops at BrOpen (block body) since the block content goes on subsequent lines.
	**/
	function findFirstLineLastToken(token:TokenTree):Null<TokenTree> {
		var last:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(token);
		if (last == null) {
			return null;
		}
		// Include trailing line comment on same line — fitLine should account for visual line length
		var next:Null<TokenInfo> = getNextToken(last);
		if (next != null && next.token.tok.match(CommentLine(_)) && parsedCode.isOriginalSameLine(last, next.token)) {
			last = next.token;
		}
		// Walk tokens from keyword forward; if we hit a BrOpen that is a block, the first line ends at '{'
		var current:Null<TokenTree> = token;
		while (current != null) {
			switch (current.tok) {
				case BrOpen:
					var type:BrOpenType = TokenTreeCheckUtils.getBrOpenType(current);
					switch (type) {
						case Block:
							return current;
						default:
					}
				default:
			}
			if (current == last) {
				break;
			}
			// Traverse: first child, then next sibling, then parent's next sibling
			if (current.children != null && current.children.length > 0) {
				current = current.children[0];
			} else if (current.nextSibling != null) {
				current = current.nextSibling;
			} else {
				// Walk up to find next sibling
				var parent:Null<TokenTree> = current.parent;
				current = null;
				while (parent != null && parent != token.parent) {
					if (parent.nextSibling != null) {
						current = parent.nextSibling;
						break;
					}
					parent = parent.parent;
				}
			}
		}
		return last;
	}

	function applySameLinePolicy(token:TokenTree, policy:SameLinePolicy) {
		switch (policy) {
			case FitLine:
				// FitLine should be resolved to Same/Next by resolveFitLine before reaching here.
				// If it does reach here (e.g. from fields that don't call resolveFitLine), do nothing.
				return;
			case Keep:
				if (parsedCode.isOriginalNewlineBefore(token)) {
					applySameLinePolicy(token, Next);
				} else {
					applySameLinePolicy(token, Same);
				}
			case Same:
				wrapBefore(token, true);
				var prev:Null<TokenInfo> = getPreviousToken(token);
				if (prev == null) {
					noLineEndBefore(token);
				} else {
					switch (token.tok) {
						case At:
							switch (prev.token.tok) {
								case POpen | Dot:
									whitespace(token, NoneBefore);
								case BrOpen | BrClose | Semicolon | DblDot | Sharp(_) | Kwd(_):
								case Binop(_):
									lineEndBefore(token);
								default:
									noLineEndBefore(token);
							}
						case _:
							switch (prev.token.tok) {
								case POpen | Dot:
									whitespace(token, NoneBefore);
								default:
									noLineEndBefore(token);
							}
					}
				}
				var lastToken:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(token);
				if (lastToken == null) {
					return;
				}
				var next:Null<TokenInfo> = getNextToken(lastToken);
				if (next == null) {
					return;
				}
				switch (next.token.tok) {
					case Kwd(KwdElse):
						noLineEndAfter(lastToken);
					default:
				}
				return;
			case Next:
				switch (token.tok) {
					case CommentLine(s):
						if (!parsedCode.isOriginalNewlineBefore(token)) {
							return;
						}
					case BkOpen:
						if (token.access().parent().matches(Kwd(KwdFor)).exists()) {
							return;
						}
					default:
				}
				var prev:Null<TokenInfo> = getPreviousToken(token);
				if ((prev == null) || (!TokenTreeCheckUtils.isMetadata(prev.token))) {
					lineEndBefore(token);
					return;
				}
				var lowestToken:TokenTree = parsedCode.tokenList.findLowestIndex(token);
				lineEndBefore(lowestToken);
		}
	}

	function markDollarSameLine() {
		var tokens:Array<TokenTree> = parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			return switch (token.tok) {
				case Dollar("") | Dollar("a") | Dollar("b") | Dollar("e") | Dollar("i") | Dollar("p") | Dollar("v"):
					FoundSkipSubtree;
				case Dollar(_):
					SkipSubtree;
				default:
					GoDeeper;
			}
		});
		for (token in tokens) {
			var brOpen:Null<TokenTree> = token.access().firstChild().matches(BrOpen).token;
			if (brOpen == null) {
				continue;
			}
			var brClose:TokenTree = getCloseToken(brOpen);
			if (!parsedCode.isOriginalSameLine(brOpen, brClose)) {
				continue;
			}
			whitespace(brOpen, None);
			var next:Null<TokenInfo> = getNextToken(brClose);
			if (next != null) {
				switch (next.token.tok) {
					case BrClose | POpen | PClose | BkOpen | BkClose | DblDot:
					case Comma | Semicolon | Dot:
						whitespace(brClose, None);
					default:
						whitespace(brClose, OnlyAfter);
				}
			} else {
				noLineEndAfter(brClose);
			}
			wrapBefore(brOpen, false);
			wrapAfter(brOpen, false);
			wrapBefore(brClose, false);
			wrapAfter(brClose, false);
		}
	}

	function markFunction(token:TokenTree) {
		var body:Null<TokenTree> = token.access().firstChild().isCIdent().token;
		if (body == null) {
			body = token.access().firstChild().matches(Kwd(KwdNew)).token;
		}
		var policy:SameLinePolicy = config.sameLine.functionBody;
		if (body == null) {
			body = token;
			policy = config.sameLine.anonFunctionBody;
		}
		if ((body == null) || (body.children == null)) {
			return;
		}
		body = body.access().firstOf(POpen).token;
		if (body == null) {
			return;
		}
		if (body.nextSibling == null) {
			return;
		}
		body = body.nextSibling;
		switch (body.tok) {
			case DblDot:
				body = body.nextSibling;
			default:
		}
		if (body == null) {
			return;
		}
		switch (body.tok) {
			case BrOpen:
				return;
			case Sharp(MarkLineEnds.SHARP_IF):
				return;
			case Semicolon:
				return;
			case CommentLine(_):
				return;
			default:
		}
		applySameLinePolicy(body, resolveFitLine(token, policy));
	}

	function markDoWhile(token:TokenTree) {
		markBody(token, resolveFitLine(token, config.sameLine.doWhileBody), false);
		var whileTok:Null<TokenTree> = token.access().firstOf(Kwd(KwdWhile)).token;
		if (whileTok == null) {
			return;
		}
		applySameLinePolicy(whileTok, config.sameLine.doWhile);
	}

	function markMacro(token:TokenTree) {
		var brOpen:Null<TokenInfo> = getNextToken(token);
		if ((brOpen == null) || (!brOpen.token.tok.match(BrOpen))) {
			return;
		}
		var brClose:TokenTree = getCloseToken(brOpen.token);
		if (parsedCode.isOriginalSameLine(brOpen.token, brClose)) {
			noLineEndAfter(brOpen.token);
			noLineEndBefore(brClose);
			noWrappingBetween(brOpen.token, brClose);
		}
	}

	function markReturn(token:TokenTree) {
		if (isFunctionBody(token)) {
			return;
		}
		if (shouldReturnBeSameLine(token)) {
			markBody(token, config.sameLine.returnBodySingleLine, false);
		} else {
			markBody(token, config.sameLine.returnBody, false);
		}
	}

	function isFunctionBody(token:TokenTree):Bool {
		var parent = token.parent;
		if (parent == null) {
			return false;
		}
		if (parent.matches(BrOpen)) {
			return false;
		}
		parent = parent.parent;
		if (parent == null) {
			return false;
		}
		return parent.matches(Kwd(KwdFunction));
	}

	function markUntyped(token:TokenTree) {
		if (!token.access().firstChild().matches(BrOpen).exists()) {
			return;
		}
		var parent:Null<TokenTree> = token.parent;
		if ((parent == null) || (token.tok == Root)) {
			return;
		}
		switch (parent.tok) {
			case BrOpen:
				var type:BrOpenType = TokenTreeCheckUtils.getBrOpenType(parent);
				switch (type) {
					case Block:
						return;
					case TypedefDecl:
						return;
					case ObjectDecl:
					case AnonType:
					case Unknown:
				}
			default:
		}

		applySameLinePolicy(token, config.sameLine.untypedBody);
	}

	function shouldReturnBeSameLine(token:TokenTree):Bool {
		var lastToken:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(token);
		if (lastToken == null) {
			return true;
		}
		if (isSameLineBetween(token, lastToken, false)) {
			return true;
		}
		return shouldReturnChildsBeSameLine(token);
	}

	function shouldReturnChildsBeSameLine(token:TokenTree):Bool {
		if (token.children == null) {
			return true;
		}
		for (child in token.children) {
			switch (child.tok) {
				case Kwd(KwdIf), Kwd(KwdSwitch), Kwd(KwdWhile), Kwd(KwdFor), Kwd(KwdTry):
					return false;
				default:
					var result:Bool = shouldReturnChildsBeSameLine(child);
					if (!result) {
						return false;
					}
			}
		}
		return true;
	}
}
