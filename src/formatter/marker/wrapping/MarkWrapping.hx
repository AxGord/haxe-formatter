package formatter.marker.wrapping;

import formatter.config.WrapConfig;

class MarkWrapping extends MarkWrappingBase {
	var conditionWraps:Array<TokenTree> = [];
	var expressionWraps:Array<TokenTree> = [];
	var parenIndentWraps:Array<TokenTree> = [];
	var ternaryWraps:Array<{itemStart:TokenTree, question:TokenTree, dblDot:TokenTree}> = [];
	var arrowWraps:Array<TokenTree> = [];
	var sharpChainExtensions:Array<TokenTree> = [];
	var multiParamOpAddTokens:Array<TokenTree> = [];
	var assignmentWraps:Array<TokenTree> = [];
	var extendsWraps:Array<{first:TokenTree, end:TokenTree}> = [];

	public function run() {
		var wrappableTokens:Array<TokenTree> = parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case Dot:
					return FoundGoDeeper;
				case BrOpen:
					return FoundGoDeeper;
				case BkOpen:
					return FoundGoDeeper;
				case POpen:
					return FoundGoDeeper;
				case Binop(OpAdd):
					return FoundGoDeeper;
				case Binop(OpLt):
					return FoundGoDeeper;
				case Binop(OpArrow), Arrow:
					return FoundGoDeeper;
				case CommentLine(_):
					return FoundGoDeeper;
				case Comma:
					wrapAfter(token, true);
					return GoDeeper;
				default:
			}
			return GoDeeper;
		});

		wrappableTokens.reverse();
		for (token in wrappableTokens) {
			switch (token.tok) {
				case Dot:
				case BrOpen:
					markBrWrapping(token);
				case BkOpen:
					arrayWrapping(token);
				case POpen:
					markPWrapping(token);
				case Binop(OpAdd):
					wrapAfter(token, true);
				case Binop(OpLt):
					if (TokenTreeCheckUtils.isTypeParameter(token)) {
						wrapTypeParameter(token);
					}
				case Binop(OpArrow), Arrow:
					wrapAfter(token, true);
					if (calcLineLength(token) > config.wrapping.maxLineLength) {
						var arrowType:Null<ArrowType> = TokenTreeCheckUtils.getArrowType(token);
						if (arrowType != OldFunctionType) {
							arrowWraps.push(token);
						}
					}
				case CommentLine(_):
					wrapBefore(token, false);
				default:
			}
		}

		markMethodChaining(parsedCode.root);
		markMultiVarChaining();
		markImplementsExtendsChaining();
		markTernaryChaining();
		markOpBoolChaining();
		markOpAddChaining();
		markCasePatternChaining();
		markAssignmentChaining();

		applyWrappingQueue();
		reEvaluateSingleArgCallParam();
		reEvaluateOpBoolAfterCallParam();
		indentChainContinuationAfterSharpEnd();
		// Fix indent for chain items added by extendChainAcrossSharp:
		// these tokens are at a shallower tree depth than the chain's original items,
		// so they need extra indent to align with the chain.
		for (token in sharpChainExtensions) {
			additionalIndent(token, 1);
		}
		// Fix indent for opAdd continuations inside multi-param calls.
		// These chains are skipped by markSingleOpAddChain (hasCommasBetween),
		// so no wrapping sets additionalIndent. Add +1 on the first token of each
		// continuation line: either the + itself (beforeLast) or the next token (afterLast).
		// Set additionalIndent on all opAdd tokens and their successors in multi-param calls.
		// Only tokens that actually start new lines will use it (CodeLines checks on line start).
		// Skip indent for leading operators (wrapBefore) — the operator itself signals continuation.
		for (token in multiParamOpAddTokens) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[token.index];
			if (info != null && !info.wrapAfter) continue;
			additionalIndent(token, 1);
			var next:Null<TokenInfo> = getNextToken(token);
			if (next != null) {
				additionalIndent(next.token, 1);
			}
		}
		lateDetectTernaries();
		applyTernaryWrapping();
		applyArrowWrapping();
		applyConditionWrapping();
		applyExpressionWrapping();
		collapseChainWraps();
		applyAssignmentWrapping();
		applyExtendsWrapping();
		reEvaluateMethodChainAfterCallParam();
		breakLongMethodChains();
		preferParenWrapOverSingleArgChainBreak();
		preferTernaryWrapOverBranchChainBreak();
		preferFunctionSignatureWrapOverInnerParen();
		breakLongOpBoolOperandAtCompare();
		applyParenIndentWrapping();
		wrapLongCallParamsInChains();
		applyAssignmentTypeParamCollapse();
	}

	/**
	 * Post-queue: for single-arg calls where the arg is multiline (inner call wrapped),
	 *  remove the outer call's leading break if the opening line fits.
	 *  e.g. `dispatchEvent(new SomeEvent(\n\t...` should not become `dispatchEvent(\n\tnew SomeEvent(\n\t\t...`.
	 */
	function reEvaluateSingleArgCallParam() {
		for (place in wrappingQueue) {
			if (place.origin != CallParameterWrapping) continue;
			if (place.items == null || place.items.length < 1) continue;
			if (place.start == null) continue;
			var pClose:Null<TokenTree> = place.end;
			if (pClose == null) pClose = getCloseToken(place.start);
			if (pClose == null) continue;
			// Multi-arg calls: try collapsing if all items are on one wrapped line
			// and the collapsed call fits (e.g. after opAdd chain shortened the line).
			if (place.items.length > 1) {
				if (!isNewLineAfter(place.start)) continue;
				var hadPCloseBreak:Bool = isNewLineBefore(pClose);
				noLineEndAfter(place.start);
				if (hadPCloseBreak) noLineEndBefore(pClose);
				// Check no remaining breaks between POpen and PClose
				var hasRemainingBreaks:Bool = false;
				var ri:Int = place.start.index + 1;
				while (ri < pClose.index) {
					var rInfo:Null<TokenInfo> = parsedCode.tokenList.tokens[ri];
					ri++;
					if (rInfo != null && rInfo.whitespaceAfter == Newline) {
						hasRemainingBreaks = true;
						break;
					}
				}
				if (hasRemainingBreaks) {
					lineEndAfter(place.start);
					if (hadPCloseBreak) lineEndBefore(pClose);
					continue;
				}
				if (calcLineLength(place.start) <= config.wrapping.maxLineLength) {
					continue; // Fits on one line — keep collapsed
				}
				// Line exceeds after collapse — try adding an opAdd break after PClose.
				// Collect OpAdd/OpSub tokens, then try the rightmost break that makes
				// the start line fit (fillLine beforeLast semantics).
				var opTokens:Array<TokenTree> = [];
				var wi:Int = pClose.index + 1;
				while (wi < parsedCode.tokenList.tokens.length) {
					var wInfo:Null<TokenInfo> = parsedCode.tokenList.tokens[wi];
					wi++;
					if (wInfo == null) continue;
					if (wInfo.whitespaceAfter == Newline) break;
					switch wInfo.token.tok {
						case Binop(OpAdd), Binop(OpSub):
							opTokens.push(wInfo.token);
						case POpen, BrOpen, BkOpen:
							var close:Null<TokenTree> = getCloseToken(wInfo.token);
							if (close != null) wi = close.index + 1;
						case _:
					}
				}
				var addedBreak:Bool = false;
				var oi:Int = opTokens.length - 1;
				while (oi >= 0) {
					lineEndBefore(opTokens[oi]);
					if (calcLineLength(place.start) <= config.wrapping.maxLineLength) {
						addedBreak = true;
						break;
					}
					noLineEndBefore(opTokens[oi]);
					oi--;
				}
				if (addedBreak) continue;
				// Doesn't fit — restore call wrapping
				lineEndAfter(place.start);
				if (hadPCloseBreak) lineEndBefore(pClose);
				continue;
			}
			if (!isNewLineAfter(place.start)) {
				// No leading break — NoWrap collapsed this call.
				// If the content has top-level comment-forced breaks (CommentLine between
				// POpen and PClose outside nested blocks), add the leading break.
				// Comments force line breaks that noWrappingBetween preserves, creating a
				// multi-line expression that needs the POpen break for consistency.
				var hasTopLevelComment:Bool = false;
				var bi:Int = place.start.index + 1;
				while (bi < pClose.index) {
					final bInfo:Null<TokenInfo> = parsedCode.tokenList.tokens[bi];
					bi++;
					if (bInfo == null) continue;
					switch bInfo.token.tok {
						case POpen, BrOpen, BkOpen:
							// Skip nested blocks
							final close:Null<TokenTree> = getCloseToken(bInfo.token);
							if (close != null) bi = close.index + 1;
						case CommentLine(_):
							hasTopLevelComment = true;
							break;
						case _:
					}
				}
				if (hasTopLevelComment) {
					lineEndAfter(place.start);
					lineEndBefore(pClose);
				}
				continue;
			}
			// Has a leading break (fillLineWithLeadingBreak was applied) — try to collapse it
			// Skip if the wrapping rule is Keep — preserve original formatting
			var rule:WrapRule = determineWrapType2(place.rules, place.start, place.items);
			if (rule.type == Keep) continue;
			// Check if inner content is multiline (has breaks inside the single arg)
			var hasInnerBreak:Bool = false;
			var idx:Int = place.start.index + 1;
			while (idx < pClose.index) {
				var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
				idx++;
				if (info == null) continue;
				if (info.whitespaceAfter == Newline) {
					hasInnerBreak = true;
					break;
				}
			}
			if (!hasInnerBreak) continue;
			// Don't collapse if content has chain operators AND full span exceeds maxLineLength.
			// Nested calls (no chain ops) should still collapse.
			var hasChainOps:Bool = false;
			var spanLen:Int = 0;
			var si:Int = place.start.index + 1;
			while (si <= pClose.index) {
				var sInfo:Null<TokenInfo> = parsedCode.tokenList.tokens[si];
				si++;
				if (sInfo == null) continue;
				spanLen += sInfo.text.length;
				switch sInfo.whitespaceAfter {
					case None:
					case Space:
						spanLen += Math.floor(Math.max(1, sInfo.spacesAfter));
					case Newline:
						spanLen += 1;
				}
				switch sInfo.token.tok {
					case Binop(OpBoolAnd), Binop(OpBoolOr), Binop(OpAdd), Binop(OpSub):
						hasChainOps = true;
					case _:
				}
			}
			if (hasChainOps) {
				var lineStart:Null<TokenTree> = findLineStartToken(place.start);
				if (lineStart != null) {
					var fullLen:Int = indenter.calcAbsoluteIndent(indenter.calcIndent(lineStart))
						+ calcLineLengthBefore(place.start)
						+ calcTokenLength(place.start)
						+ spanLen;
					if (fullLen > config.wrapping.maxLineLength) continue;
				}
			}
			// Try removing outer leading break — check if opening line fits
			noLineEndAfter(place.start);
			noLineEndBefore(pClose);
			if (calcLineLength(place.start) <= config.wrapping.maxLineLength) {
				// After collapsing outer single-arg call, inner multi-arg fills
				// may have been calculated with a deeper indent (based on the
				// pre-collapse state). Re-evaluate them with the updated indent.
				reEvaluateInnerCallWrapping(place.start, pClose);
				continue; // fits — keep collapsed
			}
			// Call doesn't fit on one line. If there's a method chain after PClose,
			// prefer breaking at the chain over wrapping inside the call.
			var nextAfterClose:Null<TokenInfo> = getNextToken(pClose);
			if (nextAfterClose != null && nextAfterClose.token.tok.match(Dot)) {
				lineEndBefore(nextAfterClose.token);
				if (calcLineLength(place.start) <= config.wrapping.maxLineLength
					&& calcLineLength(nextAfterClose.token) <= config.wrapping.maxLineLength) {
					continue; // Method chain break is better
				}
				noLineEndBefore(nextAfterClose.token);
			}
			// Doesn't fit on one line — check if wrapping actually helps.
			// If the wrapped content line also exceeds maxLineLength
			// (e.g. single long string literal), wrapping is futile — keep unwrapped.
			lineEndAfter(place.start);
			lineEndBefore(pClose);
			var contentToken:Null<TokenTree> = place.items[0].first;
			if (contentToken != null && calcLineLength(contentToken) > config.wrapping.maxLineLength) {
				noLineEndAfter(place.start);
				noLineEndBefore(pClose);
			}
		}
	}

	/**
	 * After collapsing an outer single-arg call, re-evaluate inner multi-arg
	 * call fills whose indent was calculated based on the pre-collapse state.
	 */
	function reEvaluateInnerCallWrapping(outerStart:TokenTree, outerClose:TokenTree) {
		for (innerPlace in wrappingQueue) {
			if (innerPlace.origin != CallParameterWrapping) continue;
			if (innerPlace.items == null || innerPlace.items.length <= 1) continue;
			if (innerPlace.start == null) continue;
			if (innerPlace.start.index <= outerStart.index || innerPlace.start.index >= outerClose.index) continue;
			if (!isNewLineAfter(innerPlace.start)) continue;
			var innerPClose:Null<TokenTree> = innerPlace.end;
			if (innerPClose == null) innerPClose = getCloseToken(innerPlace.start);
			if (innerPClose == null) continue;
			// Undo existing fill breaks and re-apply with corrected indent
			noWrappingBetween(innerPlace.start, innerPClose, false);
			noLineEndBefore(innerPClose);
			applyWrappingPlace(innerPlace);
		}
	}

	/**
	 * Post-queue: when an opAdd chain inside a Block-level expression is split by
	 *  `#if/#end`, the parser puts post-#end siblings at the enclosing BrOpen level.
	 *  Those tokens get the block's natural indent, breaking visual alignment with
	 *  the chain continuation inside the conditional. Walk every Sharp(end) whose
	 *  parent is a Block BrOpen and push +1 additional indent on the next non-Sharp
	 *  sibling token, so it lines up with the chain's continuation indent.
	 */
	function indentChainContinuationAfterSharpEnd() {
		var sharpEnds:Array<TokenTree> = parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			return switch (token.tok) {
				case Sharp(MarkLineEnds.SHARP_END): FoundSkipSubtree;
				default: GoDeeper;
			}
		});
		for (sharpEnd in sharpEnds) {
			if (sharpEnd.parent == null || !sharpEnd.parent.tok.match(Sharp(MarkLineEnds.SHARP_IF))) continue;
			var sharpIf:TokenTree = sharpEnd.parent;
			// Only act when this Sharp pair is an operand inside an opAdd chain — that's
			// the case where the parser splits the chain into siblings at block level.
			// Statement-level conditionals (`#if cpp ... #end` wrapping whole statements)
			// have Sharp(if) as a direct child of the block and must be left untouched.
			if (sharpIf.parent == null) continue;
			switch (sharpIf.parent.tok) {
				case Binop(OpAdd), Binop(OpSub):
				default: continue;
			}
			// Walk up to the ancestor that sits directly inside a Block BrOpen — that's
			// the statement the Sharp lives in. The post-#end chain is kept as a sibling
			// of that statement at block level, so its first token needs the continuation
			// bump to align with the wrapped chain inside #if/#end.
			var anchor:TokenTree = sharpIf;
			while (anchor.parent != null && !anchor.parent.tok.match(BrOpen)) {
				anchor = anchor.parent;
			}
			if (anchor.parent == null) continue;
			if (TokenTreeCheckUtils.getBrOpenType(anchor.parent) != Block) continue;
			var next:Null<TokenTree> = anchor.nextSibling;
			while (next != null) {
				switch (next.tok) {
					case Sharp(_), Comma, Semicolon, BrClose:
						next = next.nextSibling;
					default:
						break;
				}
			}
			if (next == null) continue;
			additionalIndent(next, 1);
		}
	}

	/**
	 * Post-queue: re-evaluate opBoolChain entries that decided NoWrap because
	 *  inner callParameter was applied first (shortening the line).
	 *  Strips callParameter breaks, re-applies opBoolChain with true line length.
	 */
	function reEvaluateOpBoolAfterCallParam() {
		for (place in wrappingQueue) {
			if (place.origin != OpBoolChainWrapping) continue;
			if (place.start == null || place.items == null) continue;
			var startIdx:Int = getPlaceStartIndex(place);
			var endIdx:Int = getPlaceEndIndex(place);
			// Skip if opBoolChain already has breaks (it wrapped successfully)
			if (hasChainBreaksBetween(startIdx, endIdx)) continue;
			// Skip if no inner callParameter breaks exist
			if (!hasSimpleCallParamBreaksBetween(startIdx, endIdx)) continue;
			// Strip inner breaks, re-apply opBoolChain
			var idx:Int = startIdx;
			while (idx <= endIdx) {
				var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
				idx++;
				if (info == null) continue;
				if (isNewLineAfter(info.token)) {
					noLineEndAfter(info.token);
				}
			}
			applyWrappingPlace(place);
		}
	}

	/** Whether the opBool chain between the indices is wrapped (operands on
	 *  separate lines). A break may be a hard Newline or a soft `wrapAfter`
	 *  (resolved at emit), and with per-operand trailing comments it sits on
	 *  the `CommentLine` after the operator (`) || // cmt\n`), not on the
	 *  operator itself — all of these count. */
	function hasChainBreaksBetween(startIdx:Int, endIdx:Int):Bool {
		var idx:Int = startIdx;
		while (idx <= endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Binop(OpBoolAnd), Binop(OpBoolOr):
					if (isNewLineBefore(info.token) || isNewLineAfter(info.token) || info.wrapAfter) return true;
					var prev:Null<TokenInfo> = getPreviousToken(info.token);
					if (prev != null && (prev.wrapAfter || isNewLineAfter(prev.token))) return true;
					var next:Null<TokenInfo> = getNextToken(info.token);
					if (next != null && (next.token.tok.match(CommentLine(_)) || next.token.tok.match(Comment(_)))
						&& (next.wrapAfter || next.whitespaceAfter == Newline)) return true;
				default:
			}
		}
		return false;
	}

	/** Check if there are simple callParameter breaks (no arrow/lambda inside)
	 *  that are INNER to the opBoolChain (not enclosing it). */
	function hasSimpleCallParamBreaksBetween(startIdx:Int, endIdx:Int):Bool {
		var idx:Int = startIdx;
		while (idx <= endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			if (info.token.tok.match(POpen) && isNewLineAfter(info.token)) {
				// Skip if call contains arrow function — complex body needs its own wrapping
				var pClose:Null<TokenTree> = getCloseToken(info.token);
				if (pClose != null && hasArrowBetween(info.token.index, pClose.index)) continue;
				// Skip if call ENCLOSES the entire opBoolChain — the call is outer,
				// opBoolChain is inner. Don't strip outer callParameter breaks.
				if (pClose != null && info.token.index <= startIdx && pClose.index >= endIdx) continue;
				return true;
			}
		}
		return false;
	}

	function hasArrowBetween(startIdx:Int, endIdx:Int):Bool {
		var idx:Int = startIdx;
		while (idx <= endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Binop(OpArrow), Arrow:
					return true;
				default:
			}
		}
		return false;
	}

	function hasCallParamBreaksBetweenTokens(start:TokenTree, end:TokenTree):Bool {
		return hasSimpleCallParamBreaksBetween(start.index, end.index);
	}

	function wrapTypeParameter(token:TokenTree) {
		var close:TokenTree = token.access().firstOf(Binop(OpGt)).token;
		if ((token.children == null) || (token.children.length <= 0)) {
			return;
		}
		var items:Array<WrappableItem> = makeWrappableItems(token);
		queueWrapping({
			origin: TypeParameterWrapping,
			start: token,
			end: close,
			items: items,
			rules: config.wrapping.typeParameter,
			useTrailing: true,
			overrideAdditionalIndent: null
		}, "wrapTypeParameter");
		return;
	}

	function markBrWrapping(token:TokenTree) {
		switch (TokenTreeCheckUtils.getBrOpenType(token)) {
			case Block:
			case TypedefDecl:
				typedefWrapping(token);
			case ObjectDecl:
				objectLiteralWrapping(token);
			case AnonType:
				anonTypeWrapping(token);
			case Unknown:
		}
	}

	function typedefWrapping(token:TokenTree) {
		var brClose:Null<TokenTree> = getCloseToken(token);
		if (isNewLineBefore(token)) {
			return;
		}
		if (parsedCode.isOriginalSameLine(token, brClose)) {
			noWrap(token, brClose);
			return;
		}
	}

	function anonTypeWrapping(token:TokenTree) {
		var brClose:Null<TokenTree> = getCloseToken(token);
		if ((token.children == null) || (token.children.length <= 0)) {
			return;
		}
		if (token.index + 1 == brClose.index) {
			whitespace(token, NoneAfter);
			whitespace(brClose, NoneBefore);
			return;
		}
		var next:Null<TokenInfo> = getNextToken(brClose);
		if (next != null) {
			switch (next.token.tok) {
				case BrOpen:
					switch (config.lineEnds.leftCurly) {
						case None, After:
							noLineEndAfter(brClose);
						case Before, Both:
					}
				case Binop(OpGt):
					noLineEndAfter(brClose);
				case Const(CIdent("from")), Const(CIdent("to")):
					noLineEndAfter(brClose);
				case Kwd(_), Const(_):
					lineEndAfter(brClose);
				default:
			}
		}
		if (!parsedCode.isOriginalSameLine(token, brClose)) {
			wrapChildOneLineEach(token, brClose, 0);
			return;
		}

		var items:Array<WrappableItem> = makeWrappableItems(token);

		applyWrappingPlace({
			origin: AnonTypeWrapping,
			start: token,
			end: brClose,
			items: items,
			rules: config.wrapping.anonType,
			useTrailing: true,
			overrideAdditionalIndent: null
		});
	}

	function objectLiteralWrapping(token:TokenTree) {
		var brClose:Null<TokenTree> = getCloseToken(token);
		if ((token.children == null) || (token.children.length <= 1)) {
			return;
		}
		if (token.index + 1 == brClose.index) {
			whitespace(token, NoneAfter);
			whitespace(brClose, NoneBefore);
			return;
		}
		// When original layout is multi-line, default behavior preserves it via one-per-line.
		// Exception: when this ObjectDecl is the body of an array-comprehension `for` with
		// FitLine policy AND the collapsed span fits on the surrounding line, follow the
		// configured rules (which typically pick NoWrap → collapse).
		if (!parsedCode.isOriginalSameLine(token, brClose)) {
			if (!shouldCollapseInComprehension(token, brClose)) {
				wrapChildOneLineEach(token, brClose, 0);
				return;
			}
		}
		var minLength:Int = 9999;
		var maxLength:Int = 0;
		var totalLength:Int = 0;
		var itemCount:Int = 0;
		for (child in token.children) {
			switch (child.tok) {
				case BrClose:
					break;
				case CommentLine(_):
					wrapChildOneLineEach(token, brClose, 0);
					return;
				default:
			}
			var length:Int = calcLength(child);
			totalLength += length;
			if (length > maxLength) {
				maxLength = length;
			}
			if (length < minLength) {
				minLength = length;
			}
			itemCount++;
		}
		var lineLength:Int = calcLineLength(token);
		var rule:WrapRule = determineWrapType(config.wrapping.objectLiteral, itemCount, minLength, maxLength, totalLength, lineLength);
		switch (rule.type) {
			case OnePerLine:
				wrapChildOneLineEach(token, brClose, rule.additionalIndent);
			case OnePerLineAfterFirst:
				wrapChildOneLineEach(token, brClose, rule.additionalIndent, true);
			case Keep:
				keep(token, brClose, rule.additionalIndent);
			case EqualNumber:
			case FillLine:
				wrapFillLine(token, brClose, config.wrapping.maxLineLength, rule.additionalIndent);
			case FillLineWithLeadingBreak:
				wrapFillLine(token, brClose, config.wrapping.maxLineLength, rule.additionalIndent);
			case NoWrap:
				noWrap(token, brClose);
				var next:TokenInfo = getNextToken(brClose);
				if (next != null) {
					switch (next.token.tok) {
						case DblDot:
							noLineEndAfter(brClose);
						case Dot, Comma:
							whitespace(brClose, NoneAfter);
						default:
					}
				}
				var prev:TokenInfo = getPreviousToken(token);
				if (prev != null) {
					switch (prev.token.tok) {
						case Kwd(KwdElse):
							// Don't override line end before object literal body after else;
							// MarkSameLine controls else-body placement for expression-if
						case Kwd(_):
							noLineEndBefore(token);
							whitespace(token, Before);
						case POpen, Binop(_), Comma:
							noLineEndBefore(token);
						default:
					}
				}
		}
	}

	/**
	 * Returns true when `brOpen` is an ObjectDecl in the body of an array-comprehension
	 * `for` (possibly wrapped in expressionParens like `({...})`) under FitLine policy
	 * AND the full struct collapsed onto its current line would fit in maxLineLength.
	 * In that case the multi-line layout from the source can be discarded; otherwise
	 * preserve original structure via one-per-line.
	 */
	function shouldCollapseInComprehension(brOpen:TokenTree, brClose:TokenTree):Bool {
		if (config.sameLine.comprehensionFor != FitLine) return false;
		if (!isInsideComprehensionForBody(brOpen)) return false;
		final indent:Int = indenter.calcAbsoluteIndent(indenter.calcIndent(brOpen));
		final collapsedSpan:Int = calcSpanLength(brOpen, brClose);
		return (indent + calcLineLengthBefore(brOpen) + collapsedSpan) <= config.wrapping.maxLineLength;
	}

	function isInsideComprehensionForBody(token:TokenTree):Bool {
		var parent:Null<TokenTree> = token.parent;
		while (parent != null) {
			switch (parent.tok) {
				case Kwd(KwdFor):
					return isComprehensionFor(parent);
				case BrOpen:
					return false;
				default:
					parent = parent.parent;
			}
		}
		return false;
	}

	function isComprehensionFor(forKw:TokenTree):Bool {
		var parent:Null<TokenTree> = forKw.parent;
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

	function markPWrapping(token:TokenTree) {
		var pClose:Null<TokenTree> = getCloseToken(token);
		switch (TokenTreeCheckUtils.getPOpenType(token)) {
			case At:
				wrapMetadataCallParameter(token);
			case Parameter:
				wrapFunctionSignature(token);
			case Call:
				wrapCallParameter(token);
			case WhileCondition:
				wrapCondition(token);
			case IfCondition:
				if (!isComprehension(token)) {
					wrapCondition(token);
				}
			case ForLoop:
				if (!isComprehension(token)) {
					wrapCondition(token);
				}
			case SwitchCondition:
			case SharpCondition:
			case Catch:
			case Expression:
				wrapExpressionParen(token);
		}
	}

	function arrayWrapping(token:TokenTree) {
		switch (TokenTreeCheckUtils.getBkOpenType(token)) {
			case ArrayAccess | ArrayLiteral | Comprehension | Unknown:
				arrayLiteralWrapping(token);
			case MapLiteral:
				mapLiteralWrapping(token);
		}
	}

	function arrayLiteralWrapping(token:TokenTree) {
		var bkClose:Null<TokenTree> = getCloseToken(token);
		if ((token.children == null) || (token.children.length <= 0)) {
			return;
		}
		var items:Array<WrappableItem> = makeWrappableItems(token);
		var itemsWithoutMetadata:Array<WrappableItem> = [];
		for (item in items) {
			switch (item.first.tok) {
				case Kwd(KwdFor), Kwd(KwdWhile):
					if (config.sameLine.comprehensionFor == Keep) {
						return;
					}
					// FitLine: MarkSameLine has already glued `[for`/`]` and decided body
					// staircase via forBody policy — applying arrayWrap rules here (esp.
					// onePerLine on hasMultilineItems) would re-insert breaks before `for`
					// and `]`, defeating the glue. Skip wrapping entirely.
					if (config.sameLine.comprehensionFor == FitLine) {
						return;
					}
					itemsWithoutMetadata.push(item);
				case At:
					if (item.firstLineLength > 30) {
						lineEndBefore(token);
						lineEndBefore(item.first);
					}
				default:
					itemsWithoutMetadata.push(item);
			}
		}
		if (config.wrapping.arrayMatrixWrap != NoMatrixWrap) {
			if (tryMatrixWrap(token, bkClose, itemsWithoutMetadata)) {
				return;
			}
		}
		applyWrappingPlace({
			origin: ArrayWrapping,
			start: token,
			end: bkClose,
			items: itemsWithoutMetadata,
			rules: config.wrapping.arrayWrap,
			useTrailing: true,
			overrideAdditionalIndent: null
		});
	}

	function tryMatrixWrap(open:TokenTree, close:TokenTree, items:Array<WrappableItem>):Bool {
		var prev:Null<WrappableItem> = null;
		var run:Int = 1;
		var lineRun:Int = 0;
		for (index in 0...items.length) {
			var item:WrappableItem = items[index];
			if (prev == null) {
				prev = item;
				continue;
			}
			if (item.multiline) {
				return false;
			}
			if (parsedCode.isOriginalSameLine(prev.first, item.first)) {
				run++;
				prev = item;
				continue;
			}
			if (lineRun != 0) {
				if (lineRun != run) {
					return false;
				}
			}
			lineRun = run;
			run = 1;
			prev = item;
		}
		if (lineRun <= 1) {
			return false;
		}
		if (lineRun != run) {
			return false;
		}
		lineEndAfter(open);

		if (config.wrapping.arrayMatrixWrap == MatrixWrapWithAlign) {
			var maxCols:Array<Int> = [for (i in 0...lineRun) 0];
			for (index in 0...items.length) {
				var item:WrappableItem = items[index];
				var col:Int = index % lineRun;
				if (item.firstLineLength > maxCols[col]) {
					maxCols[col] = item.firstLineLength;
				}
			}

			for (index in 0...items.length) {
				var item:WrappableItem = items[index];
				var expectedLength:Int = maxCols[index % lineRun];
				if (index == items.length - 1) {
					switch (item.last.tok) {
						case Comma:
							expectedLength -= 1;
						default:
							expectedLength -= 2;
					}
				}
				if (item.firstLineLength < expectedLength) {
					spacesBefore(item.first, expectedLength - item.firstLineLength);
				}
			}
		}
		var index:Int = lineRun - 1;
		while (index < items.length) {
			var item:WrappableItem = items[index];
			lineEndAfter(item.last);
			index += lineRun;
		}
		return true;
	}

	function mapLiteralWrapping(token:TokenTree) {
		var bkClose:Null<TokenTree> = getCloseToken(token);
		if ((token.children == null) || (token.children.length <= 0)) {
			return;
		}
		var items:Array<WrappableItem> = makeWrappableItems(token);
		var itemsWithoutMetadata:Array<WrappableItem> = [];
		for (item in items) {
			switch (item.first.tok) {
				case At:
					if (item.firstLineLength > 30) {
						lineEndBefore(token);
						lineEndBefore(item.first);
					}
				default:
					itemsWithoutMetadata.push(item);
			}
		}
		applyWrappingPlace({
			origin: MapWrapping,
			start: token,
			end: bkClose,
			items: itemsWithoutMetadata,
			rules: config.wrapping.mapWrap,
			useTrailing: true,
			overrideAdditionalIndent: null
		});
	}

	override function calcLineLength(token:TokenTree):Int {
		if (token == null) {
			return 0;
		}
		return super.calcLineLength(token);
	}

	function wrapFunctionSignature(token:TokenTree) {
		var pClose:TokenTree = getCloseToken(token);
		if ((token.children == null) || (token.children.length <= 0)) {
			return;
		}
		var rules:WrapRules = config.wrapping.functionSignature;
		switch (token.parent.tok) {
			case Kwd(KwdFunction):
				rules = config.wrapping.anonFunctionSignature;
			default:
		}
		var emptyBody:Bool = hasEmptyFunctionBody(token);
		var items:Array<WrappableItem> = makeWrappableItems(token);
		var rule:WrapRule = determineWrapType2(rules, token, items);
		if (rule.type == FillLineWithLeadingBreak) {
			parenIndentWraps.push(token);
		}
		var addIndent:Null<Int> = null;
		if (emptyBody) {
			addIndent = 0;
		}
		queueWrapping({
			origin: FunctionSignatureWrapping,
			start: token,
			end: pClose,
			items: items,
			rules: rules,
			useTrailing: true,
			overrideAdditionalIndent: addIndent
		}, "wrapFunctionSignature");
	}

	function wrapCallParameter(token:TokenTree) {
		var pClose:TokenTree = getCloseToken(token);
		if ((token.children == null) || (token.children.length <= 0)) {
			return;
		}
		var items:Array<WrappableItem> = makeWrappableItems(token);
		var rule:WrapRule = determineWrapType2(config.wrapping.callParameter, token, items);
		if (rule.type == FillLineWithLeadingBreak) {
			parenIndentWraps.push(token);
		}
		queueWrapping({
			origin: CallParameterWrapping,
			start: token,
			end: pClose,
			items: items,
			rules: config.wrapping.callParameter,
			useTrailing: true,
			overrideAdditionalIndent: null
		}, "wrapCallParameter");
	}

	function wrapMetadataCallParameter(token:TokenTree) {
		var pClose:TokenTree = getCloseToken(token);
		if ((token.children == null) || (token.children.length <= 0)) {
			return;
		}
		var items:Array<WrappableItem> = makeWrappableItems(token);
		queueWrapping({
			origin: MetadataCallParameterWrapping,
			start: token,
			end: pClose,
			items: items,
			rules: config.wrapping.metadataCallParameter,
			useTrailing: false,
			overrideAdditionalIndent: null
		}, "wrapMetadataCallParameter");
	}

	function wrapCondition(token:TokenTree) {
		if ((token.children == null) || (token.children.length <= 0)) {
			return;
		}
		var pClose:Null<TokenTree> = getCloseToken(token);
		if (pClose == null) {
			return;
		}
		// Skip if line exceeds only due to trailing comment — code itself fits
		if (calcLineLengthNoComment(token) <= config.wrapping.maxLineLength) {
			return;
		}
		var items:Array<WrappableItem> = makeWrappableItems(token);
		var rule:WrapRule = determineWrapType2(config.wrapping.conditionWrapping, token, items);
		if (rule.type != NoWrap && rule.type != Keep) {
			conditionWraps.push(token);
		}
	}

	/** calcLineLength excluding trailing line comment. */
	function calcLineLengthNoComment(token:TokenTree):Int {
		var len:Int = calcLineLength(token);
		// Walk forward from token to find CommentLine on same line
		var idx:Int = token.index;
		while (idx < parsedCode.tokenList.tokens.length) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			if (info.token.tok.match(CommentLine(_))) {
				len -= info.text.length;
				// Also subtract the space before comment
				var prev:Null<TokenInfo> = parsedCode.tokenList.tokens[idx - 2];
				if (prev != null && prev.spacesAfter > 0) len -= prev.spacesAfter;
				break;
			}
			if (info.whitespaceAfter == Newline) break;
		}
		return len;
	}

	function wrapExpressionParen(token:TokenTree) {
		if ((token.children == null) || (token.children.length <= 0)) {
			return;
		}
		var pClose:Null<TokenTree> = getCloseToken(token);
		if (pClose == null) {
			return;
		}
		var contentLength:Int = calcSpanLength(token, pClose);
		// Skip short content — wrapping small grouping parens (e.g. `(a && b)`) is not useful.
		if (contentLength < Std.int(config.wrapping.maxLineLength / 2)) {
			return;
		}
		// Skip disambiguation parens around struct literals: ({field: value})
		// The ( is just a parser hint, not a meaningful grouping to wrap.
		if (token.children[0].tok.match(BrOpen)) {
			return;
		}
		// Skip expression parens that are part of an opBoolChain item (preceded by &&/||),
		// UNLESS the paren content + wrapping indent would exceed maxLineLength.
		// After opBoolChain wrapping, the paren gets at least +1 indent level.
		var indent:Int = indenter.calcAbsoluteIndent(indenter.calcIndent(token));
		var prev:Null<TokenInfo> = getPreviousToken(token);
		if (prev != null) {
			switch (prev.token.tok) {
				case Binop(OpBoolAnd), Binop(OpBoolOr):
					var wrappedIndent:Int = indent + indenter.calcAbsoluteIndent(1);
					if (wrappedIndent + contentLength < config.wrapping.maxLineLength) {
						return;
					}
				default:
			}
		}
		var items:Array<WrappableItem> = makeWrappableItems(token);
		var rule:WrapRule = determineWrapType2(config.wrapping.expressionWrapping, token, items);
		if (rule.type != NoWrap && rule.type != Keep) {
			expressionWraps.push(token);
		}
	}

	/** Sum token text lengths + spaces from start to end (inclusive), ignoring newlines. */
	function calcSpanLength(start:TokenTree, end:TokenTree):Int {
		var length:Int = 0;
		var idx:Int = start.index;
		while (idx <= end.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			length += info.text.length;
			if (idx <= end.index) {
				switch (info.whitespaceAfter) {
					case Space:
						length += info.spacesAfter;
					case Newline:
						length += 1; // Count newline as single space
					case None:
				}
			}
		}
		return length;
	}

	/**
	 * Collect statement-level `var`/`final`/field initializer `=` tokens.
	 * These are the only break point that keeps type parameters `<...>` and
	 * call arguments intact when a declaration line exceeds maxLineLength.
	 */
	function markAssignmentChaining() {
		parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case Binop(OpAssign):
					if (isDeclarationAssign(token)) {
						assignmentWraps.push(token);
					}
				default:
			}
			return GoDeeper;
		});
	}

	/** `=` that initializes a `var`/`final` declaration (not a typedef, not nested in a call/array/block). */
	function isDeclarationAssign(token:TokenTree):Bool {
		var parent:Null<TokenTree> = token.parent;
		while (parent != null) {
			switch (parent.tok) {
				case Kwd(KwdVar), Kwd(KwdFinal):
					return !TokenTreeCheckUtils.isInsideTypedef(token);
				case POpen, BkOpen, Binop(OpArrow), Arrow:
					return false;
				case BrOpen:
					return TokenTreeCheckUtils.getBrOpenType(parent) != Block;
				default:
			}
			parent = parent.parent;
		}
		return false;
	}

	/** First token of the declaration's line: the `var`/`final` keyword, lifted through any leading modifiers/metadata. */
	function findDeclarationRoot(token:TokenTree):TokenTree {
		var root:Null<TokenTree> = token;
		while (root != null) {
			switch (root.tok) {
				case Kwd(KwdVar), Kwd(KwdFinal):
					break;
				default:
			}
			root = root.parent;
		}
		if (root == null) {
			return token;
		}
		while (root.parent != null) {
			switch (root.parent.tok) {
				case Kwd(KwdPublic), Kwd(KwdPrivate), Kwd(KwdStatic), Kwd(KwdOverride), Kwd(KwdInline), Kwd(KwdDynamic), Kwd(KwdMacro),
					Kwd(KwdExtern), Kwd(KwdAbstract), Kwd(KwdOverload), At:
					root = root.parent;
				default:
					return root;
			}
		}
		return root;
	}

	/**
	 * Post-queue: when a typed declaration `field/var:Type<...> = expr;` is too
	 *  long and the formatter resolved it by splitting the left-side type
	 *  parameters, break after `=` instead and collapse the `<...>` back onto
	 *  one line — provided both halves then fit. Scope is intentionally narrow:
	 *  it only acts when a type parameter list was actually broken, so plain
	 *  call/array/object initializers keep their normal wrapping.
	 */
	function applyAssignmentWrapping() {
		for (assign in assignmentWraps) {
			var next:Null<TokenInfo> = getNextToken(assign);
			if (next == null) {
				continue;
			}
			var declRoot:TokenTree = findDeclarationRoot(assign);
			var semicolon:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(declRoot);
			if (semicolon == null) {
				continue;
			}
			if (findLhsTypeParameter(declRoot, assign) == null) {
				continue;
			}
			var maxLen:Int = config.wrapping.maxLineLength;
			var indent:Int = calcLineLengthBefore(declRoot);
			// First line the formatter would keep if it wraps the RHS at its outermost
			// bracket instead of breaking at `=`. If that still exceeds maxLineLength,
			// the only remaining split is inside the type parameters — break at `=`.
			var rhsWrapOpen:Null<TokenTree> = findFirstWrapBracket(next.token, semicolon);
			var keptFirstLine:Int = indent + (rhsWrapOpen == null ? calcSpanLength(declRoot, semicolon) : calcSpanLength(declRoot, rhsWrapOpen));
			if (keptFirstLine <= maxLen) {
				continue;
			}
			var lhsLen:Int = indent + calcSpanLength(declRoot, assign);
			var rhsLen:Int = indent + config.indentation.tabWidth + calcSpanLength(next.token, semicolon);
			if (lhsLen > maxLen || rhsLen > maxLen) {
				continue;
			}
			lineEndAfter(assign);
			collapseTypeParameterBreaks(declRoot, assign);
			collapseTypeParameterBreaks(next.token, semicolon);
		}
	}

	/**
	 * Late post-pass (after all bracket/call/type-param wrapping is materialized):
	 *  `applyAssignmentWrapping`'s keptFirstLine predictor assumes the RHS bracket
	 *  wraps; when it does not (e.g. a single short call argument → callParameter
	 *  noWrap), the line containing `=` may still overflow after every other wrap
	 *  has run. In that case, break at `=` and collapse any type-parameter splits
	 *  on either side, provided both halves then fit.
	 */
	function applyAssignmentTypeParamCollapse() {
		for (assign in assignmentWraps) {
			var next:Null<TokenInfo> = getNextToken(assign);
			if (next == null) {
				continue;
			}
			if (isNewLineAfter(assign)) {
				continue;
			}
			var declRoot:TokenTree = findDeclarationRoot(assign);
			var semicolon:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(declRoot);
			if (semicolon == null) {
				continue;
			}
			// Same scope as applyAssignmentWrapping: only typed declarations
			//  (`field:Type<...> = ...`); a bare `var x = new T<...>(...)` keeps
			//  its RHS type-parameter split.
			if (findLhsTypeParameter(declRoot, assign) == null) {
				continue;
			}
			var maxLen:Int = config.wrapping.maxLineLength;
			// Gate: only fire when the line containing `=` still overflows after
			//  every other wrap pass. If callParameter (or another inner bracket)
			//  already broke the line to fit, breaking at `=` would be redundant.
			if (calcLineLength(assign) <= maxLen) {
				continue;
			}
			var indent:Int = calcLineLengthBefore(declRoot);
			var lhsLen:Int = indent + calcSpanLength(declRoot, assign);
			var rhsLen:Int = indent + config.indentation.tabWidth + calcSpanLength(next.token, semicolon);
			if (lhsLen > maxLen || rhsLen > maxLen) {
				continue;
			}
			lineEndAfter(assign);
			collapseTypeParameterBreaks(declRoot, assign);
			collapseTypeParameterBreaks(next.token, semicolon);
		}
	}

	/**
	 * Post-queue: when an `extends`/`implements` clause cannot fit on the
	 *  declaration line — either because the base type's type parameters
	 *  `<...>` have been split, or because the line as a whole still exceeds
	 *  maxLineLength after every other wrap — break before the `extends` /
	 *  `implements` keyword and collapse any split `<...>` back onto one line,
	 *  provided both halves then fit.
	 */
	function applyExtendsWrapping() {
		for (wrap in extendsWraps) {
			var first:TokenTree = wrap.first;
			var end:TokenTree = wrap.end;
			var lineStart:Null<TokenTree> = findLineStartToken(first);
			if (lineStart == null) {
				continue;
			}
			var prev:Null<TokenInfo> = getPreviousToken(first);
			if (prev == null) {
				continue;
			}
			var maxLen:Int = config.wrapping.maxLineLength;
			if (calcLineLength(first) <= maxLen && !hasWrappedTypeParameter(first, end)) {
				continue;
			}
			var indent:Int = calcLineLengthBefore(lineStart);
			// Identify leading `@:meta` chain on the declaration line. When present,
			//  lifting the metadata to its own line is preferred over breaking
			//  before `extends`/`implements` if it alone makes the declaration line
			//  fit (combine both only when neither alone fits).
			var lastMetaToken:Null<TokenTree> = null;
			var declStart:TokenTree = lineStart;
			if (lineStart.tok.match(At)) {
				var lastMeta:TokenTree = lineStart;
				var sib:Null<TokenTree> = lineStart.nextSibling;
				while ((sib != null) && sib.tok.match(At)) {
					lastMeta = sib;
					sib = sib.nextSibling;
				}
				lastMetaToken = TokenTreeCheckUtils.getLastToken(lastMeta);
				if (lastMetaToken != null) {
					var afterMeta:Null<TokenInfo> = getNextToken(lastMetaToken);
					if (afterMeta != null) {
						declStart = afterMeta.token;
					} else {
						lastMetaToken = null;
					}
				}
			}
			// Extend `end` to include the class body `{` when present — it's part
			//  of the visual line, calcSpanLength stops before its trailing space.
			var lineEnd:TokenTree = end;
			var afterEnd:Null<TokenInfo> = getNextToken(end);
			if (afterEnd != null && afterEnd.token.tok.match(BrOpen)) {
				lineEnd = afterEnd.token;
			}
			// Line kept on the declaration line if we break before `extends`.
			var headWithMeta:Int = indent + calcSpanLength(lineStart, prev.token);
			// Continuation line indented one level (a declaration continuation,
			//  not an onePerLine implements list), type parameters collapsed
			//  back onto one line.
			var contLen:Int = indent + config.indentation.tabWidth + calcSpanLength(first, lineEnd);
			var hasMeta:Bool = lastMetaToken != null;
			var declLenNoMeta:Int = hasMeta ? indent + calcSpanLength(declStart, lineEnd) : 0;
			var headNoMeta:Int = hasMeta ? indent + calcSpanLength(declStart, prev.token) : 0;
			var aFits:Bool = headWithMeta <= maxLen && contLen <= maxLen;
			var bFits:Bool = hasMeta && declLenNoMeta <= maxLen;
			var cFits:Bool = hasMeta && headNoMeta <= maxLen && contLen <= maxLen;
			if (bFits) {
				lineEndAfter(lastMetaToken);
				collapseTypeParameterBreaks(first, end);
				continue;
			}
			if (aFits) {
				lineEndBefore(first);
				additionalIndent(first, 1);
				collapseTypeParameterBreaks(first, end);
				continue;
			}
			if (cFits) {
				lineEndAfter(lastMetaToken);
				lineEndBefore(first);
				additionalIndent(first, 1);
				collapseTypeParameterBreaks(first, end);
				continue;
			}
		}
	}

	/**
	 * Matching close `>` of a type-parameter `<` — the last token of the `<`
	 *  subtree. `firstOf(Binop(OpGt))` would return a nested `>` (e.g. the inner
	 *  `Null<Language>` close), truncating the scan range.
	 */
	function typeParamClose(lt:TokenTree):Null<TokenTree> {
		var last:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(lt);
		if (last != null && last.tok.match(Binop(OpGt))) {
			return last;
		}
		return lt.access().firstOf(Binop(OpGt)).token;
	}

	/**
	 * True when a type parameter `<...>` in the range has an internal break point
	 *  — a soft `wrapAfter` (TypeParameterWrapping's split, resolved at emit when
	 *  the line overflows) or an already-materialized hard `Newline`.
	 */
	function hasWrappedTypeParameter(start:TokenTree, end:TokenTree):Bool {
		var idx:Int = start.index;
		while (idx <= end.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) {
				continue;
			}
			if (!info.token.tok.match(Binop(OpLt)) || !TokenTreeCheckUtils.isTypeParameter(info.token)) {
				continue;
			}
			var close:Null<TokenTree> = typeParamClose(info.token);
			if (close == null) {
				continue;
			}
			var inner:Int = info.token.index;
			while (inner < close.index) {
				var innerInfo:Null<TokenInfo> = parsedCode.tokenList.tokens[inner];
				inner++;
				if (innerInfo != null && (innerInfo.wrapAfter || innerInfo.whitespaceAfter == Newline)) {
					return true;
				}
			}
		}
		return false;
	}

	/** First `(`/`[`/`{` between start and end — the RHS's outermost wrappable bracket. */
	function findFirstWrapBracket(start:TokenTree, end:TokenTree):Null<TokenTree> {
		var idx:Int = start.index;
		while (idx <= end.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) {
				continue;
			}
			switch (info.token.tok) {
				case POpen, BkOpen, BrOpen:
					return info.token;
				default:
			}
		}
		return null;
	}

	/** First left-side (declaration type) type parameter `<...>` opening token, or null. */
	function findLhsTypeParameter(declRoot:TokenTree, assign:TokenTree):Null<TokenTree> {
		var idx:Int = declRoot.index;
		while (idx < assign.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) {
				continue;
			}
			if (info.token.tok.match(Binop(OpLt)) && TokenTreeCheckUtils.isTypeParameter(info.token)) {
				return info.token;
			}
		}
		return null;
	}

	/** Collapse line breaks inside every type parameter `<...>` group within the range, when the merged line fits. */
	function collapseTypeParameterBreaks(start:TokenTree, end:TokenTree) {
		var idx:Int = start.index;
		while (idx <= end.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) {
				continue;
			}
			if (!info.token.tok.match(Binop(OpLt)) || !TokenTreeCheckUtils.isTypeParameter(info.token)) {
				continue;
			}
			var close:Null<TokenTree> = typeParamClose(info.token);
			if (close == null) {
				continue;
			}
			var inner:Int = info.token.index + 1;
			while (inner <= close.index) {
				var innerInfo:Null<TokenInfo> = parsedCode.tokenList.tokens[inner];
				inner++;
				if (innerInfo != null) {
					tryCollapseBreakBefore(innerInfo.token);
				}
			}
		}
	}

	function isComprehension(pOpen:TokenTree):Bool {
		var parent:Null<TokenTree> = pOpen.parent;
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

	function applyParenIndentWrapping() {
		for (token in parenIndentWraps) {
			var pClose:Null<TokenTree> = getCloseToken(token);
			if (pClose == null) {
				continue;
			}
			if (isNewLineAfter(token)) {
				// Skip lineEndBefore(pClose) when the content ends with a block —
				// `}))` should stay on one line, not become `}\n))`.
				// But if the content between POpen and PClose spans multiple lines
				// (e.g. callParam wrapping inside a method chain), `)` must be on its own line.
				if (endsWithBrClose(pClose) && !hasLineBreaksBetween(token.index + 1, pClose.index - 1)) {
					continue;
				}
				lineEndBefore(pClose);
			}
		}
	}

	/**
	 * Check if the token before pClose (walking through intermediate PClose) is BrClose.
	 *  Returns false if any intermediate PClose has its own callParam wrapping (newline after POpen).
	 */
	function endsWithBrClose(pClose:TokenTree):Bool {
		var prev:Null<TokenInfo> = getPreviousToken(pClose);
		while (prev != null && prev.token.tok.match(PClose)) {
			// If this intermediate PClose's matching POpen has callParam wrapping,
			// stop — this PClose needs its own line break.
			var matchingPOpen:Null<TokenTree> = prev.token.parent;
			if (matchingPOpen != null && matchingPOpen.tok.match(POpen) && isNewLineAfter(matchingPOpen)) {
				return false;
			}
			prev = getPreviousToken(prev.token);
		}
		return prev != null && prev.token.tok.match(BrClose);
	}

	function applyArrowWrapping() {
		for (token in arrowWraps) {
			lineEndAfter(token);
		}
		for (token in arrowWraps) {
			if (token.children == null) {
				continue;
			}
			for (child in token.children) {
				removeInnerArrowBreaks(child);
				var lastToken:TokenTree = TokenTreeCheckUtils.getLastToken(child);
				if (lastToken != null) {
					unwrapBoolOps(child, lastToken);
					unwrapAddOps(child, lastToken);
				}
			}
		}
		// Collapse arrows that now fit, apply PClose for remaining
		for (token in arrowWraps) {
			if (!isNewLineAfter(token)) {
				continue;
			}
			// Try collapse: remove break, check if line fits
			noLineEndAfter(token);
			if (calcLineLength(token) <= config.wrapping.maxLineLength) {
				continue;
			}
			// Short struct body (u -> {email: ...}): keep collapsed — method chain will handle the line.
			// calcLineLength may overestimate because method chain breaks haven't been finalized yet.
			if (token.children != null && token.children.length > 0 && token.children[0].tok.match(BrOpen)) {
				var brClose:Null<TokenTree> = getCloseToken(token.children[0]);
				if (brClose != null && calcSpanLength(token, brClose) < Std.int(config.wrapping.maxLineLength / 2)) {
					continue;
				}
			}
			// Doesn't fit — restore break
			lineEndAfter(token);
			var parent:Null<TokenTree> = token.parent;
			while (parent != null) {
				switch (parent.tok) {
					case POpen:
						switch (TokenTreeCheckUtils.getPOpenType(parent)) {
							case Call:
								var pClose:Null<TokenTree> = getCloseToken(parent);
								if (pClose != null) {
									lineEndBefore(pClose);
								}
								break;
							default:
								parent = parent.parent;
						}
					default:
						parent = parent.parent;
				}
			}
		}
	}

	function removeInnerArrowBreaks(token:TokenTree) {
		if (token.children == null) {
			return;
		}
		for (child in token.children) {
			switch (child.tok) {
				case Binop(OpArrow), Arrow:
					if (isNewLineAfter(child) && calcLineLength(child) <= config.wrapping.maxLineLength) {
						noLineEndAfter(child);
					}
				default:
			}
			removeInnerArrowBreaks(child);
		}
	}

	function applyConditionWrapping() {
		for (token in conditionWraps) {
			var pClose:Null<TokenTree> = getCloseToken(token);
			if (pClose == null) {
				continue;
			}
			if (findWrappedPOpen(token, pClose) && !hasChainBreaks(token, pClose)) {
				// Skip if inner paren wrapping handles the line length.
				// Exception: when opBoolChain is inside and full span exceeds,
				// condition wrapping is needed so opBoolChain can re-evaluate.
				if (!hasInnerOpBoolChain(token, pClose)) {
					continue;
				}
				var indent:Int = indenter.calcAbsoluteIndent(indenter.calcIndent(token));
				if (indent + calcSpanLength(token, pClose) <= config.wrapping.maxLineLength) {
					continue;
				}
			}
			if (hasInnerArrowBreak(token, pClose)
				&& calcLineLength(token) <= config.wrapping.maxLineLength
				&& !hasChainBreaks(token, pClose)) {
				continue;
			}
			// Skip if method chain breaks already handle the line length —
			// condition wrapping would re-wrap content that's already broken.
			if (hasMethodChainBreaks(token.index, pClose.index) && calcLineLength(token) <= config.wrapping.maxLineLength) {
				continue;
			}
			// Re-check: if condition is inside a wrapped arrow/call, the line is now shorter.
			if (isInsideWrappedArrowOrCall(token)) {
				var condIndent:Int = indenter.calcAbsoluteIndent(indenter.calcIndent(token));
				var condTotal:Int = condIndent + calcLineLengthBefore(token) + calcSpanLength(token, pClose) + calcLineLengthAfter(pClose);
				if (condTotal <= config.wrapping.maxLineLength) {
					continue;
				}
			}
			lineEndAfter(token);
			lineEndBefore(pClose);
			// Re-evaluate opBoolChain inside BEFORE collapse: the queue applied it before
			// condition wrapping with callParameter shortening the line, causing NoWrap.
			// Must run before tryFullCollapseCondition so collapse sees the chain breaks.
			reApplyInnerOpBoolChain(token, pClose);
			tryFullCollapseCondition(token, pClose);
			// Collapse inner callParameter breaks that now fit after condition wrapping
			collapseInnerCallParamBreaks(token, pClose);
		}
	}

	/** Check if there's an opBoolChain at condition depth (not nested inside inner calls). */
	function hasInnerOpBoolChain(open:TokenTree, close:TokenTree):Bool {
		for (place in wrappingQueue) {
			if (place.origin != OpBoolChainWrapping) continue;
			var startIdx:Int = getPlaceStartIndex(place);
			var endIdx:Int = getPlaceEndIndex(place);
			if (startIdx < open.index || endIdx > close.index) continue;
			// Check that the chain is not nested inside another POpen (call/lambda)
			if (!isNestedInsideInnerPOpen(place.start, open)) return true;
		}
		return false;
	}

	/** Check if token is inside an inner POpen (between open and some nested POpen/PClose). */
	function isNestedInsideInnerPOpen(token:TokenTree, condOpen:TokenTree):Bool {
		var parent:Null<TokenTree> = token.parent;
		while (parent != null && parent.tok != Root) {
			if (parent.index == condOpen.index) return false;
			switch (parent.tok) {
				case POpen:
					return true;
				default:
			}
			parent = parent.parent;
		}
		return false;
	}

	/** Re-evaluate opBoolChain wrapping inside a condition that was just wrapped.
	 *  During queue processing, inner callParameter was applied before opBoolChain,
	 *  shortening the line and causing NoWrap. After condition wrapping changes the
	 *  indent level, opBoolChain may need to fire.
	 *  Strips inner breaks first so calcLineLength sees the true line span. */
	function reApplyInnerOpBoolChain(open:TokenTree, close:TokenTree) {
		for (place in wrappingQueue) {
			if (place.origin != OpBoolChainWrapping) continue;
			if (place.start == null || place.items == null) continue;
			var startIdx:Int = getPlaceStartIndex(place);
			var endIdx:Int = getPlaceEndIndex(place);
			if (startIdx < open.index || endIdx > close.index) continue;
			// Only re-apply if opBoolChain decided NoWrap in queue (no chain breaks present).
			// If it already wrapped, the breaks are correct — no need to re-evaluate.
			if (hasChainBreaks(open, close)) continue;
			// Strip inner breaks (e.g. callParameter) so calcLineLength sees true span
			var idx:Int = open.index + 1;
			while (idx < close.index) {
				var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
				idx++;
				if (info == null) continue;
				if (isNewLineAfter(info.token)) {
					noLineEndAfter(info.token);
				}
			}
			applyWrappingPlace(place);
		}
	}

	/** After condition wrapping, try to collapse callParameter breaks inside that now fit on one line. */
	function collapseInnerCallParamBreaks(open:TokenTree, close:TokenTree) {
		var idx:Int = open.index + 1;
		while (idx < close.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			if (info.token.tok.match(POpen) && info.whitespaceAfter == Newline) {
				var pClose:Null<TokenTree> = getCloseToken(info.token);
				if (pClose == null) continue;
				// Try collapse: remove breaks, check if line fits
				noLineEndAfter(info.token);
				noLineEndBefore(pClose);
				if (calcLineLength(info.token) <= config.wrapping.maxLineLength) {
					idx = pClose.index + 1;
					continue; // fits — keep collapsed
				}
				// Doesn't fit — restore
				lineEndAfter(info.token);
				lineEndBefore(pClose);
				idx = pClose.index + 1;
			}
		}
	}

	/**
	 * After condition wrapping, try to undo it if the full condition (with all chain breaks removed)
	 * fits on one line. Also collapses inner chain breaks that fit.
	 */
	function tryFullCollapseCondition(open:TokenTree, close:TokenTree) {
		// Collect inner chain breaks
		var breaksBefore:Array<TokenTree> = [];
		var breaksAfter:Array<TokenTree> = [];
		collectChainBreaks(open, close, breaksBefore, breaksAfter);
		// Only attempt full collapse if there are no other (non-chain) breaks inside
		if (hasNonChainBreaks(open, close)) {
			// Inner wrapping (callParameter, arrow, etc.) — try collapsing chain breaks.
			// Use span check: calcLineLength only sees first line (up to arrow/call break),
			// but full condition span may exceed and need the chain break.
			if (breaksBefore.length > 0 || breaksAfter.length > 0) {
				var condIndent:Int = indenter.calcAbsoluteIndent(indenter.calcIndent(open) + 1);
				if (condIndent + calcSpanLength(open, close) > config.wrapping.maxLineLength) return;
				for (token in breaksBefore) noLineEndBefore(token);
				for (token in breaksAfter) noLineEndAfter(token);
			}
			return;
		}
		// No inner breaks — try full collapse (remove condition wrapping + chain breaks, measure actual line)
		noLineEndAfter(open);
		noLineEndBefore(close);
		for (token in breaksBefore) noLineEndBefore(token);
		for (token in breaksAfter) noLineEndAfter(token);
		if (calcLineLength(open) <= config.wrapping.maxLineLength) return;
		// Doesn't fit — restore condition wrapping
		lineEndAfter(open);
		lineEndBefore(close);
		// Try collapsing just chain breaks inside
		if (breaksBefore.length > 0 || breaksAfter.length > 0) {
			for (token in breaksBefore) noLineEndBefore(token);
			for (token in breaksAfter) noLineEndAfter(token);
			var measureToken:TokenTree = breaksAfter.length > 0 ? breaksAfter[0] : breaksBefore[0];
			if (calcLineLength(measureToken) <= config.wrapping.maxLineLength) return;
			for (token in breaksBefore) lineEndBefore(token);
			for (token in breaksAfter) lineEndAfter(token);
		}
	}

	function hasNonChainBreaks(open:TokenTree, close:TokenTree):Bool {
		var idx:Int = open.index + 1;
		while (idx < close.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			if (info.whitespaceAfter != Newline) continue;
			switch (info.token.tok) {
				case Binop(OpBoolAnd), Binop(OpBoolOr), Binop(OpAdd), Binop(OpSub):
					continue;
				default:
					return true;
			}
		}
		return false;
	}

	function hasChainBreaks(open:TokenTree, close:TokenTree):Bool {
		var idx:Int = open.index;
		while (idx < close.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Binop(OpBoolAnd), Binop(OpBoolOr), Binop(OpAdd), Binop(OpSub):
					if (info.whitespaceAfter == Newline || isNewLineBefore(info.token)) return true;
				default:
			}
		}
		return false;
	}

	function collectChainBreaks(open:TokenTree, close:TokenTree, breaksBefore:Array<TokenTree>, breaksAfter:Array<TokenTree>) {
		var idx:Int = open.index;
		while (idx < close.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Binop(OpBoolAnd), Binop(OpBoolOr), Binop(OpAdd), Binop(OpSub):
					if (isNewLineBefore(info.token)) breaksBefore.push(info.token);
					if (info.whitespaceAfter == Newline) breaksAfter.push(info.token);
				default:
			}
		}
	}

	/** Check if there's an arrow break inside the condition (from arrow wrapping). */
	function hasInnerArrowBreak(open:TokenTree, close:TokenTree):Bool {
		var idx:Int = open.index;
		while (idx < close.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Arrow, Binop(OpArrow):
					if (info.whitespaceAfter == Newline) return true;
				default:
			}
		}
		return false;
	}

	function findWrappedPOpen(token:TokenTree, limit:TokenTree):Bool {
		if (token.children == null) {
			return false;
		}
		for (child in token.children) {
			if (child.index >= limit.index) {
				return false;
			}
			switch (child.tok) {
				case POpen:
					if (isNewLineAfter(child)) {
						return true;
					}
				default:
			}
			if (findWrappedPOpen(child, limit)) {
				return true;
			}
		}
		return false;
	}

	function findTernaryQuestionTokens():Array<TokenTree> {
		return parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case Question:
					if (token.hasChildren()) {
						for (child in token.children) {
							if (child.tok.match(DblDot)) {
								return FoundGoDeeper;
							}
						}
					}
				default:
			}
			return GoDeeper;
		});
	}

	function markTernaryChaining() {
		var ternaryTokens:Array<TokenTree> = findTernaryQuestionTokens();
		for (question in ternaryTokens) {
			markSingleTernaryChain(question);
		}
	}

	function markSingleTernaryChain(question:TokenTree) {
		if (question.children == null) {
			return;
		}
		var dblDot:Null<TokenTree> = null;
		for (child in question.children) {
			if (child.tok.match(DblDot)) {
				dblDot = child;
				break;
			}
		}
		if (dblDot == null) {
			return;
		}
		// Walk up to find the expression start (past operators, back to statement level)
		var condToken:TokenTree = question.parent;
		if (condToken == null) {
			return;
		}
		while (condToken.parent != null) {
			switch (condToken.parent.tok) {
				case Binop(_), Unop(_), Const(_), Kwd(KwdNull), Kwd(KwdTrue), Kwd(KwdFalse), Dot, QuestionDot:
					condToken = condToken.parent;
				default:
					break;
			}
		}
		var items:Array<WrappableItem> = [];
		items.push(makeWrappableItem(condToken, question));
		var next:Null<TokenInfo> = getNextToken(question);
		if (next != null) {
			items.push(makeWrappableItem(next.token, dblDot));
		}
		var rule:WrapRule = determineWrapType2(config.wrapping.ternaryExpression, condToken, items);
		if (rule.type != NoWrap && rule.type != Keep) {
			ternaryWraps.push({itemStart: condToken, question: question, dblDot: dblDot});
		}
	}

	/** Post-queue pass: detect ternaries missed by markSingleTernaryChain because
	 *  operator breaks (opBool/opAdd) placed by the wrapping queue shortened the line,
	 *  making determineWrapType2 see a shorter line and skip detection. */
	function lateDetectTernaries() {
		var ternaryTokens:Array<TokenTree> = findTernaryQuestionTokens();
		for (question in ternaryTokens) {
			// Skip if already detected
			var alreadyDetected:Bool = false;
			for (wrap in ternaryWraps) {
				if (wrap.question == question) {
					alreadyDetected = true;
					break;
				}
			}
			if (alreadyDetected) continue;
			// Find dblDot
			if (question.children == null) continue;
			var dblDot:Null<TokenTree> = null;
			for (child in question.children) {
				if (child.tok.match(DblDot)) {
					dblDot = child;
					break;
				}
			}
			if (dblDot == null) continue;
			var lastToken:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(dblDot);
			if (lastToken == null) continue;
			// Walk up to find condToken (same as markSingleTernaryChain)
			var condToken:TokenTree = question.parent;
			if (condToken == null) continue;
			while (condToken.parent != null) {
				switch (condToken.parent.tok) {
					case Binop(_), Unop(_), Const(_), Kwd(KwdNull), Kwd(KwdTrue), Kwd(KwdFalse), Dot, QuestionDot:
						condToken = condToken.parent;
					default:
						break;
				}
			}
			// Check: does the full expression (ignoring breaks) exceed maxLineLength?
			// calcLineLength may be shortened by operator breaks — compare with span.
			var lineLen:Int = calcLineLength(condToken);
			var spanWithPrefix:Int = calcLineLengthBefore(condToken) + calcSpanLength(condToken, lastToken)
				+ indenter.calcAbsoluteIndent(indenter.calcIndent(condToken));
			if (spanWithPrefix <= config.wrapping.maxLineLength) continue;
			// Temporarily remove ALL breaks in the ternary to get true line length
			// Start from the line beginning (walk back to find tokens before condToken on same line)
			var startIdx:Int = condToken.index - 1;
			while (startIdx >= 0) {
				var info:Null<TokenInfo> = parsedCode.tokenList.tokens[startIdx];
				if (info != null && info.whitespaceAfter == Newline) break;
				startIdx--;
			}
			startIdx = Std.int(Math.max(0, startIdx + 1));
			var saved = saveAndRemoveBreaks(startIdx, lastToken.index);
			lineLen = calcLineLength(condToken);
			restoreBreaks(saved);
			if (lineLen > config.wrapping.maxLineLength) {
				ternaryWraps.push({itemStart: condToken, question: question, dblDot: dblDot});
			}
		}
	}

	function applyExpressionWrapping() {
		for (token in expressionWraps) {
			var pClose:Null<TokenTree> = getCloseToken(token);
			if (pClose == null) {
				continue;
			}
			// Re-check: if expression paren is inside a call that already wrapped,
			// the line is now shorter — skip expression wrapping if it fits.
			if (isInsideWrappedCall(token)) {
				var indent:Int = indenter.calcAbsoluteIndent(indenter.calcIndent(token));
				var span:Int = indent + calcLineLengthBefore(token) + calcSpanLength(token, pClose);
				if (span <= config.wrapping.maxLineLength) {
					continue;
				}
			}
			lineEndAfter(token);
			// Skip lineEndBefore(pClose) when content ends with a block —
			// `}))` should stay on one line, not become `}\n))`.
			if (!endsWithBrClose(pClose)) {
				lineEndBefore(pClose);
			}
			// If PClose is followed by another PClose with its own break
			// (from callParameter wrapping), merge them — keep `));` together.
			var nextAfterPClose:Null<TokenInfo> = getNextToken(pClose);
			if (nextAfterPClose != null && nextAfterPClose.token.tok.match(PClose) && isNewLineBefore(nextAfterPClose.token)) {
				noLineEndBefore(nextAfterPClose.token);
			}
			// Try to keep the first chunk of content on the POpen line:
			// `return (mediumBtn.selected` instead of `return (\n\tmediumBtn.selected`.
			// Only when POpen is NOT preceded by a binary operator — if the expression
			// paren is an operand in a larger expression (e.g. `title + (\n`), keep the
			// structural break for readability.
			var prevToken:Null<TokenInfo> = getPreviousToken(token);
			var prevIsBinop:Bool = prevToken != null && prevToken.token.tok.match(Binop(_));
			if (!prevIsBinop) {
				noLineEndAfter(token);
				if (calcLineLength(token) > config.wrapping.maxLineLength) {
					lineEndAfter(token); // doesn't fit — restore leading break
				}
			}
			// Remove PClose break when it's safe:
			// 1. Content is single-line — `(short_expr)` should not split `)`.
			// 2. Content is multiline but PClose is followed by `;` only —
			//    handles `(multiline_call : Type);` in switch cases.
			//    Do NOT remove for PClose/operators after `)` — the closing
			//    paren serves as a visual grouping boundary.
			if (isNewLineBefore(pClose)) {
				var canRemove:Bool = false;
				// Check 1: single-line content
				if (!isNewLineAfter(token)) {
					var hasInternalBreaks:Bool = false;
					var idx:Int = token.index + 1;
					var endIdx:Int = pClose.index - 1;
					while (idx < endIdx) {
						var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
						idx++;
						if (info != null && info.whitespaceAfter == Newline) {
							hasInternalBreaks = true;
							break;
						}
					}
					if (!hasInternalBreaks) canRemove = true;
				}
				// Check 2: no leading break, multiline, followed by `;`
				if (!canRemove && !isNewLineAfter(token)) {
					var nextAfterClose:Null<TokenInfo> = getNextToken(pClose);
					if (nextAfterClose != null && nextAfterClose.token.tok.match(Semicolon)) {
						canRemove = true;
					}
				}
				if (canRemove) {
					noLineEndBefore(pClose);
					if (calcLineLength(pClose) > config.wrapping.maxLineLength) {
						lineEndBefore(pClose); // doesn't fit — restore
					}
				}
			}
			// If POpen was moved to its own line by outer wrapping (e.g. opBoolChain),
			// try to merge it back to the end of the previous line: `... || (\n` style.
			if (isNewLineBefore(token)) {
				noLineEndBefore(token);
				if (calcLineLength(token) > config.wrapping.maxLineLength) {
					lineEndBefore(token); // doesn't fit — restore
				}
			}
			// Collapse opAdd/opSub chain breaks inside the wrapped parens — expression wrapping handles the content.
			collapseInnerChainBreaks(token, pClose);
			// Try to collapse opAdd/opSub breaks around this expression paren.
			// After expression wrapping, lines before ( and after ) may be short enough to fit.
			var prev:Null<TokenInfo> = getPreviousToken(token);
			if (prev != null) {
				switch (prev.token.tok) {
					case Binop(OpAdd), Binop(OpSub):
						tryCollapseBreakBefore(prev.token);
					default:
				}
			}
			// Collapse opAdd/opSub breaks on the line(s) after PClose
			collapseChainBreaksAfter(pClose);
		}
	}

	/** Check if token is inside a wrapped arrow function or wrapped call. */
	function isInsideWrappedArrowOrCall(token:TokenTree):Bool {
		// Check for arrow break before this token's line
		var idx:Int = token.index - 1;
		while (idx >= 0) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx--;
			if (info == null) continue;
			if (info.whitespaceAfter == Newline) {
				switch (info.token.tok) {
					case Binop(OpArrow), Arrow:
						return true;
					default:
				}
				break;
			}
		}
		return isInsideWrappedCall(token);
	}

	/** Check if token is inside a callParameter POpen that has Newline after it (already wrapped). */
	function isInsideWrappedCall(token:TokenTree):Bool {
		var parent:TokenTree = token.parent;
		while (parent != null && parent.tok != Root) {
			switch (parent.tok) {
				case POpen:
					if (TokenTreeCheckUtils.getPOpenType(parent) == Call && isNewLineAfter(parent)) return true;
				default:
			}
			parent = parent.parent;
		}
		return false;
	}

	/** Post-queue: re-evaluate methodChain entries that wrapped OnePerLine/AfterFirst
	 *  because callParameter wrapping has since shortened line lengths.
	 *  Strips method chain breaks, re-applies with current measurements.
	 */
	function reEvaluateMethodChainAfterCallParam() {
		for (place in wrappingQueue) {
			if (place.origin != MethodChainWrapping) continue;
			if (place.start == null || place.items == null || place.items.length <= 0) continue;
			var startIdx:Int = getPlaceStartIndex(place);
			var endIdx:Int = getPlaceEndIndex(place);
			// Skip if no inner callParameter breaks — nothing changed since evaluation
			if (!hasCallParamBreaksInChain(startIdx, endIdx)) continue;
			// Skip if no method chain breaks — chain wasn't wrapped
			if (!hasMethodChainBreaks(startIdx, endIdx)) continue;
			// Strip method chain breaks (Dot-after-PClose), keep callParameter breaks
			stripMethodChainBreaks(startIdx, endIdx);
			// Re-apply wrapping with current line lengths
			applyWrappingPlace(place);
		}
	}

	/** Check if there are callParameter breaks (newline after POpen) between indices. */
	function hasCallParamBreaksInChain(startIdx:Int, endIdx:Int):Bool {
		var idx:Int = startIdx;
		while (idx <= endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			if (info.token.tok.match(POpen) && TokenTreeCheckUtils.getPOpenType(info.token) == Call) {
				if (isNewLineAfter(info.token)) return true;
			}
		}
		return false;
	}

	/** Check if there are method chain breaks (newline before Dot-after-PClose). */
	function hasMethodChainBreaks(startIdx:Int, endIdx:Int):Bool {
		var idx:Int = startIdx;
		while (idx <= endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			if (info.token.tok.match(Dot) && isNewLineBefore(info.token) && isDotAfterPClose(info.token)) {
				return true;
			}
		}
		return false;
	}

	/** Remove method chain breaks (before Dot-after-PClose) but keep callParameter breaks. */
	function stripMethodChainBreaks(startIdx:Int, endIdx:Int) {
		var idx:Int = startIdx;
		while (idx <= endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			if (info.token.tok.match(Dot) && isNewLineBefore(info.token) && isDotAfterPClose(info.token)) {
				noLineEndBefore(info.token);
			}
		}
	}

	/** Collapse every break (hard Newline and soft wrapAfter) strictly inside
	 *  the token index range — including nested paren/bracket pairs that
	 *  `noWrappingBetween` deliberately skips. */
	function stripBreaksBetween(startIdx:Int, endIdx:Int) {
		var idx:Int = startIdx;
		while (idx < endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			info.wrapAfter = false;
			if (info.whitespaceAfter == Newline) noLineEndAfter(info.token);
		}
	}

	/**
	 * Post-queue: for callParameter entries inside a method chain whose line
	 *  exceeds maxLineLength, apply callParameter wrapping. Method chain wrapping
	 *  runs first and may break `.method(longArg)` via chain Dot, hiding the
	 *  overflow from callParameter. This produces `.concat(\n\targ\n)` instead
	 *  of `.concat(arg\n.chainedCall(...))`.
	 *  Also fires when the opening line fits but the arg itself has internal
	 *  method-chain breaks (multi-line arg) — keeps the call paren consistent
	 *  with the arg's own wrapping instead of nesting the chain under the call.
	 */
	function wrapLongCallParamsInChains() {
		for (place in wrappingQueue) {
			if (place.origin != CallParameterWrapping) continue;
			if (place.start == null) continue;
			// Skip if callParameter already has breaks
			if (isNewLineAfter(place.start)) continue;
			// Only act on calls in method chains: .methodName( pattern
			var prev:Null<TokenInfo> = getPreviousToken(place.start);
			if (prev == null || !prev.token.isCIdent()) continue;
			var prevPrev:Null<TokenInfo> = getPreviousToken(prev.token);
			if (prevPrev == null || !prevPrev.token.tok.match(Dot)) continue;
			// Only when the Dot is after PClose (chained call)
			if (!isDotAfterPClose(prevPrev.token)) continue;
			var pClose:Null<TokenTree> = place.end;
			if (pClose == null) pClose = getCloseToken(place.start);
			if (pClose == null) continue;
			var wrapAfterFit:Bool = false;
			if (calcLineLength(place.start) <= config.wrapping.maxLineLength) {
				// Line fits packed. Only wrap if arg has internal chain breaks
				// AND the call lives inside a wrapped ternary branch — keeps the
				// branch's layered chain consistent (`?`/`:` on own lines + arg
				// of nested call on own line) without changing non-ternary cases.
				if (!hasMethodChainBreaks(place.start.index, pClose.index)) continue;
				if (!isInsideWrappedTernaryBranch(place.start)) continue;
				wrapAfterFit = true;
			}
			// Apply callParameter wrapping
			lineEndAfter(place.start);
			lineEndBefore(pClose);
			if (wrapAfterFit) {
				// Chain breaks inside the arg were placed earlier on a shorter
				// indent (before fillLineWithLeadingBreak gave the arg its own
				// line). With the arg's new deeper indent the chain may now fit
				// — collapse breaks left-to-right where the joined line still
				// fits, restore otherwise.
				collapseMethodChainBreaksInRange(place.start.index, pClose.index);
			}
		}
	}

	/** Walk Dot-after-PClose tokens in [startIdx, endIdx], remove each
	 *  leading break if the merged line still fits; restore otherwise. */
	function collapseMethodChainBreaksInRange(startIdx:Int, endIdx:Int) {
		var idx:Int = startIdx;
		while (idx < endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			if (!info.token.tok.match(Dot)) continue;
			if (!isNewLineBefore(info.token)) continue;
			if (!isDotAfterPClose(info.token)) continue;
			noLineEndBefore(info.token);
			if (calcLineLength(info.token) > config.wrapping.maxLineLength) {
				lineEndBefore(info.token);
			}
		}
	}

	/** True when token sits inside a wrapped ternary's branch range (between
	 *  `?` and the end of the false branch). Only counts ternaries whose `?`
	 *  has a leading break (actually wrapped). */
	function isInsideWrappedTernaryBranch(token:TokenTree):Bool {
		for (wrap in ternaryWraps) {
			if (!isNewLineBefore(wrap.question)) continue;
			var end:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(wrap.dblDot);
			if (end == null) continue;
			if (token.index > wrap.question.index && token.index < end.index) {
				return true;
			}
		}
		return false;
	}

	function breakLongMethodChains() {
		parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case Dot:
					if (calcLineLength(token) > config.wrapping.maxLineLength && isDotAfterPClose(token) && !isNewLineBefore(token)) {
						lineEndBefore(token);
					}
				default:
			}
			return GoDeeper;
		});
	}

	/** True when a MethodChainWrapping queue place anchored strictly inside the
	 *  range resolved to an actual wrapping rule (onePerLine etc.). Such a chain
	 *  is intentionally multi-line by config — collapsing it would defeat that.
	 *  A place that resolved NoWrap/Keep means the only break came from the
	 *  `breakLongMethodChains` overflow fallback, which is the case to fix. */
	function hasWrappedMethodChainInside(startIdx:Int, endIdx:Int):Bool {
		for (place in wrappingQueue) {
			if (place.origin != MethodChainWrapping) continue;
			if (place.start == null || place.items == null) continue;
			var psi:Int = getPlaceStartIndex(place);
			if (psi <= startIdx || psi >= endIdx) continue;
			var rule:WrapRule = determineWrapType2(place.rules, place.start, place.items);
			switch (rule.type) {
				case NoWrap, Keep:
				case _:
					return true;
			}
		}
		return false;
	}

	/**
	 * Post-queue: when a method chain is the sole argument of a call and
	 *  `breakLongMethodChains` split it at a chained `.method(` (because
	 *  callParameter NoWrap'd the single arg and the line overflowed), prefer
	 *  wrapping the call's parentheses and keeping the chain on one line —
	 *  provided the opening line and the collapsed-chain line then both fit.
	 *  Mirrors the opSub single-arg fallback in `applyWrappingPlace`
	 *  (OpAddChainWrapping case); the method chain has no queue-driven
	 *  analogue, so this acts on the materialized break and falls back to it
	 *  when paren wrapping would not fit. Gated by the actual chain break, so
	 *  it is idempotent (no break left once collapsed and paren-wrapped).
	 */
	function preferParenWrapOverSingleArgChainBreak() {
		var maxLen:Int = config.wrapping.maxLineLength;
		for (place in wrappingQueue) {
			if (place.origin != CallParameterWrapping) continue;
			if (place.start == null || place.items == null || place.items.length != 1) continue;
			// Skip calls that already wrapped their parens — reEvaluateSingleArgCallParam owns that case.
			if (isNewLineAfter(place.start)) continue;
			// Skip chained-call links (`).method(`): the enclosing method chain
			//  governs their wrapping (wrapLongCallParamsInChains), not single-arg
			//  paren wrapping. The bug case is a plain `Ident.method(` call.
			var callPrev:Null<TokenInfo> = getPreviousToken(place.start);
			if (callPrev != null && callPrev.token.isCIdent()) {
				var callPrevPrev:Null<TokenInfo> = getPreviousToken(callPrev.token);
				if (callPrevPrev != null && callPrevPrev.token.tok.match(Dot) && isDotAfterPClose(callPrevPrev.token)) continue;
			}
			var pClose:Null<TokenTree> = place.end;
			if (pClose == null) pClose = getCloseToken(place.start);
			if (pClose == null) continue;
			var startIdx:Int = place.start.index;
			var endIdx:Int = pClose.index;
			if (!hasMethodChainBreaks(startIdx, endIdx)) continue;
			// Only the breakLongMethodChains overflow fallback (no queue-driven
			//  MethodChainWrapping place for the inner chain). When the chain has
			//  its own queued wrapping decision (e.g. onePerLine), that is the
			//  authority — collapsing it would defeat intentional chain wrapping.
			if (hasWrappedMethodChainInside(startIdx, endIdx)) continue;
			var lineStart:Null<TokenTree> = findLineStartToken(place.start);
			if (lineStart == null) continue;
			var firstContent:Null<TokenInfo> = getNextToken(place.start);
			var lastContent:Null<TokenInfo> = getPreviousToken(pClose);
			if (firstContent == null || lastContent == null) continue;
			var indent:Int = calcLineLengthBefore(lineStart);
			// Opening line kept up to and including the call's `(`.
			var headLen:Int = indent + calcSpanLength(lineStart, place.start);
			// Chain on its own line, one level deeper, collapsed back onto one line.
			var contLen:Int = indent + config.indentation.tabWidth + calcSpanLength(firstContent.token, lastContent.token);
			if (headLen > maxLen || contLen > maxLen) continue;
			stripMethodChainBreaks(startIdx, endIdx);
			lineEndAfter(place.start);
			lineEndBefore(pClose);
		}
	}

	/**
	 * Post-`breakLongMethodChains`: sibling of `preferParenWrapOverSingleArgChainBreak`.
	 *  When a detected ternary was NOT wrapped (its collapse check was fooled by a
	 *  queue break shortening the first physical line) and a branch contains a
	 *  method-chain break (overflow fallback), prefer wrapping the ternary. If both
	 *  branches then fit on one line, also strip the chain breaks for a clean look;
	 *  otherwise keep them so the branches remain readable. Acts on the materialized
	 *  chain break; idempotent (gate is the break itself — once the ternary is wrapped,
	 *  any remaining chain breaks live inside an already-wrapped branch).
	 */
	function preferTernaryWrapOverBranchChainBreak() {
		var maxLen:Int = config.wrapping.maxLineLength;
		for (wrap in ternaryWraps) {
			// Already wrapped — nothing to recover.
			if (isNewLineBefore(wrap.question)) continue;
			var dblDotEnd:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(wrap.dblDot);
			if (dblDotEnd == null) continue;
			if (!hasMethodChainBreaks(wrap.question.index, dblDotEnd.index)) continue;
			var lineStart:Null<TokenTree> = findLineStartToken(wrap.itemStart);
			if (lineStart == null) continue;
			var condEnd:Null<TokenInfo> = getPreviousToken(wrap.question);
			var trueEnd:Null<TokenInfo> = getPreviousToken(wrap.dblDot);
			if (condEnd == null || trueEnd == null) continue;
			var indent:Int = calcLineLengthBefore(lineStart);
			// `?`/`:` continuation sits one level deeper than the statement.
			var branchIndent:Int = indent + config.indentation.tabWidth;
			var condLen:Int = indent + calcSpanLength(lineStart, condEnd.token);
			var trueLen:Int = branchIndent + calcSpanLength(wrap.question, trueEnd.token);
			var falseLen:Int = branchIndent + calcSpanLength(wrap.dblDot, dblDotEnd);
			if (condLen > maxLen) continue;
			// Both branches fit on one line — strip chain breaks for clean look.
			// Otherwise keep chain breaks (branches still need them).
			if (trueLen <= maxLen && falseLen <= maxLen) {
				stripMethodChainBreaks(wrap.question.index, dblDotEnd.index);
			}
			lineEndBefore(wrap.question);
			lineEndBefore(wrap.dblDot);
		}
	}

	/** A nested `FunctionSignatureWrapping` place (a Haxe-4 function-TYPE
	 *  parameter list `(a:T, b:U)->V`, classified `Parameter` by
	 *  `getPOpenType` because of the trailing `->`) that materialized a
	 *  leading break inside the given range — the symptom of the enclosing
	 *  signature being left unwrapped. Gated on the fact (`isNewLineAfter`
	 *  the inner `(`), not on a re-predicted rule. */
	function hasWrappedInnerSignature(startIdx:Int, endIdx:Int):Bool {
		for (place in wrappingQueue) {
			if (place.origin != FunctionSignatureWrapping) continue;
			if (place.start == null) continue;
			var psi:Int = place.start.index;
			if (psi <= startIdx || psi >= endIdx) continue;
			if (isNewLineAfter(place.start)) return true;
		}
		return false;
	}

	/**
	 * Post-queue sibling of `preferParenWrapOverSingleArgChainBreak`.
	 *  A Haxe-4 function-TYPE parameter list (`(a:T, b:U)->V`) is classified
	 *  as `Parameter` by `getPOpenType` (trailing `->`), so it is queued as
	 *  its own `FunctionSignatureWrapping` place. When the enclosing real
	 *  signature has a single overflowing parameter, the configured
	 *  `itemCount <= 1 -> noWrap` rule keeps it on one line; the still too
	 *  long line is then absorbed by wrapping the inner func-type paren,
	 *  splitting the type instead of the parameter. Prefer breaking the lone
	 *  parameter onto its own line (fillLineWithLeadingBreak) and collapsing
	 *  the inner func-type paren — provided the head, parameter and closing
	 *  lines then fit. Acts on the materialized inner break; idempotent (the
	 *  gate is the still-collapsed single-param signature whose one-line span
	 *  exceeds maxLineLength, measured break-agnostically via calcSpanLength,
	 *  plus a still-wrapped inner func-type paren — both false once the lone
	 *  param sits on its own line and the inner paren has collapsed).
	 */
	function preferFunctionSignatureWrapOverInnerParen() {
		var maxLen:Int = config.wrapping.maxLineLength;
		for (place in wrappingQueue) {
			if (place.origin != FunctionSignatureWrapping) continue;
			if (place.start == null || place.items == null || place.items.length != 1) continue;
			// Already broke the lone param onto its own line — nothing to do.
			if (isNewLineAfter(place.start)) continue;
			var pClose:Null<TokenTree> = place.end;
			if (pClose == null) pClose = getCloseToken(place.start);
			if (pClose == null) continue;
			// Recover only from the materialized symptom: a nested func-type
			//  paren that actually wrapped. Without it the lone-param noWrap
			//  decision stands (there is no inner split to undo).
			if (!hasWrappedInnerSignature(place.start.index, pClose.index)) continue;
			var lineStart:Null<TokenTree> = findLineStartToken(place.start);
			if (lineStart == null) continue;
			// End of the signature line: the function body `{` after `)`.
			var bodyOpen:Null<TokenTree> = pClose;
			var walk:Null<TokenInfo> = getNextToken(pClose);
			while (walk != null) {
				switch (walk.token.tok) {
					case BrOpen:
						bodyOpen = walk.token;
					case Semicolon:
						// Bodyless decl (interface/abstract/extern) — line ends at `;`.
						bodyOpen = walk.token;
					default:
						walk = getNextToken(walk.token);
						continue;
				}
				break;
			}
			var item:WrappableItem = place.items[0];
			var indent:Int = calcLineLengthBefore(lineStart);
			// Whole signature collapsed onto one line — the decision gate.
			var fullLen:Int = indent + calcSpanLength(lineStart, bodyOpen);
			if (fullLen <= maxLen) continue;
			// Opening line kept up to and including the signature `(`.
			var headLen:Int = indent + calcSpanLength(lineStart, place.start);
			// Lone parameter on its own line, one level deeper, collapsed.
			var paramLen:Int = indent + config.indentation.tabWidth + calcSpanLength(item.first, item.last);
			// Closing `)` + return type + `{` back at the signature indent.
			var closeLen:Int = indent + calcSpanLength(pClose, bodyOpen);
			if (headLen > maxLen || paramLen > maxLen || closeLen > maxLen) continue;
			stripBreaksBetween(place.start.index, pClose.index);
			wrapFillLineWithLeading2AfterLast(place.start, pClose, place.items, maxLen, 0);
		}
	}

	/** After conditionWrapping/opBoolChain, an individual `&&`/`||` operand can
	 *  still exceed maxLineLength when the operand itself contains a long
	 *  equality comparison (e.g. `a?.b == 'very long string literal'`).
	 *  opBoolChain only breaks between operands, never inside one — so split
	 *  such an operand before its top-level `==`/`!=`. The token tree already
	 *  nests the comparison one level under the operand, so the indenter
	 *  produces the continuation indent without an additionalIndent marker. */
	function breakLongOpBoolOperandAtCompare() {
		parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case Binop(OpEq), Binop(OpNotEq):
					if (isNewLineBefore(token)) {
						return GoDeeper;
					}
					if (!isInsideConditionWrap(token)) {
						return GoDeeper;
					}
					if (calcLineLength(token) <= config.wrapping.maxLineLength) {
						return GoDeeper;
					}
					lineEndBefore(token);
				default:
			}
			return GoDeeper;
		});
	}

	/** Check if there are any line breaks before operator tokens (opAdd/opSub/opBool) in the given range. */
	function hasOperatorBreaks(open:TokenTree, close:TokenTree):Bool {
		var idx:Int = open.index + 1;
		while (idx < close.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Binop(OpAdd), Binop(OpSub), Binop(OpBoolAnd), Binop(OpBoolOr):
					if (isNewLineBefore(info.token)) return true;
				default:
			}
		}
		return false;
	}

	/** Collapse opAdd chain breaks in a ternary branch, then re-evaluate opAddSubChain rules.
	 *  If the rules still require wrapping, restore the breaks. */
	function collapseTernaryBranchOpAdd(branchStart:TokenTree, branchEnd:TokenTree) {
		// Save and remove all opAdd-related breaks
		var savedBreaks:Array<{idx:Int, ws:formatter.codedata.WhitespaceAfterType}> = [];
		var opAddTokens:Array<TokenTree> = [];
		var idx:Int = branchStart.index + 1;
		while (idx < branchEnd.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Binop(OpAdd), Binop(OpSub):
					opAddTokens.push(info.token);
					var prevInfo:Null<TokenInfo> = getPreviousToken(info.token);
					if (prevInfo != null && prevInfo.whitespaceAfter == Newline) {
						savedBreaks.push({idx: prevInfo.token.index, ws: Newline});
						prevInfo.whitespaceAfter = if (prevInfo.spacesAfter <= 0) None else Space;
					}
				default:
			}
		}
		if (savedBreaks.length == 0) return;
		// Re-evaluate opAddSubChain rules with the branch-level line length
		if (opAddTokens.length > 0) {
			// Build items for the opAdd chain in the branch
			var items:Array<WrappableItem> = [];
			var itemStart:TokenTree = branchStart;
			for (opTok in opAddTokens) {
				items.push(makeWrappableItem(itemStart, opTok));
				var next:Null<TokenInfo> = getNextToken(opTok);
				if (next != null) itemStart = next.token;
			}
			items.push(makeWrappableItem(itemStart, branchEnd));
			var rule:WrapRule = determineWrapType2(config.wrapping.opAddSubChain, branchStart, items);
			if (rule.type != NoWrap && rule.type != Keep) {
				// Rules still require wrapping — restore breaks
				restoreBreaks(savedBreaks);
				// Set additionalIndent on continuation tokens (after the break) so
				// they are indented one level deeper than the branch start (? or :).
				for (opTok in opAddTokens) {
					var prevInfo:Null<TokenInfo> = getPreviousToken(opTok);
					if (prevInfo != null && prevInfo.whitespaceAfter == Newline) {
						additionalIndent(opTok, 1);
					}
				}
			}
		}
	}

	/** Re-add opAdd/opSub breaks in a ternary branch if the branch line exceeds maxLineLength.
	 *  Sets additionalIndent(1) on the operator for proper continuation indent. */
	function reAddOpAddBreaksInTernaryBranch(branchStart:TokenTree, branchEnd:TokenTree) {
		// Check if branch line exceeds maxLineLength
		if (calcLineLength(branchStart) <= config.wrapping.maxLineLength) return;
		// Check if there are already opAdd breaks — if so, nothing to do
		if (hasOperatorBreaks(branchStart, branchEnd)) return;
		// Find opAdd operators and add breaks from last to first
		var opAddTokens:Array<TokenTree> = [];
		var idx:Int = branchStart.index + 1;
		while (idx < branchEnd.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Binop(OpAdd), Binop(OpSub):
					opAddTokens.push(info.token);
				default:
			}
		}
		// Add breaks after operators (from last to first) until the line fits.
		// The continuation token (after the operator) gets additionalIndent(1).
		var i:Int = opAddTokens.length - 1;
		while (i >= 0) {
			var opTok:TokenTree = opAddTokens[i];
			i--;
			var next:Null<TokenInfo> = getNextToken(opTok);
			if (next == null) continue;
			lineEndBefore(next.token);
			additionalIndent(next.token, 1);
			if (calcLineLength(branchStart) <= config.wrapping.maxLineLength) break;
		}
	}

	function collapseInnerChainBreaks(open:TokenTree, close:TokenTree) {
		var idx:Int = open.index + 1;
		while (idx < close.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Binop(OpAdd), Binop(OpSub):
					if (isNewLineBefore(info.token)) noLineEndBefore(info.token);
					if (info.whitespaceAfter == Newline) noLineEndAfter(info.token);
				default:
			}
		}
	}

	/** Walk forward from token, collapsing opAdd/opSub breaks that now fit after expression wrapping. */
	function collapseChainBreaksAfter(token:TokenTree) {
		var idx:Int = token.index + 1;
		var limit:Int = Std.int(Math.min(idx + 20, parsedCode.tokenList.tokens.length));
		while (idx < limit) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Binop(OpAdd), Binop(OpSub):
					tryCollapseBreakBefore(info.token);
					var next:Null<TokenInfo> = getNextToken(info.token);
					if (next != null) tryCollapseBreakBefore(next.token);
				case Semicolon:
					return;
				default:
			}
		}
	}

	function collapseChainWraps() {
		parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case Binop(OpBoolAnd), Binop(OpBoolOr), Binop(OpAdd), Binop(OpSub):
					if (isInsideConditionWrap(token)) {
						if (shouldPreserveChainBreak(token)) {
							return GoDeeper;
						}
						tryCollapseBreakBefore(token);
						var next:Null<TokenInfo> = getNextToken(token);
						if (next != null) {
							tryCollapseBreakBefore(next.token);
						}
					}
				default:
			}
			return GoDeeper;
		});
	}

	/** Condition has arrow breaks AND full span exceeds maxLineLength. */
	function shouldPreserveChainBreak(token:TokenTree):Bool {
		for (open in conditionWraps) {
			var close:Null<TokenTree> = getCloseToken(open);
			if (close == null) continue;
			if (token.index <= open.index || token.index >= close.index) continue;
			if (!hasInnerArrowBreak(open, close)) continue;
			var condIndent:Int = indenter.calcAbsoluteIndent(indenter.calcIndent(open) + 1);
			if (condIndent + calcSpanLength(open, close) > config.wrapping.maxLineLength) {
				return true;
			}
		}
		return false;
	}

	/** Remove line break before token only if the combined line would still fit. */
	function tryCollapseBreakBefore(token:TokenTree) {
		if (!isNewLineBefore(token)) {
			return;
		}
		// Temporarily remove break to measure combined line length
		noLineEndBefore(token);
		if (calcLineLength(token) <= config.wrapping.maxLineLength) {
			return; // fits — keep collapsed
		}
		// Doesn't fit — restore break
		lineEndBefore(token);
	}

	/** Check if token is between an applied condition wrapping POpen and its PClose. */
	function isInsideConditionWrap(token:TokenTree):Bool {
		for (open in conditionWraps) {
			if (!isNewLineAfter(open)) continue;
			if (token.index <= open.index) continue;
			var close:Null<TokenTree> = getCloseToken(open);
			if (close != null && token.index < close.index) return true;
		}
		return false;
	}

	function applyTernaryWrapping() {
		for (wrap in ternaryWraps) {
			lineEndBefore(wrap.question);
			lineEndBefore(wrap.dblDot);
			var dblDotEnd:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(wrap.dblDot);
			resolveSoftWraps(wrap.itemStart);
			unwrapIfFits(wrap.itemStart, wrap.question);
			wrapBoolOpsIfMultiline(wrap.itemStart, wrap.question);
			unwrapTernaryBranchCalls(wrap.itemStart);
			unwrapTernaryBranchCalls(wrap.question);
			unwrapTernaryBranchCalls(wrap.dblDot);
			// If entire ternary fits on one line after unwrapping, try collapse
			noLineEndBefore(wrap.question);
			noLineEndBefore(wrap.dblDot);
			var needsWrap:Bool = false;
			var exprWrapParen:Null<TokenTree> = findEnclosingExpressionWrap(wrap.itemStart);
			// Only when the paren is preceded by a binary operator does
			// applyExpressionWrapping keep its leading break (see prevIsBinop
			// there) — that isolates the ternary on its own line. When it is
			// preceded by `return`/`=`/etc. the first chunk stays on the paren's
			// line, so the ternary is not isolated and the standard line-length
			// path applies.
			var exprWrapIsolatesTernary:Bool = false;
			if (exprWrapParen != null) {
				var beforeParen:Null<TokenInfo> = getPreviousToken(exprWrapParen);
				exprWrapIsolatesTernary = beforeParen != null && beforeParen.token.tok.match(Binop(_));
			}
			if (exprWrapIsolatesTernary && dblDotEnd != null) {
				// The enclosing expression paren is queued to wrap (decision
				// already recorded in expressionWraps — applyExpressionWrapping
				// runs after this and will move `… + (` to the previous line
				// and `)` to the next). calcLineLength / calcLineLengthBefore
				// still see the un-wrapped full line and over-count that prefix
				// and suffix. Measure the ternary at its post-wrap indent
				// instead: paren content sits one level deeper than the paren.
				var effIndent:Int = indenter.calcAbsoluteIndent(indenter.calcIndent(wrap.itemStart)) + indenter.calcAbsoluteIndent(1);
				if (effIndent + calcSpanLength(wrap.itemStart, dblDotEnd) > config.wrapping.maxLineLength) {
					needsWrap = true;
				}
			} else {
				if (calcLineLength(wrap.itemStart) > config.wrapping.maxLineLength) {
					needsWrap = true;
				} else if (dblDotEnd != null && hasCallParamBreaksBetweenTokens(wrap.itemStart, dblDotEnd)) {
					// calcLineLength shortened by callParameter breaks — check full span
					var indent:Int = indenter.calcAbsoluteIndent(indenter.calcIndent(wrap.itemStart));
					var span:Int = indent + calcLineLengthBefore(wrap.itemStart) + calcSpanLength(wrap.itemStart, dblDotEnd);
					if (span > config.wrapping.maxLineLength) {
						needsWrap = true;
					}
				}
				if (!needsWrap && dblDotEnd != null && hasOperatorBreaks(wrap.itemStart, dblDotEnd)) {
					// calcLineLength was shortened by operator breaks (opAdd/opBool)
					// within the ternary expression. Temporarily remove them to
					// get the true single-line length.
					var savedBreaks = saveAndRemoveBreaks(wrap.itemStart.index, dblDotEnd.index, tok -> switch (tok) {
						case Binop(OpAdd), Binop(OpSub), Binop(OpBoolAnd), Binop(OpBoolOr): true;
						default: false;
					});
					if (calcLineLength(wrap.itemStart) > config.wrapping.maxLineLength) {
						needsWrap = true;
					}
					// Restore operator breaks — they'll be re-evaluated per branch
					restoreBreaks(savedBreaks);
				}
			}
			if (needsWrap) {
				lineEndBefore(wrap.question);
				lineEndBefore(wrap.dblDot);
				// Re-evaluate opAdd breaks per branch — they may no longer be
				// needed now that each branch is on its own shorter line.
				if (dblDotEnd != null) {
					collapseTernaryBranchOpAdd(wrap.question, wrap.dblDot);
					lineEndBefore(wrap.question);
					lineEndBefore(wrap.dblDot);
					collapseTernaryBranchOpAdd(wrap.dblDot, dblDotEnd);
				}
				// Re-add opAdd breaks with correct additionalIndent for branches
				// where unwrapTernaryBranchCalls removed them but the line still exceeds.
				reAddOpAddBreaksInTernaryBranch(wrap.question, wrap.dblDot);
				if (dblDotEnd != null) {
					reAddOpAddBreaksInTernaryBranch(wrap.dblDot, dblDotEnd);
				}
				// The condition's &&/|| breaks were placed by the queue /
				// wrapBoolOpsIfMultiline on the un-wrapped full line. Now the
				// condition sits on its own line (the ? / : are broken) — those
				// breaks may be unnecessary. Collapse them if the condition fits,
				// restore otherwise. The !needsWrap branch below does the same
				// unconditionally because the whole ternary fits there.
				var savedCondBreaks = saveAndRemoveBreaks(wrap.itemStart.index, wrap.question.index, tok -> switch (tok) {
					case Binop(OpBoolAnd), Binop(OpBoolOr): true;
					default: false;
				});
				if (savedCondBreaks.length > 0 && calcLineLength(wrap.itemStart) > config.wrapping.maxLineLength) {
					restoreBreaks(savedCondBreaks);
				}
			} else if (dblDotEnd != null && !hasLineBreaksBetween(wrap.question.index, dblDotEnd.index - 1)) {
				// Ternary fits on one line AND branches have no inner breaks —
				// undo wrapBoolOpsIfMultiline's && breaks in the condition.
				// Use dblDotEnd.index - 1 to exclude trailing callParameter break.
				unwrapBoolOpsBetween(wrap.itemStart.index, wrap.question.index);
			}
			// Clean up unnecessary comma wrapping inside calls — removes instability
			// where pass1 wraps a call (fillLine) but pass2 doesn't (shorter line).
			cleanupCallCommaWrapping(wrap.itemStart);
			cleanupCallCommaWrapping(wrap.question);
			cleanupCallCommaWrapping(wrap.dblDot);
		}
		// Second pass: apply additionalIndent for nested ternaries.
		// A ternary is nested if its ? token falls inside another wrapped ternary's range.
		// The Indenter already staircases the continuation indent in some structural
		// configurations (e.g. right-associative nesting where the inner ternary's ? is
		// deeper in the token tree) but keeps it flat in others. Adding `depth` blindly
		// double-counts the first case. Instead target an absolute indent of
		// rootBase + depth (rootBase = the outermost containing ternary's base indent)
		// and add only the delta the Indenter has not already supplied.
		for (wrap in ternaryWraps) {
			if (!isNewLineBefore(wrap.question)) continue; // not wrapped
			var depth:Int = 0;
			var rootWrap = wrap;
			for (outer in ternaryWraps) {
				if (outer == wrap) continue;
				if (!isNewLineBefore(outer.question)) continue; // outer not wrapped
				if (wrap.question.index > outer.question.index) {
					var outerEnd:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(outer.dblDot);
					if (outerEnd != null && wrap.question.index < outerEnd.index) {
						depth++;
						if (outer.question.index < rootWrap.question.index) rootWrap = outer;
					}
				}
			}
			if (depth > 0) {
				var add:Int = (indenter.calcIndent(rootWrap.question) + depth) - indenter.calcIndent(wrap.question);
				if (add > 0) {
					additionalIndent(wrap.question, add);
					additionalIndent(wrap.dblDot, add);
				}
			}
		}
	}

	/** Remove comma wrapping from calls that fit on one line in their current context. */
	function cleanupCallCommaWrapping(branchStart:TokenTree) {
		if (branchStart.children == null) return;
		for (child in branchStart.children) {
			switch (child.tok) {
				case POpen:
					var pClose:Null<TokenTree> = getCloseToken(child);
					if (pClose == null) continue;
					if (isSameLineBetween(child, pClose, false)) continue;
					// Try removing comma wrapping
					noWrappingBetween(child, pClose, false);
					if (calcLineLength(child) <= config.wrapping.maxLineLength) {
						// Fits — keep unwrapped
						noLineEndBefore(pClose);
					} else {
						// Doesn't fit — re-wrap using configured callParameter wrapping style
						var items:Array<WrappableItem> = makeWrappableItems(child);
						var rule:WrapRule = determineWrapType2(config.wrapping.callParameter, child, items);
						applyRule(CallParameterWrapping, rule, child, pClose, items, rule.additionalIndent, true);
					}
				default:
					cleanupCallCommaWrapping(child);
			}
		}
	}

	/**
	 * Resolve wrapAfter flags to hard Newline on the line containing the token.
	 * When the full line exceeds maxLineLength, resolve the first wrapAfter
	 * on the line — it's the highest-level operator producing the best split.
	 */
	function resolveSoftWraps(token:TokenTree) {
		if (calcLineLength(token) <= config.wrapping.maxLineLength) {
			return;
		}
		// Walk backward to line start, remembering the farthest wrapAfter
		var firstWrap:Null<TokenTree> = null;
		var idx:Int = token.index - 1;
		while (idx >= 0) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			if (info == null) {
				idx--;
				continue;
			}
			if (info.whitespaceAfter == Newline) {
				break;
			}
			if (info.wrapAfter) {
				firstWrap = info.token;
			}
			idx--;
		}
		if (firstWrap != null) {
			lineEndAfter(firstWrap);
		}
	}

	function unwrapIfFits(from:TokenTree, to:TokenTree) {
		if (isSameLineBetween(from, to, false)) {
			return;
		}
		unwrapBoolOps(from, to);
	}

	function unwrapBoolOps(token:TokenTree, limit:TokenTree) {
		if (token.children == null) {
			return;
		}
		for (child in token.children) {
			if (child.index >= limit.index) {
				return;
			}
			switch (child.tok) {
				case Binop(OpBoolAnd), Binop(OpBoolOr):
					// Don't collapse && inside multiline parenthesized expressions
					// (e.g. ternary with multiline branches)
					if (!isInsideMultilineParen(child)) {
						noLineEndBefore(child);
						var next:Null<TokenInfo> = getNextToken(child);
						if (next != null) {
							noLineEndBefore(next.token);
						}
					}
				default:
			}
			unwrapBoolOps(child, limit);
		}
	}

	/** Check if there are any Newline markers between two token indices. */
	function hasLineBreaksBetween(startIdx:Int, endIdx:Int):Bool {
		var idx:Int = startIdx;
		while (idx <= endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info != null && info.whitespaceAfter == Newline) return true;
		}
		return false;
	}

	/** Remove Newline before &&/|| tokens in the given index range. */
	function unwrapBoolOpsBetween(startIdx:Int, endIdx:Int) {
		var idx:Int = startIdx;
		while (idx <= endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case Binop(OpBoolAnd), Binop(OpBoolOr):
					noLineEndBefore(info.token);
				default:
			}
		}
	}

	/** Wrap &&/|| when enclosing POpen→PClose content is multiline. */
	function wrapBoolOpsIfMultiline(token:TokenTree, limit:TokenTree) {
		if (token.children == null) return;
		for (child in token.children) {
			if (child.index >= limit.index) return;
			switch (child.tok) {
				case Binop(OpBoolAnd), Binop(OpBoolOr):
					if (isInsideMultilineParen(child)) lineEndBefore(child);
				default:
			}
			wrapBoolOpsIfMultiline(child, limit);
		}
	}

	/**
	 * Check if the content of the enclosing POpen→PClose would need wrapping
	 * (total character count exceeds maxLineLength). This indicates the expression
	 * will be multiline regardless of the opBool wrapping decision.
	 */
	/**
	 * Innermost enclosing POpen that is queued for expression wrapping
	 * (present in expressionWraps), or null. Used by the ternary collapse
	 * check to measure the ternary at its post-expression-wrap indent.
	 */
	function findEnclosingExpressionWrap(token:TokenTree):Null<TokenTree> {
		var parent:TokenTree = token.parent;
		while (parent != null && parent.tok != Root) {
			if (parent.tok.match(POpen) && expressionWraps.indexOf(parent) >= 0) {
				return parent;
			}
			parent = parent.parent;
		}
		return null;
	}

	function isInsideMultilineParen(token:TokenTree):Bool {
		var parent:TokenTree = token.parent;
		while (parent != null && parent.tok != Root) {
			switch (parent.tok) {
				case POpen:
					var pClose:Null<TokenTree> = getCloseToken(parent);
					if (pClose == null) return false;
					// Measure total content length (as if all on one line)
					var totalLen:Int = 0;
					var idx:Int = parent.index;
					while (idx <= pClose.index) {
						var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
						if (info != null) totalLen += info.token.toString().length + 1; // +1 for space
						idx++;
					}
					return totalLen > config.wrapping.maxLineLength;
				default:
			}
			parent = parent.parent;
		}
		return false;
	}

	function unwrapAddOps(token:TokenTree, limit:TokenTree) {
		if (token.children == null) {
			return;
		}
		for (child in token.children) {
			if (child.index >= limit.index) {
				return;
			}
			switch (child.tok) {
				case Binop(OpAdd), Binop(OpSub):
					noLineEndBefore(child);
					var next:Null<TokenInfo> = getNextToken(child);
					if (next != null) {
						noLineEndBefore(next.token);
					}
				default:
			}
			unwrapAddOps(child, limit);
		}
	}

	function unwrapTernaryBranchCalls(branchStart:TokenTree) {
		if (branchStart.children == null) {
			return;
		}
		for (child in branchStart.children) {
			switch (child.tok) {
				case POpen:
					var pClose:Null<TokenTree> = getCloseToken(child);
					if (pClose == null) {
						continue;
					}
					if (isSameLineBetween(child, pClose, false)) {
						continue;
					}
					// Re-evaluate: remove existing wrapping first
					noWrappingBetween(child, pClose);
					var lineLen:Int = calcLineLength(child);
					if (lineLen <= config.wrapping.maxLineLength) {
						// Fits on one line now — keep unwrapped
						noLineEndBefore(pClose);
					} else {
						// Still too long — re-wrap with leading break
						var items:Array<WrappableItem> = makeWrappableItems(child);
						wrapFillLineWithLeading2AfterLast(child, pClose, items, config.wrapping.maxLineLength);
						lineEndBefore(pClose);
					}
				default:
					unwrapTernaryBranchCalls(child);
			}
		}
	}

	function markMethodChaining(startToken:Null<TokenTree>) {
		if (startToken == null) {
			return;
		}
		var chainStarts:Array<TokenTree> = startToken.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case Dot:
					var prev:TokenInfo = getPreviousToken(token);
					while (prev != null) {
						switch (prev.token.tok) {
							case Comment(_):
							case CommentLine(_):
							case PClose:
								wrapBefore(token, true);
								return FoundSkipSubtree;
							default:
								break;
						}
						prev = getPreviousToken(prev.token);
					}
				default:
			}
			return GoDeeper;
		});
		for (chainStart in chainStarts) {
			// Skip Dots that are direct children of a Block BrOpen with a preceding Sharp —
			// these are post-#end chain continuations handled by extendChainAcrossSharp.
			if (isPostSharpChainDot(chainStart)) continue;
			// look at additional chain starts below
			markInternalMethodChaining(chainStart);
			markSingleMethodChain(chainStart);
		}
	}

	function markInternalMethodChaining(startToken:TokenTree) {
		startToken.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case BkOpen, BrOpen, POpen:
					markMethodChaining(token);
				default:
			}
			return GoDeeper;
		});
	}

	function markSingleMethodChain(chainStart:TokenTree) {
		var chainedCalls:Array<TokenTree> = chainStart.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case Dot:
					return isDotAfterPClose(token) ? FoundGoDeeper : GoDeeper;
				case POpen, BrOpen, BkOpen:
					return SkipSubtree;
				case Sharp(MarkLineEnds.SHARP_IF):
					if (token.hasChildren()) {
						for (child in token.children) {
							if (child.matches(Dot)) {
								return FoundSkipSubtree;
							}
						}
					}
				default:
			}
			return GoDeeper;
		});

		var firstMethodCall:TokenTree = chainStart.access().parent().isCIdent().parent().matches(Dot).token;
		if (firstMethodCall != null) {
			chainedCalls.unshift(firstMethodCall);
			chainStart = firstMethodCall;
		}

		// Extend chain across #if/#end boundaries: when the chain's subtree ends
		// and the parent has Sharp(if)/Dot siblings after it, include them.
		extendChainAcrossSharp(chainStart, chainedCalls);

		var items:Array<WrappableItem> = [];
		// Use last chained call's subtree end if chain was extended across #if/#end
		var chainEnd:Null<TokenTree> = if (chainedCalls.length > 0) {
			TokenTreeCheckUtils.getLastToken(chainedCalls[chainedCalls.length - 1]);
		} else {
			TokenTreeCheckUtils.getLastToken(chainStart);
		}
		var info:TokenInfo = getPreviousToken(chainStart);
		var chainOpen:Null<TokenTree> = chainStart.parent;
		if (info != null) {
			chainOpen = info.token;
		}

		for (index in 0...chainedCalls.length) {
			var child:TokenTree = chainedCalls[index];
			var endToken:TokenTree = chainEnd;
			if (index + 1 < chainedCalls.length) {
				var next:TokenTree = chainedCalls[index + 1];
				info = getPreviousToken(next);
				if (info != null) {
					endToken = info.token;
				}
			}
			items.push(makeWrappableItem(child, endToken));
		}
		chainEnd = null;
		if (chainOpen != null) {
			chainEnd = getCloseToken(chainOpen);
		}
		queueWrapping({
			origin: MethodChainWrapping,
			start: chainOpen,
			end: chainEnd,
			items: items,
			rules: config.wrapping.methodChain,
			useTrailing: false,
			overrideAdditionalIndent: null
		}, "markSingleMethodChain");
	}

	/** Check if a Dot is preceded by PClose (skipping comments and Sharp(end)). */
	function isDotAfterPClose(dot:TokenTree):Bool {
		var prev:TokenInfo = getPreviousToken(dot);
		while (prev != null) {
			switch (prev.token.tok) {
				case Comment(_):
				case CommentLine(_):
				case PClose:
					return true;
				case Sharp(MarkLineEnds.SHARP_END):
				default:
					return false;
			}
			prev = getPreviousToken(prev.token);
		}
		return false;
	}

	/** Check if a Dot chain start is a post-#end continuation in a Block. */
	function isPostSharpChainDot(chainStart:TokenTree):Bool {
		// Walk up from chainStart to find the Dot that is a direct child of its parent scope
		var dot:TokenTree = chainStart;
		while (dot != null) {
			if (dot.parent != null && dot.parent.tok.match(BrOpen)) {
				if (TokenTreeCheckUtils.getBrOpenType(dot.parent) == Block) {
					// Check if there's a Sharp(end) before this dot in the parent's children
					var prev:Null<TokenInfo> = getPreviousToken(dot);
					while (prev != null) {
						switch (prev.token.tok) {
							case Sharp(MarkLineEnds.SHARP_END):
								return true;
							case Sharp(_), Dot, PClose, Const(_), Comment(_), CommentLine(_):
								prev = getPreviousToken(prev.token);
								continue;
							default:
								return false;
						}
					}
				}
				return false;
			}
			dot = dot.parent;
		}
		return false;
	}

	/**
	 * When #if/#end splits a method chain, post-#end Dots become siblings at
	 * the parent level instead of children in the chain subtree. Walk the parent's
	 * children after the chain end and collect Sharp(if) with Dot children and
	 * standalone Dots as additional chain elements.
	 */
	function extendChainAcrossSharp(chainStart:TokenTree, chainedCalls:Array<TokenTree>) {
		// Find the chain's last token index to know where to start scanning
		var lastChainToken:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(chainStart);
		if (lastChainToken == null) return;
		var lastIdx:Int = lastChainToken.index;

		// Walk up from chainStart to find the scope that contains Sharp siblings.
		// The chain subtree may be nested several levels deep (e.g. Return → s → Dot chain).
		// Sharp(if) and post-#end Dots are children of the enclosing block (BrOpen).
		var scope:Null<TokenTree> = chainStart.parent;
		while (scope != null && scope.tok != Root) {
			if (scope.children == null) {
				scope = scope.parent;
				continue;
			}
			// Check if the first sibling after our chain is Sharp(if) with a Dot child
			var hasSharpAfter:Bool = false;
			for (child in scope.children) {
				if (child.index <= lastIdx) continue;
				if (child.tok.match(Sharp(MarkLineEnds.SHARP_IF)) && child.hasChildren()) {
					for (c in child.children) {
						if (c.matches(Dot)) {
							hasSharpAfter = true;
							break;
						}
					}
				}
				break; // only check the first sibling after lastIdx
			}
			if (hasSharpAfter) break;
			scope = scope.parent;
		}
		if (scope == null || scope.children == null) return;

		// Scan siblings after the chain subtree
		var foundSharp:Bool = false;
		for (sibling in scope.children) {
			if (sibling.index <= lastIdx) continue;
			switch (sibling.tok) {
				case Sharp(MarkLineEnds.SHARP_IF):
					// Check if this Sharp(if) contains a Dot (chain continuation inside #if)
					if (sibling.hasChildren()) {
						for (child in sibling.children) {
							if (child.matches(Dot)) {
								chainedCalls.push(sibling);
								sharpChainExtensions.push(sibling);
								foundSharp = true;
								// Update lastIdx to continue scanning after #end
								var sharpLast:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(sibling);
								if (sharpLast != null) lastIdx = sharpLast.index;
								break;
							}
						}
					}
				case Dot:
					// Dot after #end — continuation of the chain
					chainedCalls.push(sibling);
					sharpChainExtensions.push(sibling);
					// Collect nested Dots within this subtree
					sibling.filterCallback(function(token:TokenTree, index:Int):FilterResult {
						switch (token.tok) {
							case Dot:
								if (isDotAfterPClose(token)) {
									chainedCalls.push(token);
									sharpChainExtensions.push(token);
								}
							case POpen, BrOpen, BkOpen:
								return SkipSubtree;
							default:
						}
						return GoDeeper;
					});
					var sibLast:Null<TokenTree> = TokenTreeCheckUtils.getLastToken(sibling);
					if (sibLast != null) lastIdx = sibLast.index;
				case Binop(OpAdd), Binop(OpSub), Semicolon:
					break; // End of statement — stop extending
				default:
					if (!foundSharp) break; // Unexpected token before first Sharp — stop
			}
		}
	}

	function markOpBoolChaining() {
		var chainStarts:Array<TokenTree> = parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			if (!token.hasChildren()) {
				return SkipSubtree;
			}
			for (child in token.children) {
				switch (child.tok) {
					case Binop(OpBoolAnd), Binop(OpBoolOr):
						return FoundGoDeeper;
					default:
				}
			}
			return GoDeeper;
		});
		for (chainStart in chainStarts) {
			markSingleOpBoolChain(chainStart);
		}
	}

	function markSingleOpBoolChain(itemStart:TokenTree) {
		var items:Array<WrappableItem> = [];

		var firstItemStart:TokenTree = itemStart;
		switch (itemStart.tok) {
			case Binop(_):
				if (itemStart.previousSibling != null) {
					firstItemStart = itemStart.previousSibling;
				}
			default:
		}
		var prev:Null<TokenInfo> = getPreviousToken(firstItemStart);
		var chainStart:TokenTree = itemStart;
		if (prev != null) {
			chainStart = prev.token;
		}
		var chainEnd:Null<TokenTree> = itemStart.getLastChild();
		if (chainEnd != null) {
			chainEnd = TokenTreeCheckUtils.getLastToken(chainEnd);
			switch (chainEnd.tok) {
				case Semicolon, Comma, PClose:
				default:
					var next:Null<TokenInfo> = getNextToken(chainEnd);
					if (next != null) {
						chainEnd = next.token;
					}
			}
		}
		var first:Bool = true;
		if (itemStart.children != null) {
			for (child in itemStart.children) {
				switch (child.tok) {
					case Binop(OpBoolAnd), Binop(OpBoolOr):
						if (first) {
							itemStart = firstItemStart;
							first = false;
						}
						items.push(makeWrappableItem(itemStart, child));
						var next:Null<TokenInfo> = getNextToken(child);
						if (next == null) {
							return;
						}
						// Descend into operator's children to find more chained operators
						itemStart = collectOpBoolItems(child, items, next.token);
					default:
						continue;
				}
			}
		}
		items.push(makeWrappableItem(itemStart, TokenTreeCheckUtils.getLastToken(itemStart)));
		queueWrapping({
			origin: OpBoolChainWrapping,
			start: chainStart,
			end: chainEnd,
			items: items,
			rules: config.wrapping.opBoolChain,
			useTrailing: false,
			overrideAdditionalIndent: null
		}, "markSingleOpBoolChain");
	}

	function markCasePatternChaining() {
		var chainStarts:Array<TokenTree> = parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			return switch (token.tok) {
				case Kwd(KwdCase):
					FoundGoDeeper;
				default:
					GoDeeper;
			}
		});
		for (chainStart in chainStarts) {
			markSingleCasePatternChain(chainStart);
		}
	}

	function markSingleCasePatternChain(itemContainer:TokenTree) {
		var items:Array<WrappableItem> = [];
		// var prev:Null<TokenInfo> = getPreviousToken(findOpAddItemStart(itemContainer));
		var chainStart:TokenTree = itemContainer;
		var chainEnd:Null<TokenTree> = itemContainer.access().firstOf(DblDot).token;
		var next:Null<TokenInfo> = getNextToken(chainStart);
		if (next == null) {
			return;
		}
		var itemStart:TokenTree = next.token;
		if (itemContainer.children != null) {
			for (child in itemContainer.children) {
				switch (child.tok) {
					case DblDot:
						break;
					default:
						var lastToken:TokenTree = TokenTreeCheckUtils.getLastToken(child);
						items.push(makeWrappableItem(child, lastToken));
				}
			}
		}
		queueWrapping({
			origin: CasePatternWrapping,
			start: chainStart,
			end: chainEnd,
			items: items,
			rules: config.wrapping.casePattern,
			useTrailing: false,
			overrideAdditionalIndent: null
		}, "markSingleCasePatternChain");
	}

	function markOpAddChaining() {
		var chainStarts:Array<TokenTree> = parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			if (!token.hasChildren()) {
				return SkipSubtree;
			}
			// Skip operators that are children of another operator —
			// they will be collected recursively by their parent chain.
			switch (token.tok) {
				case Binop(OpAdd), Binop(OpSub):
					return SkipSubtree;
				default:
			}
			for (child in token.children) {
				switch (child.tok) {
					case Binop(OpAdd), Binop(OpSub):
						return FoundGoDeeper;
					default:
				}
			}
			return GoDeeper;
		});
		for (chainStart in chainStarts) {
			markSingleOpAddChain(chainStart);
		}
	}

	function markSingleOpAddChain(itemContainer:TokenTree) {
		// Skip when #if/#end splits statements: OpAdd operators from separate
		// statements become siblings at Block BrOpen level, or children of
		// post-#end Dots at that level.
		switch (itemContainer.tok) {
			case BrOpen:
				if (TokenTreeCheckUtils.getBrOpenType(itemContainer) == Block) {
					return;
				}
			case Dot:
				// Post-#end Dot containing OpAdd — skip, it's part of a method chain
				if (itemContainer.parent != null && itemContainer.parent.tok.match(BrOpen)) {
					if (TokenTreeCheckUtils.getBrOpenType(itemContainer.parent) == Block) {
						return;
					}
				}
			default:
		}
		var items:Array<WrappableItem> = [];
		var prev:Null<TokenInfo> = getPreviousToken(findOpAddItemStart(itemContainer));
		var chainStart:TokenTree = findOpAddItemStart(itemContainer);
		var chainEnd:Null<TokenTree> = itemContainer.getLastChild();
		switch (chainStart.tok) {
			case POpen:
				var type:POpenType = TokenTreeCheckUtils.getPOpenType(chainStart);
				switch (type) {
					case At:
						return;
					case Call:
						// Multi-argument calls: skip opAdd chain wrapping, let callParameter wrap at commas.
						// But collect opAdd operators for post-queue indent fix.
						// Single-argument calls: opAdd chain is the only way to break long arithmetic.
						if (hasCommasBetween(chainStart)) {
							var prevCount:Int = multiParamOpAddTokens.length;
							collectOpAddTokensRecursive(itemContainer, multiParamOpAddTokens);
							// Evaluate opAddSubChain rules to determine break location.
							// If the matching rule uses beforeLast, convert wrapAfter marks
							// to wrapBefore so CodeLine breaks before the operator (leading +).
							var ruleItems:Array<WrappableItem> = [];
							var firstToken:Null<TokenInfo> = getNextToken(chainStart);
							if (firstToken != null) {
								var itemStart:TokenTree = firstToken.token;
								var lastStart:TokenTree = collectOpAddItems(itemContainer, ruleItems, itemStart);
								ruleItems.push(makeWrappableItem(lastStart, TokenTreeCheckUtils.getLastToken(lastStart)));
								if (ruleItems.length > 1) {
									var rule:WrapRule = determineWrapType2(config.wrapping.opAddSubChain, chainStart, ruleItems);
									if (rule.location == BeforeLast && rule.type != NoWrap && rule.type != Keep) {
										for (i in prevCount...multiParamOpAddTokens.length) {
											wrapAfter(multiParamOpAddTokens[i], false);
											wrapBefore(multiParamOpAddTokens[i], true);
										}
									}
								}
							}
							return;
						}
					case Parameter:
					case SwitchCondition:
					case WhileCondition:
					case IfCondition:
					case SharpCondition:
					case Catch:
					case ForLoop:
					case Expression:
				}
			default:
		}

		if (chainEnd != null) {
			chainEnd = TokenTreeCheckUtils.getLastToken(chainEnd);
			switch (chainEnd.tok) {
				case Semicolon, Comma:
				default:
					var next:Null<TokenInfo> = getNextToken(chainEnd);
					if (next != null) {
						chainEnd = next.token;
					}
			}
		}
		var next:Null<TokenInfo> = getNextToken(chainStart);
		if (next == null) {
			return;
		}
		var itemStart:TokenTree = next.token;
		var lastItemStart:TokenTree = collectOpAddItems(itemContainer, items, itemStart);
		items.push(makeWrappableItem(lastItemStart, TokenTreeCheckUtils.getLastToken(lastItemStart)));
		if (items.length <= 1) {
			return;
		}
		queueWrapping({
			origin: OpAddChainWrapping,
			start: chainStart,
			end: null,
			items: items,
			rules: config.wrapping.opAddSubChain,
			useTrailing: true,
			overrideAdditionalIndent: null
		}, "markSingleOpAddChain");

		// Clear wrapAfter on chain operators — chain wrapping manages line breaks.
		// Without this, the first-pass wrapAfter(OpAdd, true) creates a second break
		// after the operator, putting + on its own line.
		for (item in items) {
			switch (item.last.tok) {
				case Binop(OpAdd), Binop(OpSub):
					wrapAfter(item.last, false);
				default:
			}
		}
	}

	/** Recursively collect OpAdd/OpSub tokens from a node's children for post-queue indent fix.
	 * Skips unary minus (OpSub preceded by POpen, Comma, or line start — not a binary chain). */
	function collectOpAddTokensRecursive(node:TokenTree, tokens:Array<TokenTree>) {
		if (node.children == null) return;
		for (child in node.children) {
			switch (child.tok) {
				case Binop(OpAdd), Binop(OpSub):
					// Skip unary minus: OpSub right after ( or , is negation, not subtraction
					var prev:Null<TokenInfo> = getPreviousToken(child);
					if (prev != null) {
						switch (prev.token.tok) {
							case POpen, Comma:
								continue;
							default:
						}
					}
					tokens.push(child);
					collectOpAddTokensRecursive(child, tokens);
				default:
			}
		}
	}

	/** Recursively collect OpBoolAnd/OpBoolOr chain items, descending through nested operators. */
	function collectOpBoolItems(node:TokenTree, items:Array<WrappableItem>, itemStart:TokenTree):TokenTree {
		if (node.children == null) {
			return itemStart;
		}
		for (child in node.children) {
			switch (child.tok) {
				case Binop(OpBoolAnd), Binop(OpBoolOr):
					items.push(makeWrappableItem(itemStart, child));
					var next:Null<TokenInfo> = getNextToken(child);
					if (next == null) {
						continue;
					}
					itemStart = collectOpBoolItems(child, items, next.token);
				default:
					continue;
			}
		}
		return itemStart;
	}

	/** Recursively collect OpAdd/OpSub chain items, descending through nested operators. */
	function collectOpAddItems(node:TokenTree, items:Array<WrappableItem>, itemStart:TokenTree):TokenTree {
		if (node.children == null) {
			return itemStart;
		}
		for (child in node.children) {
			switch (child.tok) {
				case Binop(OpAdd), Binop(OpSub):
					items.push(makeWrappableItem(itemStart, child));
					var next:Null<TokenInfo> = getNextToken(child);
					if (next == null) {
						continue;
					}
					// Descend into the operator's children to find more chained operators
					itemStart = collectOpAddItems(child, items, next.token);
				default:
					continue;
			}
		}
		return itemStart;
	}

	/** Check if there are any Comma tokens between an open and close token (multi-argument call). */
	function hasCommasBetween(openToken:TokenTree):Bool {
		var closeToken:Null<TokenTree> = getCloseToken(openToken);
		if (closeToken == null) return false;
		// Walk token list between open and close, tracking nesting depth
		var depth:Int = 0;
		var idx:Int = openToken.index + 1;
		while (idx < closeToken.index) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			switch (info.token.tok) {
				case POpen, BkOpen, BrOpen:
					depth++;
				case PClose, BkClose, BrClose:
					depth--;
				case Comma:
					if (depth == 0) return true;
				default:
			}
		}
		return false;
	}

	function findOpAddItemStart(itemStart:TokenTree):TokenTree {
		if ((itemStart == null) || (itemStart.tok == Root)) {
			return itemStart;
		}
		var parent:TokenTree = itemStart;
		while ((parent != null) && (parent.tok != Root)) {
			switch (parent.tok) {
				case POpen:
					var pClose:Null<TokenTree> = parent.access().firstOf(PClose).token;
					if ((pClose == null) || (pClose.index > itemStart.index)) {
						return parent;
					}
				case BkOpen:
					var bkClose:Null<TokenTree> = parent.access().firstOf(BkClose).token;
					if ((bkClose == null) || (bkClose.index > itemStart.index)) {
						return parent;
					}
				case BrOpen:
					var brClose:Null<TokenTree> = parent.access().firstOf(BrClose).token;
					if ((brClose == null) || (brClose.index > itemStart.index)) {
						// Don't use ObjectDecl as chain start — the opAdd chain is
						// within one field value, not spanning the whole struct.
						// Returning BrOpen causes wrapFillLine2BeforeLast to call
						// noLineEndAfter(BrOpen), removing the multiline wrapping.
						if (TokenTreeCheckUtils.getBrOpenType(parent) == ObjectDecl) {
							return itemStart;
						}
						return parent;
					}
				case Binop(OpAssign), Binop(OpAssignOp(_)):
					return parent;
				case Kwd(KwdThis), Kwd(KwdUntyped), Kwd(KwdNull):
				case Kwd(_):
					return parent;
				default:
			}
			itemStart = parent;
			parent = parent.parent;
		}
		return itemStart;
	}

	function makeWrappableItem(start:TokenTree, end:TokenTree):WrappableItem {
		var sameLine:Bool = isSameLineBetween(start, end, false);
		var firstLineLength:Int = 0;
		var lastLineLength:Int = 0;
		if (sameLine) {
			firstLineLength = calcLengthBetween(start, end) + calcTokenLength(end);
		} else {
			firstLineLength = calcLengthUntilNewline(start, end);
			lastLineLength = calcLineLengthBefore(end) + calcTokenLength(end);
		}
		return {
			first: start,
			last: end,
			multiline: !sameLine,
			firstLineLength: firstLineLength,
			lastLineLength: lastLineLength
		}
	}

	function markImplementsExtendsChaining() {
		var classesAndInterfaces:Array<TokenTree> = parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case Kwd(KwdInterface), Kwd(KwdClass):
					return FoundSkipSubtree;
				case Kwd(KwdAbstract), Kwd(KwdEnum), Kwd(KwdTypedef):
					return SkipSubtree;
				default:
					return GoDeeper;
			}
		});
		for (type in classesAndInterfaces) {
			var items:Array<WrappableItem> = [];
			var impls:Array<TokenTree> = type.filterCallback(function(token:TokenTree, index:Int):FilterResult {
				switch (token.tok) {
					case Kwd(KwdExtends), Kwd(KwdImplements):
						return FoundSkipSubtree;
					case Kwd(KwdFunction), Kwd(KwdVar):
						return SkipSubtree;
					default:
						return GoDeeper;
				}
			});
			for (impl in impls) {
				var endToken:TokenTree = TokenTreeCheckUtils.getLastToken(impl);
				items.push(makeWrappableItem(impl, endToken));
			}
			if (items.length <= 0) {
				continue;
			}
			var chainOpen:TokenTree = items[0].first;
			var prev:TokenInfo = getPreviousToken(items[0].first);
			if (prev != null) {
				chainOpen = prev.token;
			}
			var chainEnd:TokenTree = items[items.length - 1].last;
			extendsWraps.push({first: items[0].first, end: chainEnd});
			queueWrapping({
				origin: ImplementsWrapping,
				start: chainOpen,
				end: chainEnd,
				items: items,
				rules: config.wrapping.implementsExtends,
				useTrailing: false,
				overrideAdditionalIndent: null
			}, "markImplementsExtendsChaining");
		}
	}

	function markMultiVarChaining() {
		var allVars:Array<TokenTree> = parsedCode.root.filterCallback(function(token:TokenTree, index:Int):FilterResult {
			switch (token.tok) {
				case Kwd(KwdVar):
					if ((token.hasChildren()) && (token.children.length > 1)) {
						return FoundSkipSubtree;
					}
					return SkipSubtree;
				default:
					return GoDeeper;
			}
		});
		for (v in allVars) {
			var items:Array<WrappableItem> = [];
			if (v.children == null) {
				continue;
			}
			for (child in v.children) {
				var endToken:TokenTree = TokenTreeCheckUtils.getLastToken(child);
				items.push(makeWrappableItem(child, endToken));
			}
			if (items.length <= 0) {
				continue;
			}
			var chainOpen:TokenTree = v;
			var chainEnd:TokenTree = TokenTreeCheckUtils.getLastToken(v);
			queueWrapping({
				origin: MultiVarWrapping,
				start: chainOpen,
				end: chainEnd,
				items: items,
				rules: config.wrapping.multiVar,
				useTrailing: false,
				overrideAdditionalIndent: null
			}, "markMultiVarChaining");
		}
	}

	// ── Save/Restore break helpers ──────────────────────────────────────

	/** Remove line breaks in a token range and return saved state for restoration.
	 *  Without matchOperator: removes ALL breaks (saves the token with the break).
	 *  With matchOperator: removes breaks before matching operator tokens (saves predecessor). */
	function saveAndRemoveBreaks(startIdx:Int, endIdx:Int,
			?matchOperator:(tok:tokentree.TokenTreeDef) -> Bool):Array<{idx:Int, ws:formatter.codedata.WhitespaceAfterType}> {
		var saved:Array<{idx:Int, ws:formatter.codedata.WhitespaceAfterType}> = [];
		var idx:Int = startIdx;
		while (idx <= endIdx) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[idx];
			idx++;
			if (info == null) continue;
			if (matchOperator != null) {
				if (matchOperator(info.token.tok)) {
					var prevInfo:Null<TokenInfo> = getPreviousToken(info.token);
					if (prevInfo != null && prevInfo.whitespaceAfter == Newline) {
						saved.push({idx: prevInfo.token.index, ws: Newline});
						prevInfo.whitespaceAfter = if (prevInfo.spacesAfter <= 0) None else Space;
					}
				}
			} else {
				if (info.whitespaceAfter == Newline) {
					saved.push({idx: info.token.index, ws: Newline});
					info.whitespaceAfter = if (info.spacesAfter <= 0) None else Space;
				}
			}
		}
		return saved;
	}

	/** Restore previously saved line breaks. */
	function restoreBreaks(saved:Array<{idx:Int, ws:formatter.codedata.WhitespaceAfterType}>) {
		for (s in saved) {
			var info:Null<TokenInfo> = parsedCode.tokenList.tokens[s.idx];
			if (info != null) info.whitespaceAfter = s.ws;
		}
	}
}
