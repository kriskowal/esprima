/*
  Copyright (C) 2011 Ariya Hidayat <ariya.hidayat@gmail.com>

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.
    * Redistributions in binary form must reproduce the above copyright
      notice, this list of conditions and the following disclaimer in the
      documentation and/or other materials provided with the distribution.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
  AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
  IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
  ARE DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
  DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
  (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
  ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
  (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
  THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

/*global esprima:true, exports:true,
throwError: true,
parseAssignmentExpression: true, parseBlock: true, parseExpression: true,
parseFunctionDeclaration: true, parseFunctionExpression: true,
parseStatement: true, visitPostorder: true */

(function (exports) {
    'use strict';

        // constants:
    var Token,
        Syntax,
        Messages,
        // scoped to parse calls:
        source,
        length,
        sourceName = "",
        extra,
        finish,
        trackingRange = false,
        trackingLoc = false,
        tracking = false, // trackingRange || trackingLoc
        // cursor state:
        index,
        lineIndex,
        lineNumber,
        buffer,
        lastToken,
        lookingAhead;

    Token = {
        BooleanLiteral: 1,
        EOF: 2,
        Identifier: 3,
        Keyword: 4,
        NullLiteral: 5,
        NumericLiteral: 6,
        Punctuator: 7,
        StringLiteral: 8
    };

    Syntax = {
        AssignmentExpression: 'AssignmentExpression',
        ArrayExpression: 'ArrayExpression',
        BlockStatement: 'BlockStatement',
        BinaryExpression: 'BinaryExpression',
        BreakStatement: 'BreakStatement',
        CallExpression: 'CallExpression',
        CatchClause: 'CatchClause',
        ConditionalExpression: 'ConditionalExpression',
        ContinueStatement: 'ContinueStatement',
        DoWhileStatement: 'DoWhileStatement',
        DebuggerStatement: 'DebuggerStatement',
        EmptyStatement: 'EmptyStatement',
        ExpressionStatement: 'ExpressionStatement',
        ForStatement: 'ForStatement',
        ForInStatement: 'ForInStatement',
        FunctionDeclaration: 'FunctionDeclaration',
        FunctionExpression: 'FunctionExpression',
        Identifier: 'Identifier',
        IfStatement: 'IfStatement',
        Literal: 'Literal',
        LabeledStatement: 'LabeledStatement',
        LogicalExpression: 'LogicalExpression',
        MemberExpression: 'MemberExpression',
        NewExpression: 'NewExpression',
        ObjectExpression: 'ObjectExpression',
        Program: 'Program',
        ReturnStatement: 'ReturnStatement',
        SequenceExpression: 'SequenceExpression',
        SwitchStatement: 'SwitchStatement',
        SwitchCase: 'SwitchCase',
        ThisExpression: 'ThisExpression',
        ThrowStatement: 'ThrowStatement',
        TryStatement: 'TryStatement',
        UnaryExpression: 'UnaryExpression',
        UpdateExpression: 'UpdateExpression',
        VariableDeclaration: 'VariableDeclaration',
        WhileStatement: 'WhileStatement',
        WithStatement: 'WithStatement'
    };

    Messages = {
        UnexpectedToken:  'Unexpected token %0',
        UnexpectedNumber:  'Unexpected number',
        UnexpectedString:  'Unexpected string',
        UnexpectedIdentifier:  'Unexpected identifier',
        UnexpectedReserved:  'Unexpected reserved word: %0',
        UnexpectedEOS:  'Unexpected end of input',
        NewlineAfterThrow:  'Illegal newline after throw',
        InvalidRegExp: 'Invalid regular expression',
        UnterminatedRegExp:  'Invalid regular expression: missing /',
        InvalidLHSInAssignment:  'Invalid left-hand side in assignment',
        InvalidLHSInForIn:  'Invalid left-hand side in for-in',
        InvalidLHSInPostfixOp:  'Invalid left-hand side expression in postfix operation',
        InvalidLHSInPrefixOp:  'Invalid left-hand side expression in prefix operation',
        NoCatchOrFinally:  'Missing catch or finally after try'
    };

    if (typeof Object.freeze === 'function') {
        Object.freeze(Token);
        Object.freeze(Syntax);
        Object.freeze(Messages);
    }

    function isDecimalDigit(ch) {
        return '0123456789'.indexOf(ch) >= 0;
    }

    function isHexDigit(ch) {
        return '0123456789abcdefABCDEF'.indexOf(ch) >= 0;
    }

    // TODO: really handle Unicode category Lu, LI, Lt, Lm, Lo, NI
    function isUnicodeLetter(ch) {
        return (ch >= 'a' && ch <= 'z') ||
            (ch >= 'A' && ch <= 'Z');
    }

    // TODO: really handle Unicode category Nd
    function isUnicodeDigit(ch) {
        return (ch >= '0') && (ch <= '9');
    }

    // 7.2 White Space

    function isWhiteSpace(ch) {
        // TODO Unicode "space separator"
        return (ch === ' ') || (ch === '\u0009') || (ch === '\u000B') ||
            (ch === '\u000C') || (ch === '\u00A0') || (ch === '\uFEFF');
    }

    // 7.3 Line Terminators

    function isLineTerminator(ch) {
        return (ch === '\n' || ch === '\r' || ch === '\u2028' || ch === '\u2029');
    }

    // 7.6 Identifier Names and Identifiers

    function isIdentifierStart(ch) {
        // TODO UnicodeEscapeSequence
        return (ch === '$') || (ch === '_') || isUnicodeLetter(ch);
    }

    function isIdentifierPart(ch) {
        // TODO UnicodeCombiningMark UnicodeConnectorPunctuation and ZWNJ and ZWJ
        return isIdentifierStart(ch) || isUnicodeDigit(ch);
    }

    // 7.6.1.1 Keywords
    // 7.6.1.2 Future Reserved Words

    function isKeyword(id) {
        switch (id) {

        // Keywords.
        case 'break':
        case 'case':
        case 'catch':
        case 'continue':
        case 'debugger':
        case 'default':
        case 'delete':
        case 'do':
        case 'else':
        case 'finally':
        case 'for':
        case 'function':
        case 'if':
        case 'in':
        case 'instanceof':
        case 'new':
        case 'return':
        case 'switch':
        case 'this':
        case 'throw':
        case 'try':
        case 'typeof':
        case 'var':
        case 'void':
        case 'while':
        case 'with':

        // Future reserved words.
        case 'class':
        case 'const':
        case 'enum':
        case 'export':
        case 'extends':
        case 'import':
        case 'super':

        // strict mode
        case 'implements':
        case 'interface':
        case 'let':
        case 'package':
        case 'private':
        case 'protected':
        case 'public':
        case 'static':
        case 'yield':
            return true;
        }

        return false;
    }

    // Start, then finish, tracking the range or location of a part
    function start() {
        var startLineNumber, startLineIndex, startIndex;

        startLineNumber = lineNumber;
        startLineIndex = lineIndex;
        startIndex = index;

        return function (object) {
            var lastLineNumber, lastLineIndex, lastIndex;

            lastLineNumber = lineNumber;
            lastLineIndex = lineIndex;
            lastIndex = index;

            if (trackingRange) {
                object.range = [startIndex, lastIndex - 1];
            }

            if (trackingLoc) {
                object.loc = {
                    source: sourceName,
                    start: {
                        line: startLineNumber,
                        column: startIndex - startLineIndex
                    },
                    end: {
                        line: lastLineNumber,
                        column: lastIndex - lastLineIndex
                    }
                };
            }

            return object;
        };
    }

    // Copy the range or location of a bit of syntax from the
    // originating token
    function finishUsingToken(syntax, token) {
        if (trackingRange) {
            syntax.range = token.range;
        }
        if (trackingLoc) {
            syntax.loc = token.loc;
        }
    }

    // Return the next character and move forward.

    function nextChar() {
        var ch = '\x00',
            idx = index;

        if (idx < length) {
            ch = source[idx];
            index += 1;
        }
        return ch;
    }

    // 7.4 Comments

    function skipComment() {
        var ch, blockComment, lineComment;

        blockComment = false;
        lineComment = false;

        while (index < length) {
            ch = source[index];

            if (lineComment) {
                nextChar();
                if (isLineTerminator(ch)) {
                    lineComment = false;
                    lineNumber += 1;
                    lineIndex = index + 1;
                }
            } else if (blockComment) {
                nextChar();
                if (ch === '*') {
                    ch = source[index];
                    if (ch === '/') {
                        nextChar();
                        blockComment = false;
                    }
                } else if (isLineTerminator(ch)) {
                    lineNumber += 1;
                    lineIndex = index + 1;
                }
            } else if (ch === '/') {
                ch = source[index + 1];
                if (ch === '/') {
                    nextChar();
                    nextChar();
                    lineComment = true;
                } else if (ch === '*') {
                    nextChar();
                    nextChar();
                    blockComment = true;
                } else {
                    break;
                }
            } else if (isWhiteSpace(ch)) {
                nextChar();
            } else if (isLineTerminator(ch)) {
                nextChar();
                lineNumber += 1;
                lineIndex = index;
            } else {
                break;
            }
        }
    }

    function scanIdentifier() {
        var ch, id, token, finish;

        if (tracking) {
            finish = start();
        }

        ch = source[index];
        if (!isIdentifierStart(ch)) {
            return;
        }

        id = nextChar();
        while (index < length) {
            ch = source[index];
            if (!isIdentifierPart(ch)) {
                break;
            }
            id += nextChar();
        }

        // There is no keyword or literal with only one character.
        // Thus, it must be an identifier.
        if (id.length === 1) {
            token = {
                type: Token.Identifier,
                value: id
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        if (isKeyword(id)) {
            token = {
                type: Token.Keyword,
                value: id
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        // 7.8.1 Null Literals

        if (id === 'null') {
            token = {
                type: Token.NullLiteral
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        // 7.8.2 Boolean Literals

        if (id === 'true' || id === 'false') {
            token = {
                type: Token.BooleanLiteral,
                value: id
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        token = {
            type: Token.Identifier,
            value: id
        };
        if (tracking) {
            finish(token);
        }
        return token;
    }

    // 7.7 Punctuators

    function scanPunctuator() {
        var ch1 = source[index],
            ch2,
            ch3,
            ch4,
            token,
            finish;

        if (tracking) {
            finish = start();
        }

        // Check for most common single-character punctuators.

        if (ch1 === ';' || ch1 === '{' || ch1 === '}') {
            nextChar();
            token = {
                type: Token.Punctuator,
                value: ch1
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        if (ch1 === ',' || ch1 === '(' || ch1 === ')') {
            nextChar();
            token = {
                type: Token.Punctuator,
                value: ch1
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        // Dot (.) can also start a floating-point number, hence the need
        // to check the next character.

        ch2 = source[index + 1];
        if (ch1 === '.' && !isDecimalDigit(ch2)) {
            token = {
                type: Token.Punctuator,
                value: nextChar()
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        // Peek more characters.

        ch3 = source[index + 2];
        ch4 = source[index + 3];

        // 4-character punctuator: >>>=

        if (ch1 === '>' && ch2 === '>' && ch3 === '>') {
            if (ch4 === '=') {
                nextChar();
                nextChar();
                nextChar();
                nextChar();
                token = {
                    type: Token.Punctuator,
                    value: '>>>='
                };
                if (tracking) {
                    finish(token);
                }
                return token;
            }
        }

        // 3-character punctuators: === !== >>> <<= >>=

        if (ch1 === '=' && ch2 === '=' && ch3 === '=') {
            nextChar();
            nextChar();
            nextChar();
            token = {
                type: Token.Punctuator,
                value: '==='
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        if (ch1 === '!' && ch2 === '=' && ch3 === '=') {
            nextChar();
            nextChar();
            nextChar();
            token = {
                type: Token.Punctuator,
                value: '!=='
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        if (ch1 === '>' && ch2 === '>' && ch3 === '>') {
            nextChar();
            nextChar();
            nextChar();
            token = {
                type: Token.Punctuator,
                value: '>>>'
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        if (ch1 === '<' && ch2 === '<' && ch3 === '=') {
            nextChar();
            nextChar();
            nextChar();
            token = {
                type: Token.Punctuator,
                value: '<<='
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        if (ch1 === '>' && ch2 === '>' && ch3 === '=') {
            nextChar();
            nextChar();
            nextChar();
            token = {
                type: Token.Punctuator,
                value: '>>='
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }

        // 2-character punctuators: <= >= == != ++ -- << >> && ||
        // += -= *= %= &= |= ^= /=

        if (ch2 === '=') {
            if ('<>=!+-*%&|^/'.indexOf(ch1) >= 0) {
                nextChar();
                nextChar();
                token = {
                    type: Token.Punctuator,
                    value: ch1 + ch2
                };
                if (tracking) {
                    finish(token);
                }
                return token;
            }
        }

        if (ch1 === ch2 && ('+-<>&|'.indexOf(ch1) >= 0)) {
            if ('+-<>&|'.indexOf(ch2) >= 0) {
                nextChar();
                nextChar();
                token = {
                    type: Token.Punctuator,
                    value: ch1 + ch2
                };
                if (tracking) {
                    finish(token);
                }
                return token;
            }
        }

        // The remaining 1-character punctuators.

        if ('[]<>+-*%&|^!~?:=/'.indexOf(ch1) >= 0) {
            token = {
                type: Token.Punctuator,
                value: nextChar()
            };
            if (tracking) {
                finish(token);
            }
            return token;
        }
    }

    // 7.8.3 Numeric Literals

    function scanNumericLiteral() {
        var number, ch, token, finish;

        if (tracking) {
            finish = start();
        }

        ch = source[index];
        if (!isDecimalDigit(ch) && (ch !== '.')) {
            return;
        }

        number = '';
        if (ch !== '.') {
            number = nextChar();
            ch = source[index];

            // Hex number starts with '0x'.
            if (ch === 'x' || ch === 'X') {
                number += nextChar();
                while (index < length) {
                    ch = source[index];
                    if (!isHexDigit(ch)) {
                        break;
                    }
                    number += nextChar();
                }
                token = {
                    type: Token.NumericLiteral,
                    value: parseInt(number, 16)
                };
                if (tracking) {
                    finish(token);
                }
                return token;
            }

            while (index < length) {
                ch = source[index];
                if (!isDecimalDigit(ch)) {
                    break;
                }
                number += nextChar();
            }
        }

        if (ch === '.') {
            number += nextChar();
            while (index < length) {
                ch = source[index];
                if (!isDecimalDigit(ch)) {
                    break;
                }
                number += nextChar();
            }
        }

        if (ch === 'e' || ch === 'E') {
            number += nextChar();
            ch = source[index];
            if (ch === '+' || ch === '-' || isDecimalDigit(ch)) {
                number += nextChar();
                while (index < length) {
                    ch = source[index];
                    if (!isDecimalDigit(ch)) {
                        break;
                    }
                    number += nextChar();
                }
            } else {
                ch = 'character ' + ch;
                if (index >= length) {
                    ch = '<end>';
                }
                throwError(Messages.UnexpectedToken, 'ILLEGAL');
            }
        }

        token = {
            type: Token.NumericLiteral,
            value: parseFloat(number)
        };
        if (tracking) {
            finish(token);
        }
        return token;
    }

    // 7.8.4 String Literals

    // TODO Unicode
    function scanStringLiteral() {
        var str = '', quote, ch, token, finish;

        if (tracking) {
            finish = start();
        }

        quote = source[index];
        if (quote !== '\'' && quote !== '"') {
            return;
        }
        nextChar();

        while (index < length) {
            ch = nextChar();

            if (ch === quote) {
                quote = '';
                break;
            } else if (ch === '\\') {
                ch = nextChar();
                if (!isLineTerminator(ch)) {
                    str += '\\';
                    str += ch;
                }
            } else {
                str += ch;
            }
        }

        if (quote !== '') {
            throwError(Messages.UnexpectedToken, 'ILLEGAL');
        }

        token = {
            type: Token.StringLiteral,
            value: str
        };
        if (tracking) {
            finish(token);
        }
        return token;
    }

    function scanRegExp() {
        var str = '',
            ch,
            pattern,
            flags,
            value,
            classMarker = false,
            token,
            finish;

        buffer = null;
        skipComment();

        if (tracking) {
            finish = start();
        }

        ch = source[index];
        if (ch !== '/') {
            return;
        }
        str = nextChar();

        while (index < length) {
            ch = nextChar();
            str += ch;
            if (classMarker) {
                if (ch === ']') {
                    classMarker = false;
                }
            } else {
                if (ch === '\\') {
                    str += nextChar();
                }
                if (ch === '/') {
                    break;
                }
                if (ch === '[') {
                    classMarker = true;
                }
                if (isLineTerminator(ch)) {
                    throwError(Messages.UnterminatedRegExp);
                }
            }
        }

        // Exclude leading and trailing slash.
        pattern = str.substr(1, str.length - 2);

        flags = '';
        while (index < length) {
            ch = source[index];
            if (!isIdentifierPart(ch)) {
                break;
            }
            flags += ch;
            str += nextChar();
        }

        try {
            value = new RegExp(pattern, flags);
        } catch (e) {
            throwError(Messages.InvalidRegExp);
        }

        token = {
            // XXX should there be a type for this?
            literal: str,
            value: value
        };
        if (tracking) {
            finish(token);
        }
        return token;
    }

    function advance() {
        var ch, token;

        if (index >= length) {
            return {
                type: Token.EOF
            };
        }

        token = scanPunctuator();
        if (typeof token !== 'undefined') {
            return token;
        }

        ch = source[index];

        if (ch === '\'' || ch === '"') {
            return scanStringLiteral();
        }

        if (ch === '.' || isDecimalDigit(ch)) {
            return scanNumericLiteral();
        }

        token = scanIdentifier();
        if (typeof token !== 'undefined') {
            return token;
        }

        throwError(Messages.UnexpectedToken, 'ILLEGAL');
    }

    function lex() {
        var token, initialIndex, initialLineNumber, initialLineIndex;

        if (buffer) {
            index = buffer.finalIndex;
            lineNumber = buffer.finalLineNumber;
            lineIndex = buffer.finalLineIndex;
            token = buffer;
            buffer = null;
            return token;
        }

        buffer = null;
        skipComment();

        initialIndex = index;
        initialLineIndex = lineIndex;
        initialLineNumber = lineNumber;

        token = advance();

        token.index = initialIndex;
        token.lineIndex = initialLineIndex;
        token.lineNumber = initialLineNumber;

        lastToken = token;

        return token;
    }

    function lookahead() {
        var token, tempIndex, tempLineIndex, tempLineNumber;

        if (buffer !== null) {
            return buffer;
        }

        tempIndex = index;
        tempLineIndex = lineIndex;
        tempLineNumber = lineNumber;

        lookingAhead = true;
        token = lex();
        lookingAhead = false;

        token.finalIndex = index;
        token.finalLineIndex = lineIndex;
        token.finalLineNumber = lineNumber;

        index = tempIndex;
        lineIndex = tempLineIndex;
        lineNumber = tempLineNumber;

        buffer = token;

        return buffer;
    }

    // Return true if there is a line terminator before the next token.

    function peekLineTerminator() {
        var tempIndex, tempLineNumber, tempLineIndex, found;

        tempIndex = index;
        tempLineNumber = lineNumber;
        tempLineIndex = lineIndex;

        skipComment();

        found = lineNumber !== tempLineNumber;

        index = tempIndex;
        lineNumber = tempLineNumber;
        lineIndex = tempLineIndex;

        return found;
    }

    // Throw an exception

    function throwError(messageFormat) {
        var args = Array.prototype.slice.call(arguments, 1);
        throw new Error(
            'Line ' + lineNumber +
            ': ' + messageFormat.replace(
                /%(\d)/g,
                function (whole, index) {
                    return args[index] || '';
                }
            )
        );
    }

    // Throw an exception because of the token.

    function throwUnexpected(token) {
        var s;

        if (token.type === Token.EOF) {
            throwError(Messages.UnexpectedEOS);
        }

        if (token.type === Token.NumericLiteral) {
            throwError(Messages.UnexpectedNumber);
        }

        if (token.type === Token.StringLiteral) {
            throwError(Messages.UnexpectedString);
        }

        if (token.type === Token.Identifier) {
            throwError(Messages.UnexpectedIdentifier);
        }

        if (token.type === Token.Keyword) {
            throwError(Messages.UnexpectedReserved, token.value);
        }

        s = token.value;
        if (s.length > 10) {
            s = s.substr(0, 10) + '...';
        }
        throwError(Messages.UnexpectedToken, s);
    }

    // Expect the next token to match the specified punctuator.
    // If not, an exception will be thrown.

    function expect(value) {
        var token = lex();
        if (token.type !== Token.Punctuator || token.value !== value) {
            throwUnexpected(token);
        }
    }

    // Expect the next token to match the specified keyword.
    // If not, an exception will be thrown.

    function expectKeyword(keyword) {
        var token = lex();
        if (token.type !== Token.Keyword || token.value !== keyword) {
            throwUnexpected(token);
        }
    }

    // Return true if the next token matches the specified punctuator.

    function match(value) {
        var token = lookahead();
        return token.type === Token.Punctuator && token.value === value;
    }

    // Return true if the next token matches the specified keyword

    function matchKeyword(keyword) {
        var token = lookahead();
        return token.type === Token.Keyword && token.value === keyword;
    }

    // Return true if the next token is an assignment operator

    function matchAssign() {
        var token = lookahead(),
            op = token.value;

        if (token.type !== Token.Punctuator) {
            return false;
        }
        return op === '=' ||
            op === '*=' ||
            op === '/=' ||
            op === '%=' ||
            op === '+=' ||
            op === '-=' ||
            op === '<<=' ||
            op === '>>=' ||
            op === '>>>=' ||
            op === '&=' ||
            op === '^=' ||
            op === '|=';
    }

    // Return true if expr is left hand side expression

    function isLeftHandSide(expr) {
        return expr.type === Syntax.Identifier ||
            expr.type === Syntax.MemberExpression ||
            expr.type === Syntax.CallExpression ||
            expr.type === Syntax.NewExpression;
    }

    function consumeSemicolon() {
        var token, sameLineNumber;

        // Catch the very common case first.
        if (source[index] === ';') {
            lex();
            return;
        }

        sameLineNumber = lineNumber;
        skipComment();
        if (lineNumber !== sameLineNumber) {
            return;
        }

        if (match(';')) {
            lex();
            return;
        }

        token = lookahead();
        if (token.type !== Token.EOF && !match('}')) {
            throwUnexpected(token);
        }
        return;
    }

    // 11.1.4 Array Initialiser

    function parseArrayInitialiser() {
        var elements = [], undef, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expect('[');

        while (index < length) {
            if (match(']')) {
                lex();
                break;
            }

            if (match(',')) {
                lex();
                elements.push(undef);
            } else {
                elements.push(parseAssignmentExpression());

                if (match(']')) {
                    lex();
                    break;
                }

                expect(',');
            }
        }

        syntax = {
            type: Syntax.ArrayExpression,
            elements: elements
        };

        if (tracking) {
            finish(syntax);
        }

        return syntax;
    }

    // 11.1.5 Object Initialiser

    function parseObjectInitialiser() {
        var token,
            expr,
            properties = [],
            property,
            finish,
            nestedFinish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expect('{');

        // TODO handle 'get' and 'set'
        while (index < length) {
            nestedFinish = start();
            token = lex();
            if (token.type === Token.Punctuator && token.value === '}') {
                break;
            }

            property = {};
            switch (token.type) {
            case Token.Identifier:
                property.key = {
                    type: Syntax.Identifier,
                    name: token.value
                };
                if (tracking) {
                    finishUsingToken(property.key, token);
                }

                // Property Assignment: Getter and Setter.

                if (token.value === 'get' && !match(':')) {
                    token = lex();
                    if (token.type !== Token.Identifier) {
                        throwUnexpected(token);
                    }
                    expect('(');
                    expect(')');
                    property = {
                        key: {
                            type: Syntax.Identifier,
                            name: token.value
                        },
                        value: {
                            type: Syntax.FunctionExpression,
                            id: null,
                            params: [],
                            body: parseBlock()
                        },
                        kind: 'get'
                    };
                    if (tracking) {
                        finishUsingToken(property.key, token);
                        nestedFinish(property.value);
                    }
                    break;
                }

                if (token.value === 'set' && !match(':')) {
                    token = lex();
                    if (token.type !== Token.Identifier) {
                        throwUnexpected(token);
                    }
                    property.key = {
                        type: Syntax.Identifier,
                        name: token.value
                    };
                    if (tracking) {
                        finishUsingToken(property.key, token);
                    }
                    expect('(');
                    token = lex();
                    if (token.type !== Token.Identifier) {
                        throwUnexpected(token);
                    }
                    expect(')');
                    property.value = {
                        type: Syntax.FunctionExpression,
                        id: null,
                        params: [{
                            type: Syntax.Identifier,
                            name: token.value
                        }],
                        body: parseBlock()
                    };
                    if (tracking) {
                        nestedFinish(property.value);
                        finishUsingToken(property.value.params[0], token);
                    }
                    property.kind = 'set';
                    break;
                }

                expect(':');
                property.value = parseAssignmentExpression();
                break;

            case Token.StringLiteral:
            case Token.NumericLiteral:
                property.key = {
                    type: Syntax.Literal,
                    value: token.value
                };
                if (tracking) {
                    finishUsingToken(property.key, token);
                }
                expect(':');
                property.value = parseAssignmentExpression();
                break;

            default:
                throwUnexpected(token);
            }
            properties.push(property);

            token = lookahead();
            if (token.type === Token.Punctuator && token.value === '}') {
                lex();
                break;
            }
            expect(',');
        }

        token = {
            type: Syntax.ObjectExpression,
            properties: properties
        };

        if (tracking) {
            finish(token);
        }

        return token;
    }

    // 11.1 Primary Expressions

    function parsePrimary() {
        var token, expr;

        if (match('[')) {
            return parseArrayInitialiser();
        }

        if (match('{')) {
            return parseObjectInitialiser();
        }

        if (match('(')) {
            lex();
            expr = parseExpression();
            expect(')');
            return expr.expression;
        }

        if (matchKeyword('function')) {
            return parseFunctionExpression();
        }

        if (matchKeyword('this')) {
            lex();
            return {
                type: Syntax.ThisExpression
            };
        }

        if (match('/') || match('/=')) {
            token = scanRegExp();
            expr = {
                type: Syntax.Literal,
                value: token.value
            };
            if (tracking) {
                finishUsingToken(expr, token);
            }
            return expr;
        }

        token = lex();

        if (token.type === Token.Identifier) {
            expr = {
                type: Syntax.Identifier,
                name: token.value
            };
            if (tracking) {
                finishUsingToken(expr, token);
            }
            return expr;
        }

        if (token.type === Token.BooleanLiteral) {
            expr ={
                type: Syntax.Literal,
                value: (token.value === 'true')
            };
            if (tracking) {
                finishUsingToken(expr, token);
            }
            return expr;
        }

        if (token.type === Token.NullLiteral) {
            expr = {
                type: Syntax.Literal,
                value: null
            };
            if (tracking) {
                finishUsingToken(expr, token);
            }
            return expr;
        }

        if (token.type === Token.NumericLiteral) {
            expr = {
                type: Syntax.Literal,
                value: token.value
            };
            if (tracking) {
                finishUsingToken(expr, token);
            }
            return expr;
        }

        if (token.type === Token.StringLiteral) {
            expr = {
                type: Syntax.Literal,
                value: token.value
            };
            if (tracking) {
                finishUsingToken(expr, token);
            }
            return expr;
        }

        return throwUnexpected(token);
    }

    function parsePrimaryExpression() {
        return parsePrimary();
    }

    // 11.2 Left-Hand-Side Expressions

    function parseArguments() {
        var args = [];

        expect('(');

        if (!match(')')) {
            while (index < length) {
                args.push(parseAssignmentExpression());
                if (match(')')) {
                    break;
                }
                expect(',');
            }
        }

        expect(')');

        return args;
    }

    function parseMemberExpression() {
        var expr, token, property, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parsePrimaryExpression();

        while (index < length) {
            if (match('.')) {
                lex();
                token = lex();
                if (token.type !== Token.Identifier) {
                    throwUnexpected(token);
                }
                property = {
                    type: Syntax.Identifier,
                    name: token.value
                };
                expr = {
                    type: Syntax.MemberExpression,
                    computed: false,
                    object: expr,
                    property: property
                };
                if (tracking) {
                    finishUsingToken(property, token);
                    finish(expr);
                }
            } else if (match('[')) {
                lex();
                property = parseExpression();
                if (property.type === Syntax.ExpressionStatement) {
                    property = property.expression;
                }
                expect(']');
                expr = {
                    type: Syntax.MemberExpression,
                    computed: true,
                    object: expr,
                    property: property
                };
                if (tracking) {
                    finish(expr);
                }
            } else if (match('(')) {
                expr = {
                    type: Syntax.CallExpression,
                    callee: expr,
                    'arguments': parseArguments()
                };
                if (tracking) {
                    finish(expr);
                }
            } else {
                break;
            }
        }

        return expr;
    }

    function parseLeftHandSideExpression() {
        var useNew, expr, args, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        useNew = matchKeyword('new');
        if (useNew) {
            // Read the keyword.
            lex();
            expr = parseLeftHandSideExpression();
        } else {
            expr = parseMemberExpression();
        }

        if (match('(')) {
            args = parseArguments();
        }

        if (useNew) {

            // Force to have at least an empty argument list.
            if (typeof args === 'undefined') {
                args = [];
            }

            // e.g. "new x()" thus adopt the CallExpression of "x()".
            if (expr.type === Syntax.CallExpression) {
                args = expr['arguments'];
                expr = expr.callee;
            }

            syntax = {
                type: Syntax.NewExpression,
                callee: expr,
                'arguments': args
            };
            if (tracking) {
                finish(syntax);
            }
            return syntax;
        }

        if (typeof args !== 'undefined') {
            syntax = {
                type: Syntax.CallExpression,
                callee: expr,
                'arguments': args
            };
            if (tracking) {
                finish(syntax);
            }
            return syntax;
        }

        return expr;
    }

    // 11.3 Postfix Expressions

    function parsePostfixExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseLeftHandSideExpression();

        if ((match('++') || match('--')) && !peekLineTerminator()) {
            if (!isLeftHandSide(expr)) {
                throwError(Messages.InvalidLHSInPostfixOp);
            }
            expr = {
                type: Syntax.UpdateExpression,
                operator: lex().value,
                argument: expr,
                prefix: false
            };
            if (tracking) {
                finish(expr);
            }
        }

        return expr;
    }

    // 11.4 Unary Operators

    function parseUnaryExpression() {
        var operator, expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }


        if (match('++') || match('--')) {
            operator = lex().value;
            expr = parseUnaryExpression();
            if (!isLeftHandSide(expr)) {
                throwError(Messages.InvalidLHSInPrefixOp);
            }
            expr = {
                type: Syntax.UpdateExpression,
                operator: operator,
                argument: expr,
                prefix: true
            };
            if (tracking) {
                finish(expr);
            }
            return expr;
        }

        if (match('+') || match('-') || match('~') || match('!')) {
            expr = {
                type: Syntax.UnaryExpression,
                operator: lex().value,
                argument: parseUnaryExpression()
            };
            if (tracking) {
                finish(expr);
            }
            return expr;
        }

        if (matchKeyword('delete') || matchKeyword('void') || matchKeyword('typeof')) {
            expr = {
                type: Syntax.UnaryExpression,
                operator: lex().value,
                argument: parseUnaryExpression()
            };
            if (tracking) {
                finish(expr);
            }
            return expr;
        }

        return parsePostfixExpression();
    }

    // 11.5 Multiplicative Operators

    function parseMultiplicativeExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseUnaryExpression();

        while (match('*') || match('/') || match('%')) {
            expr = {
                type: Syntax.BinaryExpression,
                operator: lex().value,
                left: expr,
                right: parseUnaryExpression()
            };
            if (tracking) {
                finish(expr);
            }
        }

        return expr;
    }

    // 11.6 Additive Operators

    function parseAdditiveExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseMultiplicativeExpression();

        while (match('+') || match('-')) {
            expr = {
                type: Syntax.BinaryExpression,
                operator: lex().value,
                left: expr,
                right: parseMultiplicativeExpression()
            };
            if (tracking) {
                finish(expr);
                finish = start();
            }
        }

        return expr;
    }

    // 11.7 Bitwise Shift Operators

    function parseShiftExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseAdditiveExpression();

        while (match('<<') || match('>>') || match('>>>')) {
            expr = {
                type: Syntax.BinaryExpression,
                operator: lex().value,
                left: expr,
                right: parseAdditiveExpression()
            };
            if (tracking) {
                finish(expr);
                finish = start();
            }
        }

        return expr;
    }

    // 11.8 Relational Operators

    function parseRelationalExpression() {
        var expr, finish;

        if (tracking) {
            finish = start();
        }

        expr = parseShiftExpression();

        if (match('<') || match('>') || match('<=') || match('>=')) {
            expr = {
                type: Syntax.BinaryExpression,
                operator: lex().value,
                left: expr,
                right: parseRelationalExpression()
            };
            if (tracking) {
                finish(expr);
            }
        } else if (matchKeyword('in')) {
            lex();
            expr = {
                type: Syntax.BinaryExpression,
                operator: 'in',
                left: expr,
                right: parseRelationalExpression()
            };
            if (tracking) {
                finish(expr);
            }
        } else if (matchKeyword('instanceof')) {
            lex();
            expr = {
                type: Syntax.BinaryExpression,
                operator: 'instanceof',
                left: expr,
                right: parseRelationalExpression()
            };
            if (tracking) {
                finish(expr);
            }
        }

        return expr;
    }

    // 11.9 Equality Operators

    function parseEqualityExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseRelationalExpression();

        while (match('==') || match('!=') || match('===') || match('!==')) {
            expr = {
                type: Syntax.BinaryExpression,
                operator: lex().value,
                left: expr,
                right: parseRelationalExpression()
            };
            if (tracking) {
                finish(expr);
            }
        }

        return expr;
    }

    // 11.10 Binary Bitwise Operators

    function parseBitwiseANDExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseEqualityExpression();

        while (match('&')) {
            lex();
            expr = {
                type: Syntax.BinaryExpression,
                operator: '&',
                left: expr,
                right: parseEqualityExpression()
            };
            if (tracking) {
                finish(expr);
                finish = start();
            }
        }

        return expr;
    }

    function parseBitwiseORExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseBitwiseANDExpression();

        while (match('|')) {
            lex();
            expr = {
                type: Syntax.BinaryExpression,
                operator: '|',
                left: expr,
                right: parseBitwiseANDExpression()
            };
            if (tracking) {
                finish(expr);
                finish = start();
            }
        }

        return expr;
    }

    function parseBitwiseXORExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseBitwiseORExpression();

        while (match('^')) {
            lex();
            expr = {
                type: Syntax.BinaryExpression,
                operator: '^',
                left: expr,
                right: parseBitwiseORExpression()
            };
            if (tracking) {
                finish(expr);
                finish = start();
            }
        }

        return expr;
    }

    // 11.11 Binary Logical Operators

    function parseLogicalANDExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseBitwiseXORExpression();

        while (match('&&')) {
            lex();
            expr = {
                type: Syntax.LogicalExpression,
                operator: '&&',
                left: expr,
                right: parseBitwiseXORExpression()
            };
            if (tracking) {
                finish(expr);
                finish = start();
            }
        }

        return expr;
    }

    function parseLogicalORExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseLogicalANDExpression();

        while (match('||')) {
            lex();
            expr = {
                type: Syntax.LogicalExpression,
                operator: '||',
                left: expr,
                right: parseLogicalANDExpression()
            };
            if (tracking) {
                finish(expr);
                finish = start();
            }
        }

        return expr;
    }

    // 11.12 Conditional Operator

    function parseConditionalExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseLogicalORExpression();

        if (match('?')) {
            lex();
            expr = {
                type: Syntax.ConditionalExpression,
                test: expr
            };
            expr.consequent = parseAssignmentExpression();
            expect(':');
            expr.alternate = parseAssignmentExpression();
            if (tracking) {
                finish(expr);
            }
        }

        return expr;
    }

    // 11.13 Assignment Operators

    function parseAssignmentExpression() {
        var expr, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseConditionalExpression();

        if (matchAssign()) {
            if (!isLeftHandSide(expr)) {
                throwError(Messages.InvalidLHSInAssignment);
            }
            expr = {
                type: Syntax.AssignmentExpression,
                operator: lex().value,
                left: expr,
                right: parseAssignmentExpression()
            };
            if (tracking) {
                finish(expr);
            }
        }

        return expr;
    }

    // 11.14 Comma Operator

    function parseExpression() {
        var expr, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expr = parseAssignmentExpression();

        if (match(',')) {
            expr = {
                type: Syntax.SequenceExpression,
                expressions: [ expr ]
            };

            while (index < length) {
                if (!match(',')) {
                    break;
                }
                lex();
                expr.expressions.push(parseAssignmentExpression());
            }

        }

        syntax = {
            type: Syntax.ExpressionStatement,
            expression: expr
        };

        if (tracking) {
            finish(expr);
            finish(syntax);
        }

        return syntax;
    }

    // 12.1 Block

    function parseStatementList() {
        var list = [],
            statement;

        while (index < length) {
            if (match('}')) {
                break;
            }
            statement = parseStatement();
            if (typeof statement === 'undefined') {
                break;
            }
            list.push(statement);
        }

        return list;
    }

    function parseBlock() {
        var block, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expect('{');

        block = parseStatementList();

        expect('}');

        syntax = {
            type: Syntax.BlockStatement,
            body: block
        };
        if (tracking) {
            finish(syntax);
        }
        return syntax;
    }

    // 12.2 Variable Statement

    function parseVariableDeclaration() {
        var token, id, init, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        token = lex();
        if (token.type !== Token.Identifier) {
            throwUnexpected(token);
        }

        id = {
            type: Syntax.Identifier,
            name: token.value
        };

        init = null;
        if (match('=')) {
            lex();
            init = parseAssignmentExpression();
        }

        syntax = {
            id: id,
            init: init
        };

        if (tracking) {
            finishUsingToken(id, token);
            finish(syntax);
        }

        return syntax;
    }

    function parseVariableDeclarationList() {
        var list = [];

        while (index < length) {
            list.push(parseVariableDeclaration());
            if (!match(',')) {
                break;
            }
            lex();
        }

        return list;
    }

    function parseVariableStatement() {
        var declarations, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('var');

        declarations = parseVariableDeclarationList();

        syntax = {
            type: Syntax.VariableDeclaration,
            declarations: declarations,
            kind: 'var'
        };

        if (tracking) {
            finish(syntax);
        }

        consumeSemicolon();

        return syntax;
    }

    // http://wiki.ecmascript.org/doku.php?id=harmony:let.
    // Warning: This is experimental and not in the specification yet.

    function parseLetStatement() {
        var declarations, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('let');

        declarations = parseVariableDeclarationList();

        syntax = {
            type: Syntax.VariableDeclaration,
            declarations: declarations,
            kind: 'let'
        };

        if (tracking) {
            finish(syntax);
        }

        consumeSemicolon();
        return syntax;
    }

    // 12.3 Empty Statement

    function parseEmptyStatement() {
        var syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expect(';');

        syntax = {
            type: Syntax.EmptyStatement
        };

        if (tracking) {
            finish(syntax);
        }

        return syntax;
    }

    // 12.4 Expression Statement

    function parseExpressionStatement() {
        var expr = parseExpression();

        consumeSemicolon();

        return expr;
    }

    // 12.5 If statement

    function parseIfStatement() {
        var test, consequent, alternate, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('if');

        expect('(');

        test = parseExpression().expression;

        expect(')');

        consequent = parseStatement();

        if (matchKeyword('else')) {
            lex();
            alternate = parseStatement();
        } else {
            alternate = null;
        }

        syntax = {
            type: Syntax.IfStatement,
            test: test,
            consequent: consequent,
            alternate: alternate
        };

        if (tracking) {
            finish(syntax);
        }

        return syntax;
    }

    // 12.6 Iteration Statements

    function parseDoWhileStatement() {
        var body, test, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('do');

        body = parseStatement();

        expectKeyword('while');

        expect('(');

        test = parseExpression().expression;

        expect(')');

        syntax = {
            type: Syntax.DoWhileStatement,
            body: body,
            test: test
        };

        if (tracking) {
            finish(syntax);
        }

        consumeSemicolon();

        return syntax;
    }

    function parseWhileStatement() {
        var test, body, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('while');

        expect('(');

        test = parseExpression().expression;

        expect(')');

        body = parseStatement();

        syntax = {
            type: Syntax.WhileStatement,
            test: test,
            body: body
        };

        if (tracking) {
            finish(syntax);
        }

        return syntax;
    }

    function parseForStatement() {
        var kind, init, test, update, left, right, body, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        init = test = update = null;

        expectKeyword('for');

        expect('(');

        if (match(';')) {
            lex();
        } else {
            if (matchKeyword('var') || matchKeyword('let')) {
                kind = lex().value;
                init = {
                    type: Syntax.VariableDeclaration,
                    declarations: parseVariableDeclarationList(),
                    kind: kind
                };

                if (tracking) {
                    finish(init);
                }

                if (matchKeyword('in')) {
                    lex();
                    left = init;
                    right = parseExpression().expression;
                    init = null;
                }
            } else {
                init = parseExpression().expression;
            }

            if (typeof left === 'undefined') {
                if (init.hasOwnProperty('operator') && init.operator === 'in') {
                    left = init.left;
                    right = init.right;
                    init = null;
                    if (!isLeftHandSide(left)) {
                        throwError(Messages.InvalidLHSInForIn);
                    }
                } else {
                    expect(';');
                }
            }
        }

        if (typeof left === 'undefined') {

            if (!match(';')) {
                test = parseExpression().expression;
            }
            expect(';');

            if (!match(')')) {
                update = parseExpression().expression;
            }
        }

        expect(')');

        body = parseStatement();

        if (typeof left === 'undefined') {
            syntax = {
                type: Syntax.ForStatement,
                init: init,
                test: test,
                update: update,
                body: body
            };
            if (tracking) {
                finish(syntax);
            }
            return syntax;
        }

        syntax = {
            type: Syntax.ForInStatement,
            left: left,
            right: right,
            body: body,
            each: false
        };

        if (tracking) {
            finish(syntax);
        }

        return syntax;
    }

    // 12.7 The continue statement

    function parseContinueStatement() {
        var token, label = null, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('continue');

        // Optimize the most common form: 'continue;'.
        if (source[index] === ';') {
            lex();
            syntax = {
                type: Syntax.ContinueStatement,
                label: null
            };
            if (tracking) {
                finish(syntax);
            }
            return syntax;
        }

        if (peekLineTerminator()) {
            syntax = {
                type: Syntax.ContinueStatement,
                label: null
            };
            if (tracking) {
                finish(syntax);
            }
            return syntax;
        }

        token = lookahead();
        if (token.type === Token.Identifier) {
            lex();
            label = {
                type: Syntax.Identifier,
                name: token.value
            };
            if (tracking) {
                finishUsingToken(label, token);
            }
        }

        syntax = {
            type: Syntax.ContinueStatement,
            label: label
        };

        if (tracking) {
            finish(syntax);
        }

        consumeSemicolon();

        return syntax;
    }

    // 12.8 The break statement

    function parseBreakStatement() {
        var token, label = null, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('break');

        // Optimize the most common form: 'break;'.
        if (source[index] === ';') {
            lex();
            return {
                type: Syntax.BreakStatement,
                label: null
            };
        }

        if (peekLineTerminator()) {
            return {
                type: Syntax.BreakStatement,
                label: null
            };
        }

        token = lookahead();
        if (token.type === Token.Identifier) {
            lex();
            label = {
                type: Syntax.Identifier,
                name: token.value
            };
            if (tracking) {
                finishUsingToken(label, token);
            }
        }

        syntax = {
            type: Syntax.BreakStatement,
            label: label
        };

        if (tracking) {
            finish(syntax);
        }

        consumeSemicolon();

        return syntax;
    }

    // 12.9 The return statement

    function parseReturnStatement() {
        var token, argument = null, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('return');

        // 'return' followed by a space and an identifier is very common.
        if (source[index] === ' ') {
            if (isIdentifierStart(source[index + 1])) {
                argument = parseExpression().expression;
                syntax = {
                    type: Syntax.ReturnStatement,
                    argument: argument
                };
                if (tracking) {
                    finish(syntax);
                }
                consumeSemicolon();
                return syntax;
            }
        }

        if (peekLineTerminator()) {
            syntax = {
                type: Syntax.ReturnStatement,
                argument: null
            };
            if (tracking) {
                finish(syntax);
            }
            return syntax;
        }

        if (!match(';')) {
            token = lookahead();
            if (!match('}') && token.type !== Token.EOF) {
                argument = parseExpression().expression;
            }
        }

        syntax = {
            type: Syntax.ReturnStatement,
            argument: argument
        };

        if (tracking) {
            finish(syntax);
        }

        consumeSemicolon();

        return syntax;
    }

    // 12.10 The with statement

    function parseWithStatement() {
        var object, body, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('with');

        expect('(');

        object = parseExpression().expression;

        expect(')');

        body = parseStatement();

        syntax = {
            type: Syntax.WithStatement,
            object: object,
            body: body
        };

        if (tracking) {
            finish(syntax);
        }

        return syntax;
    }

    // 12.10 The swith statement

    function parseSwitchConsequent() {
        var consequent = [], statement;

        while (index < length) {
            if (match('}') || matchKeyword('default') || matchKeyword('case')) {
                break;
            }
            statement = parseStatement();
            if (typeof statement === 'undefined') {
                break;
            }
            consequent.push(statement);
        }

        return consequent;
    }

    function parseSwitchStatement() {
        var discriminant,
            cases,
            test,
            consequent,
            statement,
            syntax,
            finish,
            nestedSyntax,
            nestedFinish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('switch');

        expect('(');

        discriminant = parseExpression().expression;

        expect(')');

        expect('{');

        if (match('}')) {
            lex();
            syntax = {
                type: Syntax.SwitchStatement,
                discriminant: discriminant
            };
            if (tracking) {
                finish(syntax);
            }
            return syntax;
        }

        cases = [];

        while (index < length) {
            if (match('}')) {
                break;
            }
            if (tracking) {
                nestedFinish = start();
            }

            if (matchKeyword('default')) {
                lex();
                test = null;
            } else {
                expectKeyword('case');
                test = parseExpression().expression;
            }
            expect(':');

            nestedSyntax = {
                type: Syntax.SwitchCase,
                test: test,
                consequent: parseSwitchConsequent()
            };

            if (tracking) {
                finish(nestedSyntax);
            }

            cases.push(nestedSyntax);
        }

        expect('}');

        syntax = {
            type: Syntax.SwitchStatement,
            discriminant: discriminant,
            cases: cases
        };

        if (tracking) {
            finish(syntax);
        }

        return syntax;
    }

    // 12.13 The throw statement

    function parseThrowStatement() {
        var argument, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('throw');

        if (peekLineTerminator()) {
            throwError(Messages.NewlineAfterThrow);
        }

        argument = parseExpression().expression;

        syntax = {
            type: Syntax.ThrowStatement,
            argument: argument
        };

        if (tracking) {
            finish(syntax);
        }

        consumeSemicolon();

        return syntax;
    }

    // 12.14 The try statement

    function parseTryStatement() {
        var block,
            handlers = [],
            param,
            finalizer = null,
            syntax,
            finish,
            nestedSyntax,
            nestedFinish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('try');

        block = parseBlock();

        if (tracking) {
            nestedFinish = start();
        }

        if (matchKeyword('catch')) {
            lex();
            expect('(');
            if (!match(')')) {
                param = parseExpression().expression;
            }
            expect(')');

            nestedSyntax = {
                type: Syntax.CatchClause,
                param: param,
                guard: null,
                body: parseBlock()
            };
            if (tracking) {
                nestedFinish(nestedSyntax);
            }
            handlers.push(nestedSyntax);
        }

        if (matchKeyword('finally')) {
            lex();
            finalizer = parseBlock();
        }

        if (handlers.length === 0 && !finalizer) {
            throwError(Messages.NoCatchOrFinally);
        }

        syntax = {
            type: Syntax.TryStatement,
            block: block,
            handlers: handlers,
            finalizer: finalizer
        };
        if (tracking) {
            finish(syntax);
        }
        return syntax;
    }

    // 12.15 The debugger statement

    function parseDebuggerStatement() {
        var syntax, finish;

        if (tracking) {
            skipComment();
        }

        finish = start();

        expectKeyword('debugger');

        syntax = {
            type: Syntax.DebuggerStatement
        };

        if (tracking) {
            finish(syntax);
        }

        consumeSemicolon();

        return syntax;
    }

    // 12 Statements

    function parseStatement() {
        var token, stat, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        token = lookahead();

        if (token.type === Token.EOF) {
            return;
        }

        if (token.type === Token.Punctuator) {
            switch (token.value) {
            case ';':
                return parseEmptyStatement();
            case '{':
                return parseBlock();
            case '(':
                return parseExpressionStatement();
            default:
                break;
            }
        }

        if (token.type === Token.Keyword) {
            switch (token.value) {
            case 'break':
                return parseBreakStatement();
            case 'continue':
                return parseContinueStatement();
            case 'debugger':
                return parseDebuggerStatement();
            case 'do':
                return parseDoWhileStatement();
            case 'for':
                return parseForStatement();
            case 'if':
                return parseIfStatement();
            case 'let':
                return parseLetStatement();
            case 'return':
                return parseReturnStatement();
            case 'switch':
                return parseSwitchStatement();
            case 'throw':
                return parseThrowStatement();
            case 'try':
                return parseTryStatement();
            case 'var':
                return parseVariableStatement();
            case 'while':
                return parseWhileStatement();
            case 'with':
                return parseWithStatement();
            default:
                break;
            }
        }

        stat = parseExpression();

        if (stat.expression.type === Syntax.FunctionExpression) {
            if (stat.expression.id !== null) {
                syntax = {
                    type: Syntax.FunctionDeclaration,
                    id: stat.expression.id,
                    params: stat.expression.params,
                    body: stat.expression.body
                };
                if (tracking) {
                    finish(syntax);
                }
                return syntax;
            }
        }

        // 12.12 Labelled Statements
        if ((stat.expression.type === Syntax.Identifier) && match(':')) {
            lex();
            syntax = {
                type: Syntax.LabeledStatement,
                label: stat.expression,
                body: parseStatement()
            };
            if (tracking) {
                finish(syntax);
            }
            return syntax;
        }

        consumeSemicolon();

        return stat;
    }

    // 13 Function Definition

    function parseFunctionDeclaration() {
        var token, id = null, param, params = [], body, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('function');

        token = lex();
        if (token.type !== Token.Identifier) {
            throwUnexpected(token);
        }
        id = {
            type: Syntax.Identifier,
            name: token.value
        };
        if (tracking) {
            finishUsingToken(id, token);
        }

        expect('(');

        if (!match(')')) {
            while (index < length) {
                token = lex();
                if (token.type !== Token.Identifier) {
                    throwUnexpected(token);
                }
                param = {
                    type: Syntax.Identifier,
                    name: token.value
                };
                if (tracking) {
                    finishUsingToken(param, token);
                }
                params.push(param);
                if (match(')')) {
                    break;
                }
                expect(',');
            }
        }

        expect(')');

        body = parseBlock();

        syntax = {
            type: Syntax.FunctionDeclaration,
            id: id,
            params: params,
            body: body
        };
        if (tracking) {
            finish(syntax);
        }
        return syntax;
    }

    function parseFunctionExpression() {
        var token, id = null, param, params = [], body, syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        expectKeyword('function');

        if (!match('(')) {
            token = lex();
            if (token.type !== Token.Identifier) {
                throwUnexpected(token);
            }
            id = {
                type: Syntax.Identifier,
                name: token.value
            };
            if (tracking) {
                finishUsingToken(id, token);
            }
        }

        expect('(');

        if (!match(')')) {
            while (index < length) {
                token = lex();
                if (token.type !== Token.Identifier) {
                    throwUnexpected(token);
                }
                param = {
                    type: Syntax.Identifier,
                    name: token.value
                };
                if (tracking) {
                    finishUsingToken(param, token);
                }
                params.push(param);
                if (match(')')) {
                    break;
                }
                expect(',');
            }
        }

        expect(')');

        body = parseBlock();

        syntax = {
            type: Syntax.FunctionExpression,
            id: id,
            params: params,
            body: body
        };

        if (tracking) {
            finish(syntax);
        }

        return syntax;
    }

    // 14 Program

    function parseSourceElement() {
        var token;

        token = lookahead();
        if (token.type === Token.EOF) {
            return;
        }

        if (matchKeyword('function')) {
            return parseFunctionDeclaration();
        }

        return parseStatement();
    }

    function parseSourceElements() {
        var sourceElement, sourceElements = [];

        while (index < length) {
            sourceElement = parseSourceElement();
            if (typeof sourceElement === 'undefined') {
                break;
            }
            sourceElements.push(sourceElement);
        }
        return sourceElements;
    }

    function parseProgram() {
        var syntax, finish;

        if (tracking) {
            skipComment();
            finish = start();
        }

        syntax = {
            type: Syntax.Program,
            body: parseSourceElements()
        };

        if (tracking) {
            finish(syntax);
        }

        return syntax;
    }

    // The following functions are needed only when the option to preserve
    // the comments is active.

    function scanComment() {
        var comment,
            ch,
            blockComment,
            lineComment,
            startIndex,
            startLineIndex,
            finish;

        comment = '';
        blockComment = false;
        lineComment = false;

        while (index < length) {
            ch = source[index];

            if (lineComment) {
                ch = nextChar();
                if (isLineTerminator(ch)) {
                    lineComment = false;
                    lineNumber += 1;
                    lineIndex = index + 1;
                    if (!lookingAhead) {
                        comment = {
                            type: 'Line',
                            value: comment
                        };
                        if (tracking) {
                            finish(comment);
                            if (trackingRange) {
                                comment.prefixLength = startIndex - startLineIndex;
                            }
                        }
                        extra.comments.push(comment);
                    }
                    comment = '';
                } else {
                    comment += ch;
                }
            } else if (blockComment) {
                ch = nextChar();
                comment += ch;
                if (ch === '*') {
                    ch = source[index];
                    if (ch === '/') {
                        comment = comment.substr(0, comment.length - 1);
                        blockComment = false;
                        nextChar();
                        if (!lookingAhead) {
                            comment = {
                                type: 'Block',
                                value: comment
                            };
                            if (tracking) {
                                finish(comment);
                                if (trackingRange) {
                                    comment.prefixLength = startIndex - startLineIndex;
                                }
                            }
                            extra.comments.push(comment);
                        }
                        comment = '';
                    }
                } else if (isLineTerminator(ch)) {
                    lineNumber += 1;
                    lineIndex = index + 1;
                }
            } else if (ch === '/') {
                ch = source[index + 1];
                if (ch === '/') {
                    startIndex = index;
                    startLineIndex = lineIndex;
                    finish = start();
                    nextChar();
                    nextChar();
                    lineComment = true;
                } else if (ch === '*') {
                    startIndex = index;
                    startLineIndex = lineIndex;
                    finish = start();
                    nextChar();
                    nextChar();
                    blockComment = true;
                } else {
                    break;
                }
            } else if (isWhiteSpace(ch)) {
                nextChar();
            } else if (isLineTerminator(ch)) {
                nextChar();
                lineNumber += 1;
                lineIndex = index;
            } else {
                break;
            }
        }

        if (!lookingAhead && comment.length > 0) {
            extra.comments.push(finish({
                type: (blockComment) ? 'Block' : 'Line',
                value: comment
            }));
        }
    }

    function tokenTypeAsString(type) {
        switch (type) {
        case Token.BooleanLiteral: return 'Boolean';
        case Token.Identifier: return 'Identifier';
        case Token.Keyword: return 'Keyword';
        case Token.NullLiteral: return 'Null';
        case Token.NumericLiteral: return 'Numeric';
        case Token.Punctuator: return 'Punctuator';
        case Token.StringLiteral: return 'String';
        default:
            throw new Error('Unknown token type');
        }
    }

    function lexWithAnnotations() {
        var token,
            extraToken,
            initialIndex,
            initialLineIndex,
            initialLineNumber;

        if (buffer) {
            index = buffer.finalIndex;
            lineIndex = buffer.finalLineIndex;
            lineNumber = buffer.finalLineNumber;
            token = buffer;
            buffer = null;
            return token;
        }

        buffer = null;
        skipComment();

        initialIndex = index;
        initialLineIndex = lineIndex;
        initialLineNumber = lineNumber;

        token = advance();

        token.index = initialIndex;
        token.lineIndex = initialLineIndex;
        token.lineNumber = initialLineNumber;

        if (token.type !== Token.EOF) {
            extraToken = {
                type: tokenTypeAsString(token.type),
                value: source.slice(initialIndex, index)
            };
            if (trackingRange) {
                extraToken.range = token.range;
            }
            if (trackingLoc) {
                extraToken.loc = token.loc;
            }
            extra.tokens.push(extraToken);
        }

        lastToken = token;

        return token;
    }

    function scanRegExpWithAnnotations() {
        var pos, regex, token, finish;

        skipComment();

        finish = start();
        pos = index;
        regex = extra.scanRegExp();

        // Pop the previous token, which is likely '/' or '/='
        if (lastToken) {
            if (lastToken.index === pos && lastToken.type === Token.Punctuator) {
                if (lastToken.value === '/' || lastToken.value === '/=') {
                    extra.tokens.pop();
                }
            }
        }

        extra.tokens.push(finish({
            type: 'RegularExpression',
            value: regex.literal
        }));

        return regex;
    }

    function postprocessCommentPrefix(program) {
        program.comments.forEach(function (comment) {
            var stop = comment.range[0];
            var start = stop - comment.prefixLength;
            comment.prefix = source.slice(start, stop);
        });
    }

    function patch(options) {
        extra = {};
        tracking = false;

        if (typeof options.comment === 'boolean' && options.comment) {
            extra.skipComment = skipComment;
            skipComment = scanComment;
            extra.comments = [];
            tracking = true;
        }

        if (typeof options.range === 'boolean' && options.range) {
            extra.trackingRange = trackingRange;
            trackingRange = true;
            tracking = true;
        }

        if (typeof options.loc === 'boolean' && options.loc) {
            extra.trackingLoc = trackingLoc;
            trackingLoc = true;
            tracking = true;
        }

        if (typeof options.source === 'string') {
            extra.sourceName = sourceName;
            sourceName = options.source;
        }

        if (typeof options.tokens === 'boolean' && options.tokens) {
            extra.lex = lex;
            extra.scanRegExp = scanRegExp;

            lex = lexWithAnnotations;
            scanRegExp = scanRegExpWithAnnotations;

            extra.tokens = [];
        }

    }

    function unpatch() {
        if (typeof extra.skipComment === 'function') {
            skipComment = extra.skipComment;
        }

        if (typeof extra.lex === 'function') {
            lex = extra.lex;
        }

        trackingRange = extra.trackingRange;
        trackingLoc = extra.trackingLoc;
        sourceName = extra.sourceName;

        if (typeof extra.scanRegExp === 'function') {
            scanRegExp = extra.scanRegExp;
        }

        extra = {};
    }

    function parse(code, opt) {
        var options, program;

        options = opt || {};

        source = code;
        index = 0;
        lineIndex = 0;
        lineNumber = (source.length > 0) ? 1 : 0;
        length = source.length;
        buffer = null;
        lastToken = null;
        lookingAhead = false;

        patch(options);
        try {
            program = parseProgram();
            if (typeof extra.comments !== 'undefined') {
                program.comments = extra.comments;
            }
            if (typeof extra.tokens !== 'undefined') {
                program.tokens = extra.tokens;
            }
            if (options.commentPrefix) {
                postprocessCommentPrefix(program);
            }
        } catch (e) {
            throw e;
        } finally {
            unpatch();
        }

        return program;
    }

    // Executes f on the object and its children (recursively).

    function visitPreorder(object, f) {
        var key, child;

        if (f(object) === false) {
            return;
        }
        for (key in object) {
            if (object.hasOwnProperty(key)) {
                child = object[key];
                if (typeof child === 'object' && child !== null) {
                    visitPreorder(child, f);
                }
            }
        }
    }

    // XXX this code is dead, was used in range postprocessing
    function visitPostorder(object, f) {
        var key, child;

        for (key in object) {
            if (object.hasOwnProperty(key)) {
                child = object[key];
                if (typeof child === 'object' && child !== null) {
                    visitPostorder(child, f);
                }
            }
        }
        f(object);
    }

    function traverse(code, options, f) {
        var program;

        if (typeof options === 'undefined') {
            throw new Error('Wrong use of traverse() function');
        }

        if (typeof f === 'undefined') {
            f = options;
            options = {};
        }

        program = parse(code, options);
        visitPreorder(program, f);

        return program;
    }

    // Sync with package.json.
    exports.version = '0.9.4';

    exports.parse = parse;
    exports.traverse = traverse;

}(typeof exports === 'undefined' ? (esprima = {}) : exports));
