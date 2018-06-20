#!/usr/bin/env lua

-- Lexical analyzer for Dugong files. Used by userlexer.lua.
-- Dustin Fast
-- Spring, 2018


----------------------
--  Lexit Module  --
----------------------
local lexit = {}  -- This module

lexit.KEY = 1           -- Numeric constants representing lexeme categories
lexit.ID = 2
lexit.NUMLIT = 3
lexit.STRLIT = 4
lexit.OP = 5
lexit.PUNCT = 6
lexit.MAL = 7

-- Lxeme categories. Indices align with category returned by lexit.lex.getNextLexeme()
lexit.catnames = {
    "Keyword",
    "Identifier",
    "NumericLiteral",
    "StringLiteral",
    "Operator",
    "Punctuation",
    "Malformed"}

-- When preferOpFlag == true, Lexer will assume any single char operator in
-- PREFFERED_OPERATORS it encounters on its next iteration to be a lone operator. 
-- Note: preferOpFlag resets to false at end of each lexer iteration.
local preferOpFlag = false

-- Prefer operator function. Sets preferOpFlag = true
function lexit.preferOp()
    preferOpFlag = true
end


----------------------
--    The Lexer     --
----------------------
-- The Lexer is written as a state based machine.
-- Returns an iterator
-- Iterator returns lexeme (string), lexeme_category (int)
function lexit.lex(progstr)
    
    ------------------------------------
    -- lexit.lex Constant defs        --
    ------------------------------------
    local DONE = 0          -- State_handlers list index constants
    local START = 1
    local LETTER = 2
    local STRLIT = 3
    local OP = 4
    local NUMLIT = 5
    local EXPONENT = 6

    -- Keyword and Operator list constants
    local KEYWORDS = {'call', 'cr', 'else', 'elseif', 'end', 'false', 'func',
                        'if', 'input', 'print', 'true', 'while'}
    local OPERATORS = {'=', '&&', '||', '!', '==', '!=', '<', '<=', '>', '>=',
                        '+', '-', '*', '/', '%', '[', ']', ';'}
    local PREFERRED_OPERATORS = {'+', '-'} -- may contain single char operators only
    
    ------------------------------------
    -- lexit.lex cosvariable defs --
    ------------------------------------
    local curr_index        -- Index of next character in progstr. 
                            -- At any time will either be first character of the next lexeme
                            -- or progstr:len()+1
    local curr_state        -- Current state for our state machine
    local lexstr            -- The lexeme builder string.
    local category          -- Category of lexeme, an int, set on curr_state == DONE. 
    local state_handlers    -- State handler functions table. Populated in lexit.lex body, below.


    --------------------------------
    -- lexit.lex helper functions --
    --------------------------------

    --Returns true iff string s is a "char". I.e. it is a string of length one
    local function isChar(s)
        return s:len() == 1
    end 

    -- Returns true iff char c is [a-zA-z]
    local function isAlpha(c)
        return isChar(c) and ((c >= "A" and c <= "Z") or (c >= "a" and c <= "z"))
    end

    -- Returns true if char c is a digit character
    local function isDigit(c)
        return isChar(c) and (c >= "0" and c <= "9")
    end

    -- Returns true iff char c is whitespace (blank, tab, carriage return, or formfeed)
    local function isWhitespace(c)
        return isChar(c) and (c == " " or c == "\t" or c == "\r" or c == "\f" or c == "\n")
    end

    -- Returns true iff char c is a valid char in our language
    local function isLegal(c)
        return isChar(c) and (isWhitespace(c) or (string.byte(c) >= 32 and string.byte(c) <= 126))
    end

    -- Returns true iff string s is a keyword in our language
    local function isKeyword(s)
        for i = 1, #KEYWORDS do
            if KEYWORDS[i] == s then
                return true
            end
        end  
    end

    -- Returns true iff char c is a preffered operator in our language. 
    local function isPrefferedOperator(c)
        for i = 1, #PREFERRED_OPERATORS do
            if PREFERRED_OPERATORS[i] == c then
                return true
            end
        end  
    end

    -- Returns true iff string s is a single operator in our language. 
    local function isSingleOperator(s)
        for i = 1, #OPERATORS do
            if OPERATORS[i]:len() == 1 and OPERATORS[i] == s then
                return true
            end
        end  
    end

    local function isDoubleOperator(s)
        for i = 1, #OPERATORS do
            if OPERATORS[i]:len() == 2 and OPERATORS[i] == s then
                return true
            end
        end  
    end

    -- Returns true iff char c might be the start of an operator in our language.
    local function isMaybeOperator(c)
        if not isChar(c) then
            return nil
        end

        for i = 1, #OPERATORS do
            if OPERATORS[i]:sub(1,1) == c then
                return true
            end
        end  
    end
    
    -- Returns progstr[curr_index] or empty string if curr_index > progstr:len()
    local function currChar()
        return progstr:sub(curr_index, curr_index)
    end

    -- Returns progstr[curr_index+1] or empty string if curr_index+1 > progstr:len()    
    local function nextChar()
        return progstr:sub(curr_index+1, curr_index+1)
    end

    -- Returns progstr[curr_index+2] or empty string if curr_index+2 > progstr:len()    
    local function nextNextChar()
        return progstr:sub(curr_index+2, curr_index+2)
    end

    -- Increments curr_index without adding progstr[curr_index] to lexstr
    local function dropCurrMoveNext()
        curr_index = curr_index+1
    end

    -- Adds progstr[curr_index] to lexstr then increments curr_index
    local function addCurrMoveNext()
        lexstr = lexstr .. currChar()
        curr_index = curr_index+1
    end

    -- Returns true iff we are past the last char of progstr (i.e. currChar() == '') 
    local function isEnd()
        return currChar() == ''
    end

    -- Skip whitespace and comments, effectively moving curr_index to the beginning of
    -- the next lexeme, or to progstr:len()+1, whichever comes first.
    local function skipWhitespace()
        -- Skip whitespace
        while isWhitespace(currChar()) do
            dropCurrMoveNext()
        end

        -- Skip comments. Comments start with # and end with newline
        if currChar() == "#" then
            while currChar() ~= '\n' and not isEnd() do
                dropCurrMoveNext()
            end
            dropCurrMoveNext() -- remove newline char ending comment
            skipWhitespace() -- Remove trailing whitespace from comments
        end

        
        -- End of progstr
        if isEnd() then
            return
        end

    end


    ---------------------------------------
    -- lexit.lex state handler functions --
    ---------------------------------------
    -- Each state handler function handles that specific state. 
    -- Ex: handle_START() handles the start state and can be called via state_handlers[

    local function handle_DONE()
        io.write("ERROR: 'DONE' state should not be handled\n")
        assert(0)
    end

    -- Lexer starts each iteration here and changes state according to curr char.
    -- Note we always MoveNext() first thing in handle_START()
    local function handle_START()
        start_char = currChar() -- Note start char
        addCurrMoveNext()       -- Add start char to lexstr and advance curr_index
        
        if not isLegal(start_char) then 
            curr_state = DONE
            category = lexit.MAL

        -- handle Identifiers (or possibly keywords)
        elseif isAlpha(start_char) or start_char == "_" then
            curr_state = LETTER
        
        -- handle string literals (either ' or " can begin a strlit)
        elseif start_char == "'" or start_char == '"' then
            curr_state = STRLIT

        -- handle preffered operators
        elseif preferOpFlag and isPrefferedOperator(start_char) then
            category = lexit.OP
            curr_state = DONE

        -- handle non-preffered operators
        elseif isMaybeOperator(start_char) then
            curr_state = OP

        -- handle digits    
        elseif isDigit(start_char) then
            curr_state = NUMLIT

        -- anything else we encounter is malformed or punctuation
        else
            category = lexit.PUNCT
            curr_state = DONE
        end
    end

    local function handle_LETTER()
        if isAlpha(currChar()) or isDigit(currChar()) or currChar() == "_" then
            addCurrMoveNext()
        else
            if isKeyword(lexstr) then
                category = lexit.KEY
            else
                category = lexit.ID
            end
            curr_state = DONE            
        end
    end

    local function handle_STRLIT()
        -- Denote start char because it will serve as our break char
        endchar = lexstr

        while currChar() ~= endchar do
            -- if we fall off progstr or encountered a newline, strlit is malformed
            if currChar() == '' or currChar() == '\n' then
                addCurrMoveNext() -- add the newline, if any, to the malformed string
                category = lexit.MAL
                curr_state = DONE
                return
            end

            addCurrMoveNext() -- add everything between quotes to lexstr
        end

        addCurrMoveNext() -- add the trailing quote to lexstr
        
        category = lexit.STRLIT
        curr_state = DONE

    end

    local function handle_OP()
        -- If we're actually looking at a NUMLIT
        if isDigit(currChar()) and (lexstr == '+' or lexstr == '-') then
            addCurrMoveNext()
            curr_state = NUMLIT
        
        -- else, looking at OP or PUNCT
        else
            --handle two-character operators
            if isDoubleOperator(lexstr .. currChar()) then
                addCurrMoveNext()
                category = lexit.OP
            elseif isSingleOperator(lexstr) then
                category = lexit.OP
            else
                category = lexit.PUNCT
            end

            curr_state = DONE
        end 
    end

    local function handle_NUMLIT()
        if isDigit(currChar()) then
            addCurrMoveNext()
        elseif currChar():lower() == 'e' then
            -- handle NUMLIT with implicitly positive exponent
            if isDigit(nextChar()) then
                addCurrMoveNext() -- add the e
                addCurrMoveNext() -- add the digit
                curr_state = EXPONENT
            
            -- handle NUMLIT with explicitly positive exponent
            elseif nextChar() == '+' and isDigit(nextNextChar()) then
                addCurrMoveNext() -- add the e
                addCurrMoveNext() --add the +
                addCurrMoveNext() --add the digit
                curr_state = EXPONENT                

            -- handle the end of the NUMLIT
            else 
                category = lexit.NUMLIT
                curr_state = DONE
            end
        else
            category = lexit.NUMLIT
            curr_state = DONE
        end
    end

    local function handle_EXPONENT()
        if isDigit(currChar()) then
            addCurrMoveNext()
        else 
            category = lexit.NUMLIT
            curr_state = DONE
        end
    end

    
    -- Ini curr_index and  state_handlers list.
    curr_index = 1
    state_handlers = {
        [DONE] = handle_DONE,
        [START] = handle_START,
        [LETTER] = handle_LETTER,
        [STRLIT] = handle_STRLIT,
        [OP] = handle_OP,
        [NUMLIT] = handle_NUMLIT,
        [EXPONENT]=handle_EXPONENT
    }

    --------------
    -- Iterator --
    --------------
    -- Returns (lexstr, category), or (nil, nil) if done iterating.
    local function getNextLexeme(dummy1, dummy2)
        skipWhitespace() -- advance curr_index past leading whitespaces

        -- If we are past progstr:len() end iteration
        if curr_index > progstr:len() then
            preferOpFlag = false -- reset to false after the last iter
            return nil, nil
        end

        -- Form the next lexeme in progstr
        lexstr = ""
        curr_state = START
        while curr_state ~= DONE do
            state_handlers[curr_state]()
            preferOpFlag = false -- reset to false after each iter
        end
        skipWhitespace() -- advance curr_index past trailing whitepaces
        
        return lexstr, category
    end
    
    -- return iterator
    return getNextLexeme, nil, nil 
end

return lexit -- return the module table to the importer

