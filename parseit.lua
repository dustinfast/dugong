-- parseit.lua, A Recursive-Descent parser for "Dugong".
-- Requires lexit.lua, a lexical analyzer for "Dugong".
-- CSCE A3331, Assignment 4
-- Dustin Fast
-- Spring, 2018
-- Adapted from rdparser4.lua, Glenn G. Chappell 2018


-------------
-- Grammar --
-------------
-- Note: Operators (+ - * /) are left-associative.
-- Start Symbol = program
-- (G1): program  ->  stmt_list
-- (G2): stmt_list  ->  { statement }
-- (G3): statement  ->  'input' lvalue
-- (G4):  	|  	'print' print_arg { ';' print_arg }
-- (G5):  	|  	'func' ID stmt_list 'end'
-- (G6):  	|  	'call' ID
-- (G7):  	|  	'if' expr stmt_list { 'elseif' expr stmt_list } [ 'else' stmt_list ] 'end'
-- (G8):  	|  	'while' expr stmt_list 'end'
-- (G9):  	|  	lvalue '=' expr
-- (G10): print_arg  ->  'cr'
-- (G11):  	|  	STRLIT
-- (G12):  	|  	expr
-- (G13): expr  ->  comp_expr { ( '&&' | '||' ) comp_expr }
-- (G14): comp_expr  ->  '!' comp_expr
-- (G15):  	|  	arith_expr { ( '==' | '!=' | '<' | '<=' | '>' | '>=' ): arith_expr }
-- (G16): arith_expr  ->  term { ( '+' | '-' ) term }
-- (G17): term  ->  factor { ( '*' | '/' | '%' ) factor }
-- (G18): factor  ->  '(' expr ')'
-- (G19):  	|  	( 'true' | 'false' )
-- (G20):  	|  	( '+' | '-' ) factor
-- (G21):  	|  	'call' ID
-- (G22):  	|  	NUMLIT
-- (G23):  	|  	lvalue
-- (G24): lvalue  ->  ID [ '[' expr ']' ]


-----------------------
-- AST Specification --
-----------------------
-- - For an ID, the AST is { SIMPLE_VAR, SS }, where SS is the string
--   form of the lexeme.
-- - For a NUMLIT, the AST is { NUMLIT_VAL, SS }, where SS is the string
--   form of the lexeme.
-- - For expr -> term, then AST for the expr is the AST for the term,
--   and similarly for term -> factor.
-- - Let X, Y be expressions with ASTs XT, YT, respectively.
--   - The AST for ( X ) is XT.
--   - The AST for X + Y is { { BIN_OP, "+" }, XT, YT }. For multiple
--     "+" operators, left-asociativity is reflected in the AST. And
--     similarly for the other operators.


-- Import Lexer module
lexer = require "lexit" 

-- Define this module
local parseit = {}  

----------------------
-- Module Variables --
----------------------
-- For lexer iteration
local iter          -- Iterator returned by lexer
local state         -- State for above iterator (maybe not used)
local lexer_out_s   -- Return value #1 from above iterator
local lexer_out_c   -- Return value #2 from above iterator

-- For current lexeme
local curr_lexstr = ""   -- String form of current lexeme
local curr_lexcat = 0    -- Category of current lexeme:
                         --  one of categories below,
                         --  or 0 for past the end or if parser un-initialized
                            -- lexer.KEY = 1           
                            -- lexer.ID = 2
                            -- lexer.NUMLIT = 3
                            -- lexer.STRLIT = 4
                            -- lexer.OP = 5
                            -- lexer.PUNCT = 6
                            -- lexer.MAL = 7

-- Symbolic Constants for AST
local STMT_LIST   = 1
local INPUT_STMT  = 2
local PRINT_STMT  = 3
local FUNC_STMT   = 4
local CALL_FUNC   = 5
local IF_STMT     = 6
local WHILE_STMT  = 7
local ASSN_STMT   = 8
local CR_OUT      = 9
local STRLIT_OUT  = 10
local BIN_OP      = 11
local UN_OP       = 12
local NUMLIT_VAL  = 13
local BOOLLIT_VAL = 14
local SIMPLE_VAR  = 15
local ARRAY_VAR   = 16

-----------------------
-- Utility Functions --
-----------------------

-- Calls lexer.prefer() iff appropriate.
-- Note the conditions for calling preferOp are defined here
local function doPreferOp()
    if curr_lexcat == lexer.NUMLIT or 
        curr_lexcat == lexer.ID or
        curr_lexstr == ']' or
        curr_lexstr == ')' then
        --print('calling lexer.prefer()')
        lexer.preferOp()
    end
end

-- Go to next lexeme and load it into currlex_str, currlex_cat.
local function advance()
    -- Advance the iterator
    lexer_out_s, lexer_out_c = iter(state, lexer_out_s)

    -- If we're not past the end, copy current lexeme into vars
    if lexer_out_s ~= nil then
        curr_lexstr, curr_lexcat = lexer_out_s, lexer_out_c
    else
        curr_lexstr, curr_lexcat = "", 0
    end

    -- print('Adv to: ' .. curr_lexstr)
    
    -- Call lexit.preferOp() if it's appropriate
    doPreferOp()
end


-- Initializes iterator then advances to the first lexeme
local function init(progstr)
    iter, state, lexer_out_s = lexer.lex(progstr)
    advance()
end

-- Return true iff no more lexemes. i.e. iff curr_lexcat == 0
local function atEnd()
    return curr_lexcat == 0
end

-- Given string s, return true and advance() iff
-- curr_lexstr is equal to s. 
local function matchStr(s)
    if curr_lexstr == s then
        advance()
        return true
    end
end

-- Given lexeme category c (an int), return true and advance() iff
-- curr_lexcat is equal to c. 
local function matchCat(c)
    if curr_lexcat == c then
        advance()
        return true
    end
end

-- Returns true iff matchStr(s) == true for some options list (a table)
-- i.e. processes a rule of form ( 'a' || 'b' || ... )
-- Assumes optlist is an array (i.e. #optlist works)
local function matchORList(optlist)
    for i = 1, #optlist do
        if matchStr(optlist[i]) then
            return true 
        end
    end
end

-- Function to print ast to console. For debug use.
-- from useparseit.lua, Glenn G. Chappell 2018
function writeAST(x)
    local symbolNames = {
        "STMT_LIST", "INPUT_STMT", "PRINT_STMT", "FUNC_STMT",
        "CALL_FUNC", "IF_STMT", "WHILE_STMT", "ASSN_STMT", "CR_OUT",
        "STRLIT_OUT", "BIN_OP", "UN_OP", "NUMLIT_VAL", "BOOLLIT_VAL",
        "SIMPLE_VAR", "ARRAY_VAR"
    }
    if type(x) == "number" then
        local name = symbolNames[x]
        if name == nil then
            print("<ERROR: Unknown constant: "..x..">")
        else
            print(name)
        end
    elseif type(x) == "string" then
        print('"'..x..'"')
    elseif type(x) == "boolean" then
        if x then
            print("true")
        else
            print("false")
        end
    elseif type(x) == "table" then
        local first = true
        print("{")
        for k = 1, #x do  -- ipairs is problematic
            if not first then
                print(", ")
            end
            writeAST(x[k])
            first = false
        end
        print("}")
    elseif type(x) == "nil" then
        print("nil")
    else
        print("<ERROR: "..type(x)..">")
    end
end


--------------------------------------
-- Primary Function for Client Code --
--------------------------------------
-- Given program, initialize parser and call parsing function for start
-- symbol. Returns pair of booleans & AST. First boolean indicates
-- successful parse or not. Second boolean indicates whether the parser
-- reached the end of the input or not. AST is only valid if first
-- boolean is true.
function parseit.parse(progstr)
    print('-- Parsing...') -- Debug output
    init(progstr) -- init parser
    local pvalid, ast = parse_program()  -- Parse start symbol
    --writeAST(ast) -- Debug output
    return pvalid, atEnd(), ast -- return results
end


-----------------------------------
-- Generalized Parsing Functions --
-----------------------------------
-- Parser function that parse a given form, for use in
-- specific parsing functions.

-- Parse rules of form a -> nonterm { ( optlist[1] || optlist[2] || ... ) nonterm}
-- Ex: arith_expr  ->  expr { ( '+' | '-' ) exp }
--      i.e. nonterm = function parse_exp()
--           optlist = {'+', '-'}
-- Returns two values - success and ast
local function genparse_expr(nonterm, optlist)
    local pvalid, ast, ast1, savelex

    -- Ensure first nonterminal is valid
    pvalid, ast = nonterm()
    if not pvalid then
        return
    end

    -- for each non-mandatory option
    while true do
        breakFlag = true -- assume we will not match options
        savelex = curr_lexstr -- Note curr lexstr

        -- Ensure a match for one of the OR options
        if not matchORList(optlist) then
            break
        end

        -- return false iff cannot match last nonterminal
        pvalid, ast1 = nonterm()
        if not pvalid then
            return
        end

        -- set ast for Binary Operator, since we matched an OR option
        ast = {{BIN_OP, savelex}, ast, ast1}
    end

    return true, ast -- return results
end

-- Parses rule of form 'prefix' inner 'postfix', where
-- prefix and postfix are strings and inner is a parsefunction
-- ex: '[' expr ']'
--  i.e. inner = '[', expr = parse_expr, outter = ']'
-- Returns three values - success, syntaxOK, and ast.
-- Note: syntaxOK is false iff prefix is matched but
-- inner is not valid and/or postfix is notmatched.
local function genparse_enclosed(prefix, inner, postfix)
    if matchStr(prefix) then
        local pvalid, ast = inner()
        if not pvalid or not matchStr(postfix) then
            return false, false
        end
        return true, true, ast
    end
    return false, true
end

-- Parses rules of the form: nonterm1 nonterm2
-- ex: expr stmt_list
--    i.e. expr = parse_expr()
--         stmt_list = parse_stmt_list()
-- Returns 3 values - success, ast for nonterm1, and ast for nonterm2
local function genparse_twoNonTerms(nonterm1, nonterm2)
    -- nonterm1
    local pvalid, ast = nonterm1()
    if pvalid then
        -- nonterm2
        local ast1        
        pvalid, ast1 = nonterm2()
        if pvalid then
            return true, ast, ast1
        end
    end
end


--------------------------------
-- Specific Parsing Functions --
--------------------------------
-- Parsing functions for each specific nonterminal in the
-- grammar. Each function parses the nonterminal in its name and returns
-- a pair: boolean, AST. On a successul parse, the boolean is true, the
-- AST is valid, and the current lexeme is just past the end of the
-- string the nonterminal expanded into. Otherwise, the boolean is
-- false, the AST is not valid, and no guarantees are made about the
-- current lexeme. See the AST Specification near the beginning of this
-- file for the format of the returned AST.
-- NOTE. Parsing functions aren't "local". This allows them to
-- be called before their definitions.

-- (G1): program  ->  stmt_list
function parse_program()
    return parse_stmt_list()
end

-- Parses rules:
-- (G2): stmt_list  ->  { statement }
-- From assn4_code.txt, Glenn G. Chappell 2018
function parse_stmt_list()
    local good, ast, newast
    ast = { STMT_LIST }
    while true do
        if curr_lexstr ~= "input"
            and curr_lexstr ~= "print"
            and curr_lexstr ~= "func"
            and curr_lexstr ~= "call"
            and curr_lexstr ~= "if"
            and curr_lexstr ~= "while"
            and curr_lexcat ~= lexer.ID then
            return true, ast
        end
        good, newast = parse_statement()
        if not good then
            return false, nil
        end
        table.insert(ast, newast)
    end
end

-- Parses rules:
-- (G3): statement  ->  'input' lvalue
-- (G4):  	|  	'print' print_arg { ';' print_arg }
-- (G5):  	|  	'func' ID stmt_list 'end'
-- (G6):  	|  	'call' ID
-- (G7):  	|  	'if' expr stmt_list { 'elseif' expr stmt_list } [ 'else' stmt_list ] 'end'
-- (G8):  	|  	'while' expr stmt_list 'end'
-- (G9):  	|  	lvalue '=' expr
function parse_statement()
    local pvalid, ast, ast1, ast2, savelex

    -- 'input' lvalue
    if matchStr("input") then
        pvalid, ast = parse_lvalue()
        if pvalid then
            return true, {INPUT_STMT, ast}
        end
    end

    -- 'print' print_arg { ';' print_arg }
    if matchStr("print") then
        -- print_arg
        pvalid, ast = parse_print_arg()
        if pvalid then
            ast1 = {PRINT_STMT, ast}

            -- { ';' print_arg }
            while true do
                if not matchStr(";") then
                    break
                end
                pvalid, ast = parse_print_arg()
                if not pvalid then
                    return
                end
                table.insert(ast1, ast)
            end
            return true, ast1
        end
    end

    -- 'func' ID stmt_list 'end'
    if matchStr('func') then
        savelex = curr_lexstr
        print('SL to '.. savelex)
        if matchCat(lexer.ID) then
            pvalid, ast = parse_stmt_list()
            if pvalid and matchStr('end') then
                return true, {FUNC_STMT, savelex, ast}
            end
        end
    end

    --'call' ID
    if matchStr('call') then
        savelex = curr_lexstr
        if matchCat(lexer.ID) then
            return true, {CALL_FUNC, savelex}
        end
    end

    
    --'if' expr stmt_list { 'elseif' expr stmt_list } [ 'else' stmt_list ] 'end'
    if matchStr("if") then
        -- expr stmt_list
        local pe1_ast, pe2_ast, ps1_ast, ps2_ast        
        pvalid, pe1_ast, ps1_ast = genparse_twoNonTerms(parse_expr, parse_stmt_list)
        if pvalid then
            ast = {IF_STMT, pe1_ast, ps1_ast}

            -- { 'elseif' expr stmt_list }
            while true do
                if not matchStr("elseif") then
                    break
                end
                pvalid, pe2_ast, ps2_ast  = genparse_twoNonTerms(parse_expr, parse_stmt_list)
                if not pvalid then
                    return
                end
                table.insert(ast, pe2_ast)
                table.insert(ast, ps2_ast)
            end
            
            -- [ 'else' stmt_list ]
            ast2 = {STMT_LIST, ast3}              
            if matchStr('else') then
                pvalue, ast1 = parse_stmt_list()
                if not pvalue then
                    return
                end
                table.insert(ast, ast1)
            end

            -- 'end'
            if matchStr('end') then
                return true, ast
            end
        end
    end
        

    -- 'while' expr stmt_list 'end'
    if matchStr('while') then
        pvalid, ast, ast1 = genparse_twoNonTerms(parse_expr, parse_stmt_list)
        if pvalid and matchStr('end') then
            return true, {WHILE_STMT, ast, ast1}
        end
    end

    -- lvalue '=' expr
    if curr_lexcat == lexer.ID then  
        pvalid, ast = parse_lvalue()
        if pvalid and matchStr('=') then
            pvalid, ast1 = parse_expr()
            if pvalid then 
                -- io.write('RT parse_statement(): ') writeAST({ASSN_STMT, ast, ast1})        
                return true, {ASSN_STMT, ast, ast1}
            end
        end
    end
end

-- Parses rules:
-- (G10): print_arg  ->  'cr'
-- (G11):  	|  	STRLIT
-- (G12):  	|  	expr
function parse_print_arg()
    -- print('P: ' .. curr_lexstr .. ' in parse_print_arg()')
    -- 'cr'    
    if matchStr('cr') then
        return true, {CR_OUT}
    end

    -- STRLIT
    local savelex = curr_lexstr
    if matchCat(lexer.STRLIT) then
        return true, {STRLIT_OUT, savelex}
    end

    -- expr
    local pvalid, ast = parse_expr()
    if pvalid then
        return true, ast
    end
end

-- Parses rules:
-- (G13): expr  ->  comp_expr { ( '&&' | '||' ): comp_expr }
function parse_expr()
    -- print('P: ' .. curr_lexstr .. ' in parse_expr()')
    return genparse_expr(parse_comp_expr, {'&&', '||'})
end

-- Parses rules:
-- (G14): comp_expr  ->  '!' comp_expr
-- (G15):  	|  	arith_expr { ( '==' | '!=' | '<' | '<=' | '>' | '>=' ): arith_expr }
function parse_comp_expr()
    -- print('P: ' .. curr_lexstr .. ' in parse_comp_expr()')
    local savelex = curr_lexstr
    if matchStr('!') then
        local pvalid, ast = parse_comp_expr()
        if pvalid then
            return true, {{UN_OP, savelex}, ast}
        end
    else
        return genparse_expr(parse_arith_expr, {'==', '!=', '<', '<=', '>', '>='})
    end
end

-- Parses rules:
-- (G16): arith_expr  ->  term { ( '+' | '-' ): term }
function parse_arith_expr()
    -- print('P: ' .. curr_lexstr .. ' in parse_arith_expr()')    
    return genparse_expr(parse_term, {'+', '-'})
end

-- Parses rules:
-- (G17): term  ->  factor { ( '*' | '/' | '%' ): factor }
function parse_term()
    -- print('P: ' .. curr_lexstr .. ' in parse_term()')    
    return genparse_expr(parse_factor, {'*' , '/' , '%'})
end

-- Parses rules:
-- (G18): factor  ->  '(' expr '):'
-- (G19):  	|  	( 'true' | 'false' ):
-- (G20):  	|  	( '+' | '-' ): factor
-- (G21):  	|  	'call' ID
-- (G22):  	|  	NUMLIT
-- (G23):  	|  	lvalue
function parse_factor()
    -- print('P: ' .. curr_lexstr .. ' in parse_factor()')    
    local pvalid, svalid, ast, savelex
    
    -- '(' expr '):'
    pvalid, svalid, ast = genparse_enclosed('(', parse_expr, ')')
    if pvalid then
        return true, ast
    elseif not svalid then
        return
    end

    -- Note curr lex
    savelex = curr_lexstr
    
    --( 'true' | 'false' ):
    if matchORList({'true', 'false'}) then
        return true, {BOOLLIT_VAL, savelex}
    end

    --( '+' | '-' ): factor
    if matchORList({'+', '-'}) then
        pvalid, ast = parse_factor()
        if pvalid then
            return true, {{UN_OP, savelex}, ast}
        end
    end

    --'call' ID
    if matchStr('call') then
        savelex = curr_lexstr
        if matchCat(lexer.ID) then
            return true, {CALL_FUNC, savelex}
        else
            return
        end
    end

    -- NUMLIT
    if matchCat(lexer.NUMLIT) then
        return true, {NUMLIT_VAL, savelex}
    end

    -- lvalue
    pvalid, ast = parse_lvalue()
    if pvalid then
        return true, ast
    end

end

-- Parses rules:
-- (G24): lvalue  ->  ID [ '[' expr ']' ]
function parse_lvalue()
    -- print('P: ' .. curr_lexstr .. ' in parse_lvalue()')        
    local savelex = curr_lexstr    
    if matchCat(lexer.ID) then
        local pvalid, svalid, ast = genparse_enclosed('[', parse_expr, ']')
        if pvalid then
            return true, {ARRAY_VAR, savelex, ast}
        elseif svalid then
            return true, {SIMPLE_VAR, savelex}
        end
    end
end


-- Export the module
return parseit

