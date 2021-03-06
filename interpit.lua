#!/usr/bin/env lua

-- Interpreter for Dugong files. 
-- Dustin Fast
-- Spring, 2018


-- * To run a Dugong program, use dugong.lua (which uses this file). *
-- This module uses a coroutine to parse a given dugong absract syntax tree. 
-- 

local interpit = {}  -- Module def


-- ***** Variables *****

-- Symbolic Constants for astParser
local ERROR = 1
local CONST = 2
local BOOL = 3
local STR = 4
local FUNC_AST = 5
local FUNC_NAME = 6
local SUBTREE = 7

local astNames = {
    'ERROR', 'CONST', 'BOOL', 'STR', 'FUNC_AST', 'FUNC_NAME',
    'SUBTREE'}

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

local symbolNames = {
    'STMT_LIST', 'INPUT_STMT', 'PRINT_STMT', 'FUNC_STMT',
    'CALL_FUNC', 'IF_STMT', 'WHILE_STMT', 'ASSN_STMT', 'CR_OUT',
    'STRLIT_OUT', 'BIN_OP', 'UN_OP', 'NUMLIT_VAL', 'BOOLLIT_VAL',
    'SIMPLE_VAR', 'ARRAY_VAR'}


----- Utility Functions -----

-- numToInt (G Chappell, 2018)
-- Given a number, return the number rounded toward zero.
local function numToInt(n)
    assert(type(n) == 'number')

    if n >= 0 then
        return math.floor(n)
    else
        return math.ceil(n)
    end
end


-- strToNum (G Chappell, 2018)
-- Given a string, attempt to interpret it as an integer. If this
-- succeeds, return the integer. Otherwise, return 0.
local function strToNum(s)
    assert(type(s) == 'string' or type(s) == 'number')

    -- Try to do string -> number conversion; make protected call
    -- (pcall), so we can handle errors.
    local success, value = pcall(function() return 0+s end)

    -- Return integer value, or 0 on error.
    if success then
        return numToInt(value)
    else
        return 0
    end
end


-- numToStr (G Chappell, 2018)
-- Given a number, return its string form.
local function numToStr(n)
    assert(type(n) == 'number')
    return ''..n
end


-- Given a boolean in string, boolean, or number
-- form, return 1 if it is true, 0 if it is false.
local function boolToInt(b)
    assert(type(b) == 'boolean' or type(b) == 'string' or type(b) == 'number')
    
    if type(b) == 'boolean' then
        if b then
            return 1
        else
            return 0
        end
    elseif type(b) == 'string' then
        if b == 'true' then 
            return 1
        elseif b == 'false' then 
            return 0
        elseif strToNum(b) > 0 then
            return 1
        else 
            return 0
        end
    elseif type(b) == 'number' then
        if b >= 1 then return 1 else return 0 end
    end
end


-- convertVal
-- Given a variable type and val, returns value in correct form
local function convertVal(type, value)
    if type == BOOLLIT_VAL then return boolToInt(value)
    elseif type == NUMLIT_VAL then return strToNum(value)
    else
        print('ERROR - Unhandled conversion type: '..type)
    end
end


-- convertToStr
-- Given a variable, attemps to convert it to a string
local function convertToStr(value)
    if type(value) == 'boolean' then
        if value == false then value = 'false'
        elseif value == true then value = 'true' end
    elseif type(value) == 'number' then
        value =  ''..value
    elseif type(value) == 'string' then
        -- no conv needed
    elseif type(value) == 'table' then
        value = astToStr(value)
    else
        print('ERROR - Unhandled converToStr type for '.. value)
    end

    return value
end


-- astToStr (G Chappell, 2018)
-- Given an AST, produce a string holding the AST in (roughly) Lua form,
-- with numbers replaced by names of symbolic constants used in parseit.
-- A table is assumed to represent an array.
local function astToStr(ast)
    if type(ast) == 'number' then
        local name = symbolNames[ast]
        if name == nil then
            return '<Unknown numerical constant: '..ast..'>'
        else
            return name
        end
    elseif type(ast) == 'string' then
        return '"'..ast..'"'
    elseif type(ast) == 'boolean' then
        if ast then
            return 'true'
        else
            return 'false'
        end
    elseif type(ast) == 'table' then
        local first = true
        local result = '{'
        for k = 1, #ast do
            if not first then
                result = result .. ','
            end
            result = result .. astToStr(ast[k])
            first = false
        end
        result = result .. '}'
        return result
    elseif type(ast) == 'nil' then
        return 'nil'
    else
        return '<'..type(ast)..'>'
    end
end


-- evalArith
-- Accepts: lval, rval, and operator of a binary arithmetic expr
-- Returns: result of the expression, or 0 nil if indeterminate
local function evalArith (lval, rval, op)
    if op == '+' then return lval + rval
    elseif op == '-' then return lval - rval
    elseif op == '*' then return lval * rval
    elseif op == '%' then
        if rval ~= 0 then return lval % rval end
        return 0 -- return 0 on div by zero
    elseif op == '/' then 
        if rval ~= 0 then 
            return numToInt(lval / rval) -- numToInt for int division
        end
        return 0 -- return 0 on div by zero
    else
      print('ERROR: Invalid Operator Encountered: '..op)
    end
end


---- Exported Function, interpit.interp ----
--------------------------------------------

-- interp
-- An interpreter for Dugong
-- Assumes: ast is valid/correct
-- Accepts:
--   ast     - AST constructed by parseit.parse
--   state   - Table holding Dugong variables & functions
--             - AST for function xyz is in state.f['xyz']
--             - Value of simple variable xyz is in state.v['xyz']
--             - Value of array item xyz[42] is in state.a['xyz'][42]
--   incall  - Function to call for line input
--             - incall() inputs line, returns string with no newline
--   outcall - Function to call for string output
--             - outcall(str) outputs str with no added newline
--             - To output a newline, do outcall('\n')
-- Returns: state, updated with new and/or updated variable values
function interpit.interp(start_ast, state, incall, outcall)

    -- interp variables --
    ----------------------
    local debugmode = false      -- denotes debug output on/off
    local debugpause = false     -- denotes debug output causes pause

    local currAST = 0            -- ASTtrees/parsers index, used for the below tables
    local ASTParsers = {}        -- a list of ast parser coroutines
    local ASTrees = {}           -- a list of the trees we're parsing
    local firstFlag = {}         -- denotes the initial STMT_LIST has been encountered
    local stmtList = {}          -- container to hold STMT_LISTs
    local subtreeDone = {}       -- denotes astParser just yielded an intact STMT_LIST

    local currKey, currVal = nil -- key and val of ASTParsers[currVal]'s current node


    -- interp helper funcs --
    -------------------------

    -- printDebug
    -- prints debug info if in debug mode (set debug mode at line 237)
    local function printDebug(str)
        if debugmode then
            local key, val = nil
            if currKey == nil then key = "nil" 
            else key = astNames[currKey] end

            if currVal == nil then val = "nil" 
            elseif currKey == CONST then
                val = symbolNames[currVal]
            else val = currVal end

            if type(val) == 'table' then
                val = astToStr(val)
            end
            if str then print('** '..str..' **') end
            print('{ '..key..', '..val..' } (currAST = '..currAST..')\n')
            if debugpause then io.read('*l') end -- pause
        end
    end

    -- astParse
    -- A recursive coroutine yielding node values via preorder traversal
    -- Used by interpit.interp
    -- Accepts: An AST node (may be root) in table form.
    -- Yields: AST node value as two vars of one of the following:
    --              CONST, NUMBER   = A numeric value corresponding to symbolNames[NUMBER]
    --              LIT LITERAL     = A string or numeric literal, in string form
    --              BOOL, bool      = A bool in string form, either true or false
    --              SUBTREE, tree   = An intact AST
    --              ERR, string     = An error in string form
    -- Ex: given AST '{STMT_LIST,{PRINT_STMT,{STRLIT_OUT,'Hello World'}}}',
    --  yields {CONST, 1}, {CONST, 3}, {CONST, 10}, {LIT, 'Hello World'}
    local function astParse(node)
        -- If node is a symbolic constant:
        if type(node) == 'number' then        
            local name = symbolNames[node]
            
            if name == nil then
                coroutine.yield(ERROR, 'Unknown constant: '..node)
            else
                -- If STMT_LIST node, the intact subtree is in stmtList[currAST],
                -- We return the STMT_LISTs intact as long as its not the first one.
                -- If it is the first one, we set firstFlag to denote it's been seen.
                if node == STMT_LIST then
                    if firstFlag[currAST]then
                        serveast = table.remove(stmtList[currAST])
                        printDebug('** ast served: '..astToStr(serveast)..'**') --debug                        
                        coroutine.yield(SUBTREE, serveast)
                        subtreeDone[currAST] = true
                    else
                        -- denote first STMT_LIST has been seen
                        firstFlag[currAST] = true
                        coroutine.yield(CONST, node)    
                    end
                else
                    coroutine.yield(CONST, node)    
                end
            end
            
        -- If node is a string value:
        elseif type(node) == 'string' then
            coroutine.yield(STR, node)
        
        -- If node is a table, do recursive call to parse it:
        elseif type(node) == 'table' then
            for i = 1, #node do  

                -- If next node is stmt list, save it to return later intact
                if (i+1) <= #node then
                    if firstFlag[currAST] and (i+1) <= #node and node[i+1][1] == STMT_LIST then
                        printDebug('** ast saved: '..astToStr(node[i+1])..'**') --debug
                        table.insert(stmtList[currAST], 1, node[i+1])
                    end
                end
                
                -- recursively parse next node
                astParse(node[i]) 

                -- if we last yielded an intact subtree, break out of the current subtree
                if subtreeDone[currAST] then 
                    printDebug('brk subtree') -- debug
                    subtreeDone[currAST] = false 
                    return 
                end
            end

        -- If node is empty or of an unexpected type:
        elseif type(node) == 'nil' then
            coroutine.yield(ERROR, 'Empty node encountered.')
        else
            coroutine.yield(ERROR, 'Invalid type encountered: '..type(node))
        end
    end


    -- advanceNode
    -- Advances astParse coroutine and assigns attributes to currKey and currVal
    local function advanceNode()
        if coroutine.status(ASTParsers[currAST]) == 'dead' then
        printDebug('Parser '..currAST..' dead') return end
        
        local ok = nil
        ok, currKey, currVal = coroutine.resume(ASTParsers[currAST], ASTrees[currAST])          
        assert(ok)    
    end


    -- setVar
    -- Called to set a varable of the given name/type to the given value
    -- Accepts: name  = Variable name
    --          type  = Variable type, either SIMPLE_VAR, ARRAY_VAR, or FUNC_STMT
    --          value = Variable value
    --          vtype = Type of value, either NUMLIT_VAL or BOOLLIT_VAL
    --          index = Array index. Required if type = ARRAY_VAR
    -- Returns: None
    local function setVar(name, type, value, valtype, index)
        if type == SIMPLE_VAR then
            state.v[name] = convertVal(valtype, value)
            printDebug('Assigned '..name..' = '..value) -- debug

        elseif type == ARRAY_VAR then
            -- If state.a[name] doesn't exit, create it first, then assign val
            local table = state.a[name]
            if not table then state.a[name] = {} end
            state.a[name][index] = convertVal(valtype, value)
            printDebug('Assigned '..name..'['..index..'] = '..value) -- debug   
        
        elseif type == FUNC_STMT then
            state.f[name] = value
            printDebug('Assigned '..name..' = '..astToStr(state.f[name])) -- debug
        
        else
            if not index then index = 'nil' end -- debug
            printDebug('ERROR: Unhandled var assignment: '..name..', '..type..', '..val..', '..index)
        end
    end


    -- getVar
    -- Called to get the value of the given variable
    -- Accepts: name  = Variable name
    --          type  = Variable type, either SIMPLE_VAR or ARRAY_VAR, or FUNC_STMT
    --          index = Array index. Required if type = ARRAY_VAR
    -- Returns: 
    local function getVar(name, type, index)
        local value = nil
        if not index then index = 'nil' end -- for debug output
        printDebug('getVar: '..name..', '..type..', '..index)

        if type == SIMPLE_VAR then
            value = state.v[name]
        elseif type == ARRAY_VAR then
            value = state.a[name]
            if value ~= nil then
                value = value[strToNum(index)]
            end
        elseif type == FUNC_STMT then
            value = state.f[name]
        else
            printDebug('ERROR: Unhandled variable fetch: '..name..', '..type..', '..index)
        end

        -- ensure no nil vals (i.e. an undefined var was used)
        if value == nil then 
            value = '0' 
            printDebug('WARNING: An undefined value was referenced: '..name..', '..type..', '..index)            
        end

        return value
    end

    -- parseVar
    -- Called to get var attributes when a SIMPLE_VAR or ARRAY_VAR is encountered
    -- Calls advanceNode()
    -- Accepts: None
    -- Returns: name  = Variable name
    --          type  = Variable type, either SIMPLE_VAR or ARRAY_VAR
    --          index = Array index. Required if type = ARRAY_VAR
    local function parseVar()
        -- Current val is our var type.Next val is var name. 
        local type = currVal
        advanceNode()
        local name = currVal
        local index = nil

        -- If type is ARRAY_VAR
        if type == ARRAY_VAR then
            advanceNode()
            if currVal == BIN_OP then index = doBIN_OP()
            elseif currVal == UN_OP then index = doUN_OP()
            elseif currVal == SIMPLE_VAR then 
                local name2, type2, value2, index2
                name2, type2, value2, index2 = parseAndGetVar()
                index = value2
            elseif currVal == NUMLIT_VAL then
                advanceNode()
                index = strToNum(currVal)
            else 
                printDebug('ERROR: Unhandled Array index type in '..debug.getinfo(1, 'n').name) -- debug
                
            end
        end

        return name, type, index
    end


    -- parseAndGetVar
    -- Called to get var attributes and value when a SIMPLE_VAR or ARRAY_VAR is encountered
    -- Calls advanceNode()
    -- Accepts: None
    -- Returns: name  = Variable name
    --          type  = Variable type, either SIMPLE_VAR or ARRAY_VAR
    --          value = 
    --          index = Array index. Required if type = ARRAY_VAR
    function parseAndGetVar()
        local name, type, index = parseVar()
        local value = getVar(name, type, index)
        return name, type, value, index
    end


    -- interp Dugong processing functions --
    ----------------------------------------
    -- doSYMBOLNAME
    -- Called when the specified SYMBOL is encountered in the AST.
    -- Each function calls advanceNode to set currKey and currVal,
    -- then acts accordingly, based on its contents.
    -- Accepts/Returns: Function specific
    -- Scope: Intentionally global

    -- doSTMT_LIST
    -- Loops through a statement list.
    -- Accepts: None
    -- Returns: The results of the last stmt call (a bool), if any
    function doSTMT_LIST()
        local no_advance = nil -- container to hold statement call results
                               -- used to denote whether or not to call advanceNode()
        while (true) do
            -- update currVal as long as no statement has indicated not to.
            if not no_advance then
                advanceNode()
            end
            no_advance = nil

            -- If coroutine dead, we're done
            if coroutine.status(ASTParsers[currAST]) == 'dead' then break end

            printDebug('In '..debug.getinfo(1, 'n').name) --debug output

            -- call appropriate function based on currVal
            -- Invariant: If we're seeing BIN_OP or UN_OP, break
            -- because we got here from a WHILE loop
            if currVal == STMT_LIST then advanceNode() end -- if we're here one step early
            if currVal == INPUT_STMT then no_advance = doINPUT_STMT()
            elseif currVal == PRINT_STMT then no_advance = doPRINT_STMT() 
            elseif currVal == FUNC_STMT then no_advance = doFUNC_STMT() 
            elseif currVal == CALL_FUNC then no_advance = doCALL_FUNC() 
            elseif currVal == IF_STMT then no_advance = doIF_STMT() 
            elseif currVal == WHILE_STMT then no_advance = doWHILE_STMT()
            elseif currVal == ASSN_STMT then no_advance = doASSN_STMT()
            elseif currVal == BIN_OP then no_advance = doBIN_OP() break
            elseif currVal == UN_OP then no_advance = doUN_OP() break
            else
                -- Note: this is expected to occur in some cases
                printDebug('ERROR: Unhandled STMT in '..debug.getinfo(1, 'n').name) -- debug
                printDebug()
            end
        end

        return no_advance
    end


    -- doINPUT_STMT
    -- Prompts user for a string value and assigns it to state var
    -- Accepts/Returns: None
    function doINPUT_STMT()
        advanceNode()
        printDebug('In '..debug.getinfo(1, 'n').name) --debug output

        -- get var attributes
        local name, type, index = parseVar()

        -- Prompt for input and do assignment
        local value = incall()
        setVar(name, type, value, NUMLIT_VAL, index)
    end


    -- doPRINT_STMT
    -- Outputs an STR_LIT or NUM_LIT to the console
    -- Accepts/Returns:None
    function doPRINT_STMT()
        advanceNode()
        printDebug('In '..debug.getinfo(1, 'n').name) --debug output
        
        -- do outcall after necessary formatting
        function doOutcall(str)
            -- remove leading/trailing quote pair
            if type(str) == 'string' then
                if (str:sub(1,1) == '"' and str:sub(#str, #str) == '"')
                or (str:sub(1,1) == "'" and str:sub(#str, #str) == "'")
                then str = str:sub(2, #str-1) end

            -- represent bools as "1" or "0"
            elseif type(str) == 'boolean' then
                str = convertToStr(boolToInt(str))
            
            -- anything else, represent as a string
            else
                str = convertToStr(str)
            end

            -- do outcall
            outcall(str)
        end

        -- loop through print args. Break when we encounter a non print arg
        while true do 
            printDebug('In '..debug.getinfo(1, 'n').name) --debug output
            local value = nil

            if currVal == CR_OUT then
                value = '\n'

            elseif currVal == STRLIT_OUT
                   or currVal == NUMLIT_VAL
                   or currVal == BOOLLIT_VAL then
                advanceNode()
                value = currVal

            elseif currVal == BIN_OP then
                value = doBIN_OP()
            elseif currVal == UN_OP then
                value = doUN_OP()
            
            elseif currVal == SIMPLE_VAR  or currVal == ARRAY_VAR then
                local name, vtype, index = nil
                name, vtype, value, index = parseAndGetVar()

            elseif currVal == CALL_FUNC then 
                doCALL_FUNC(true)
                value = getVar('return', SIMPLE_VAR)

            else
                print('ERROR: Unhandled case encountered in '..debug.getinfo(1, 'n').name) -- debug
                printDebug()
            end
            
            -- do outcall
            doOutcall(value)

            -- peak at next node. if not another print arg, return
            advanceNode()
            printDebug()
            if not (currVal == CR_OUT or currVal == STRLIT_OUT
            or currVal == BIN_OP or currVal == UN_OP
            or currVal == SIMPLE_VAR or currVal == ARRAY_VAR
            or currVal == NUMLIT_VAL or currVal == BOOLLIT_VAL 
            or currVal == CALL_FUNC)
            then 
                return true -- true, to tell do_STMT_LIST not to advance (we just did it by peeking)
            end
        end
    end


    -- doFUNC_STMT
    -- Processes a function definition and saves it to state
    -- Accepts/Returns: None
    function doFUNC_STMT()
        advanceNode()
        printDebug('In '..debug.getinfo(1, 'n').name) --debug output

        -- curr val is func name, then next is functions body (an AST)
        local name = currVal
        advanceNode()
        local ast = currVal

        -- store func name and associated body
        setVar(name, FUNC_STMT, ast)
    end


    -- doCALL_FUNC
    -- "Calls" a previously defined function by proccesing its STMT_LIST ast
    -- Accepts/Returns: None
    function doCALL_FUNC()
        advanceNode()
        printDebug('In '..debug.getinfo(1, 'n').name) --debug output

        -- curr val is func name, get its ast and parse it
        local ast = getVar(currVal, FUNC_STMT)
        interpSTMT_LIST(ast)
    end

    
    -- doIF_STMT
    -- Processes an if statment and the necessary case's STMT_LIST
    -- Accepts: None (single var 'cond_hit' is only used in recursive calls)
    -- Returns: True (necessary to tell caller not to advanceNode()
    function doIF_STMT(cond_hit)
        advanceNode()
        printDebug('In '..debug.getinfo(1, 'n').name) --debug output
        local value, execute = nil
        local matched = false   -- denote if we've matched a cond at this depth

        -- function to run a STMT_LIST if we haven't matched the if cond yet.
        function runstmt(stmt_list)
            if cond_hit then
                printDebug('cond_hit = true. SKIPPING:') --debug
                printDebug(astToStr(stmt_list))
            else
                printDebug('cond_hit = false. RUNNING.') --debug
                interpCOND_STMT(stmt_list)
            end
        end

        -- If currVal is not an operator (BIN_OP or UN_OP) or
        -- NUMLIT_VAL or BOOLIT_VAL, or STMT_LIST, we're done w the IF_STMT
        if not (currVal == BIN_OP or currVal == UN_OP or currVal == NUMLIT_VAL
                or currVal == BOOLLIT_VAL or type(currVal) == "table") then 
                    printDebug('Done w If') --debug
                    return end

        if currVal == BIN_OP then 
            value = doBIN_OP()
            advanceNode()
            execute = currVal
            -- printDebug('b: '..value..':'..astToStr(execute))  

        elseif currVal == UN_OP then
            value = doUN_OP()   
            advanceNode()
            execute = currVal
            -- printDebug('u: '..value..':'..astToStr(execute))

        elseif currVal == NUMLIT_VAL or currVal == BOOLLIT_VAL then
            advanceNode()
            value = currVal
            advanceNode()
            execute = currVal
            -- printDebug('Lit1: '..value..':'..type(value)..':\n'..astToStr(execute))

        -- handle STMT_LIST, i.e the if's "else" branch
        elseif type(currVal) == "table" then
            value = 1 -- set to true so execute gets done if we haven't hit any conds
            execute = currVal
            -- printDebug('e: '..value..':'..astToStr(execute))

        -- unhandled
        else
            print('ERROR: Unhandled value in IF_STMT: '..currVal)
        end

        -- Do the correct action based on value (assigned above)
        if boolToInt(value) >= 1 then 
            matched = true
            runstmt(execute)
        end

        -- Recursively process next conds
        doIF_STMT((matched or cond_hit))

        -- return true to tell do_STMT_LIST not to advanceNode()
        -- (because we did it in this function already)
        return true 
    end

    
    -- doWHILE_STATMENT
    -- Processes a while loop and its STMT_LIST accordingly
    -- Accepts/Returns: None
    function doWHILE_STMT()
        advanceNode()
        printDebug('In '..debug.getinfo(1, 'n').name) --debug output

        local temp = {}         -- temp
        local expr = {}         -- holds expression AST
        local op_type = nil     -- operator type
        local execute = nil     -- holds STMT_LIST AST
        local value = nil       -- value after eval(expr)

        -- build an AST for the expression from next vals,
        -- noting the operator type when we see it (it's the currVal).
        while true do
            if currKey == CONST then
                if not op_type then 
                    op_type = currVal 
                end
                table.insert(temp, currVal)
            elseif currKey == STR or currKey == BOOL then
                table.insert(temp, currVal)
                table.insert(expr, temp)
                temp = {}
            end                
            advanceNode()       
            if type(currVal) == 'table' then break end
        end

        -- curVal is our STMT_LIST to execute inside the loop
        execute = currVal

        while true do
            -- handle BIN_OP 
            if op_type == BIN_OP then 
                value = interpCOND_STMT(expr, true)
                -- printDebug('b: '..value..':'..astToStr(execute))  

            -- handle UN_OP 
            elseif op_type == UN_OP then
                value = interpCOND_STMT(expr, true)                
                -- printDebug('u: '..value..':'..astToStr(execute))

            -- handle NUMLIT and BOOLLIT 
            elseif op_type == NUMLIT_VAL or op_type == BOOLLIT_VAL then
                value = expr[1][2] -- expr is of the form ({TYPE, VALUE}}
                -- printDebug('l: '..value..':'..astToStr(execute))
            
            -- handle SIMPLE_VAR
            elseif op_type == SIMPLE_VAR then
                value = expr[1][2] -- expr is of the form ({SIMPLE_VAR, VARNAME}}
                value = getVar(value, SIMPLE_VAR)
                -- printDebug('v: '..value..':'..astToStr(execute))

            -- handle ARRAY_VAR
            elseif op_type == ARRAY_VAR then
                value = expr[1][2] -- expr is of the form ({TYPE, VARNAME}, {NUMLIT_VAL, INDEX}}
                index = expr[2][2]
                value = getVar(value, ARRAY_VAR, index)
                printDebug('v: '..value..':'..index..astToStr(execute))
                
            -- unhandled
            else
                print('ERROR: Unhandled optype in WHILE_STMT: '..op_type)
            end

            if boolToInt(value) == 1 then
                printDebug('Running While body')
                interpSTMT_LIST(execute)
            else
                printDebug('done w WHILE')
                break
            end
        end
    end

    
    -- doASSN_STMT
    -- Process a VAR = VALUE type statment
    -- Accepts/Returns: None
    function doASSN_STMT()
        advanceNode()
        printDebug('In '..debug.getinfo(1, 'n').name) --debug output

        -- Get var attributes
        local name, type, index = parseVar()

        -- Next node is either an operator (BIN_OP or UN_OP)
        -- or a value (NUMLIT_VAL, BOOLLIT_VAL)
        -- or a variable (SIMPLE_VAR, ARRAY_VAR)  
        advanceNode()
        local value = nil

        -- handle BIN_OP assignment
        if currVal == BIN_OP then 
            value = doBIN_OP()
            setVar(name, type, value, NUMLIT_VAL, index) 
                       
        -- handle UN_OP assignment 
        elseif currVal == UN_OP then
            value = doUN_OP()
            setVar(name, type, value, NUMLIT_VAL, index)     

        -- handle NUMLIT or BOOLLIT assignment
        elseif currVal == NUMLIT_VAL or currVal == BOOLLIT_VAL then
            local valType = currVal
            advanceNode()
            setVar(name, type, currVal, valType, index)

        -- handle assignment of another vars value
        elseif currVal == SIMPLE_VAR or currVal == ARRAY_VAR then
            local currType = currVal
            local name2, type2, value2, index2 = parseAndGetVar()
            setVar(name, type, value2, NUMLIT_VAL, index)
        end
    end

    
    -- doBIN_OP
    -- Accepts: None
    -- Returns: Result of operation (true or false for boolean operators, else an int)
    function doBIN_OP()        
        advanceNode()
        printDebug('In '..debug.getinfo(1, 'n').name) --debug output

        local name, index = nil     -- temp vars
        local lvalue, ltype = nil   -- left operand
        local rvalue, rtype = nil   -- right operand
        local op = currVal          -- operator
        local result = false        -- final result (return value)
        
        -- Note: For both the l and r values:
        -- Next node == BIN_OP, UN_OP, NUMLIT_VAL, BOOLIT_VAL, SIMPLE_VAR, ARRAY_VAR.
        -- If BIN_OP or UN_OP, recursively call this func to process them.
        -- Else, the next value is an operand.

        -- evaluate lvalue
        advanceNode()
        if currVal == BIN_OP then 
            lvalue = doBIN_OP() 
        elseif currVal == UN_OP then
            lvalue = doUN_OP()
        elseif currVal == SIMPLE_VAR then
            name, ltype, lvalue, index = parseAndGetVar()            
        elseif currVal == ARRAY_VAR then
            name, ltype, lvalue, index = parseAndGetVar()
        elseif currVal == NUMLIT_VAL or currVal == BOOLLIT_VAL then
            ltype = currVal
            advanceNode()  
            lvalue = convertVal(ltype, currVal) 
        else
            print('ERROR: Unhandled value in BIN_OP lvalue'..curVal)          
        end
        
        -- evaluate rvalue
        advanceNode()
        if currVal == BIN_OP then 
            rvalue = doBIN_OP() 
        elseif currVal == UN_OP then
            rvalue = doUN_OP()
        elseif currVal == SIMPLE_VAR then
            name, rtype, rvalue, index = parseAndGetVar()            
        elseif currVal == ARRAY_VAR then
            name, rtype, rvalue, index = parseAndGetVar()
        elseif currVal == NUMLIT_VAL or currVal == BOOLLIT_VAL then
            rtype = currVal
            advanceNode()  
            rvalue = convertVal(rtype, currVal) 
        else
            print('ERROR: Unhandled value in BIN_OP rvalue'..curVal)
        end

        -- handle boolean operators
        if op == '&&' or op == '||' or op == '==' or op == '!=' then
            
            -- normalize bool forms
            if lvalue == 0 then lvalue = false
            elseif lvalue == 1 then lvalue = true
            elseif lvalue == 'false' then lvalue = false
            elseif lvalue == 'true' then lvalue = true end
            
            if rvalue == 0 then rvalue = false
            elseif rvalue == 1 then rvalue = true
            elseif rvalue == 'false' then rvalue = false
            elseif rvalue == 'true' then rvalue = true end

            -- determine boolean result
            if op == '&&' then
                if lvalue and rvalue then result = true end
            elseif op == '||' then
                if lvalue or rvalue then result = true end
            elseif op == '==' then
                if lvalue == rvalue then result = true end
            elseif op == '!=' then
                if lvalue ~= rvalue then result = true end
            end

        -- handle arith operators
        elseif op == '<' or op == '<=' or op == '>' or op == '>='
               or op == '+' or op == '-' or op == '*' or op == '/' or op == '%' then
            
            -- normalize ints
            if type(lvalue) ~= 'number' then lvalue = boolToInt(lvalue) end
            if type(rvalue) ~= 'number' then rvalue = boolToInt(rvalue) end
            
            -- determine result
            if op == '<' then
                if lvalue < rvalue then result = true end
            elseif op == '<=' then
                if lvalue <= rvalue then result = true end
            elseif op == '>' then
                if lvalue > rvalue then result = true end
            elseif op == '>=' then
                if lvalue >= rvalue then result = true end
            elseif op == '+' or op == '-' or op == '*' or op == '/' or op == '%' then 
                result = evalArith(lvalue, rvalue, op)
            end
                        
        else
            print('ERROR: Unhandled operator encountered: '..op)
        end
        
        printDebug('Operand types: '..type(lvalue)..':'..type(rvalue))
        printDebug('BIN_OP results: '..convertToStr(lvalue)..' '..convertToStr(op)..' '..convertToStr(rvalue)..' = '..convertToStr(result)) -- debug
        return result
    end


    -- doUN_OP
    -- Accepts: None
    -- Returns: Result of operation - 1 or 0 for boolean operators, else an int
    function doUN_OP()        
        advanceNode()
        printDebug('In '..debug.getinfo(1, 'n').name) --debug output

        local name, index                -- temp vars
        local value, vtype, result = nil -- operand
        local op = currVal               -- operator

        -- Next node == BIN_OP, UN_OP, NUM_LIT, SIMPLE_VAR, or ARRAY_VAR
        -- If BIN_OP or UN_OP, recursively call this func to process them.
        -- Else, the current node value is our operand type,
        -- and the next value is the operand.
        advanceNode()
        if currVal == BIN_OP then 
            value = doBIN_OP() 
        elseif currVal == UN_OP then
            value = doUN_OP()
        elseif currVal == SIMPLE_VAR then
            name, vtype, value, index = parseAndGetVar()            
        elseif currVal == ARRAY_VAR then
            name, vtype, value, index = parseAndGetVar()
        elseif currVal == NUMLIT_VAL or currVal == BOOLLIT_VAL then
            vtype = currVal
            advanceNode()  
            value = convertVal(vtype, currVal) 
            if vtype == BOOLLIT_VAL then
                if value == 0 then value = false
                elseif value == 1 then value = true end
            end
        else
            print('ERROR: Unhandled value in BIN_OP lvalue'..curVal)          
        end

        -- convert bool vals to a actual bools
        if vtype == BOOLLIT_VAL then
            if value == 0 then value = false
            elseif value == 1 then value = true end
        end
        if type(value) == 'string' then
            if value == 'false' then value = false
            elseif value == 'true' then value = true end
        end

        -- handle negative operator 
        result = value
        if op == '-' then
            -- if vtype == NUMLIT_VAL then result = -value
            if type(value) == 'boolean' then 
                if value == true then result = false
                else result = true end
            else 
                result = -value
            end

        -- handle negation operator
        elseif op == '!' then
            if type(value) == 'boolean' then 
                result = not value
            else
                if value >= 1 then result = 0
                else result = 1 end
            end
        end

        printDebug('UN_OP results: '..op..convertToStr(value)..' = '..convertToStr(result)) -- debug
        return result
    end

    
    -- interpSTMT_LST
    -- Called to process an AST STMT_LIST.
    -- Called first from interp main function body, then
    -- from any other func that encounters a STMT_LIST
    -- Acccepts: an AST node of type STMT_LIST
    function interpSTMT_LIST(ast)
        -- increase ast parser count by 1 and init ast parser coroutine
        currAST = currAST + 1
        ASTrees[currAST] = ast
        firstFlag[currAST] = false
        stmtList[currAST] = {}
        subtreeDone[currAST] = false
        ASTParsers[currAST] = coroutine.create(astParse)

        printDebug('In MAIN loop #'..currAST.. ' for:\n'..astToStr(ASTrees[currAST])) -- debug            
        local temp = currAST
        doSTMT_LIST()
        currAST = currAST - 1
        printDebug('END MAIN loop # '..temp..' Curr = '..currAST) -- debug 
    end


    -- similiar to above but returns a result to tell doSTMT_LIST to advance or not
    function interpCOND_STMT(ast, no_advance)
        -- increase ast parser count by 1 and init ast parser coroutine
        local baseASTCount = currAST -- note currAST count, for debug
        currAST = currAST + 1
        ASTrees[currAST] = ast
        firstFlag[currAST] = false
        stmtList[currAST] = {}
        subtreeDone[currAST] = false
        ASTParsers[currAST] = coroutine.create(astParse)
        
        printDebug('In COND loop #'..currAST.. ' base = '..baseASTCount..' for: '..astToStr(ASTrees[currAST])) -- debug
        local temp = currAST
        local result = doSTMT_LIST()
        currAST = currAST - 1
        printDebug('END COND loop # '..temp..' Curr = '..currAST) -- debug
        
        return result
    end


    -- interp function body --
    ---------------------------
    -- The current node is the root STMT_LIST, 
    -- Process it, then return the state table
    interpSTMT_LIST(start_ast) 
    return state                
end

-- Export the interpit module
return interpit

