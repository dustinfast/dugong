-- lexit.lua
-- CSCE A3331, Assignment 6
-- Dustin Fast
-- Spring, 2018
-- Adapted from interpit.lua, Glenn G. Chappell 2018


-- *******************************************************************
-- * To run a Dugong program, use dugong.lua (which uses this file). *
-- *******************************************************************


local interpit = {}  -- Our module


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


-- boolToInt (G Chappell, 2018)
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
        else
            return 0
        end
    elseif type(b) == 'number' then
        return b
    end
end


-- convertVal
-- Given a variable type and val, returns value in correct form
local function convertVal(type, value)
    -- print('Converting: '..type..':'..value) -- debug
    if type == BOOLLIT_VAL then return boolToInt(value)
    elseif type == NUMLIT_VAL then return strToNum(value)
    else
        print('ERROR - Unhandled conversion type: '..type)
    end
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
    elseif op == '%' then return lval % rval
    elseif op == '/' then 
        if rval ~= 0 then return lval / rval end
        return 0 -- return 0 on div by zero
    else
      Print('ERROR: Invalid Operator Encountered: '..op)
    end
end


----- Primary Function for Client Code -----
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
--             - To print a newline, do outcall('\n')
-- Returns: state, updated with new and/or updated variable values
function interpit.interp(start_ast, state, incall, outcall)

    -- interp variables --
    ----------------------
    local astParser = {} -- a list of ast parser coroutines
    local ASTrees = {}
    local currAST= 0 -- current AST and parser index
    local currKey, currVal = nil -- key and val of astParser's current node.


    -- interp helper funcs --
    -------------------------

    -- iterateSubtree
    -- A recursive coroutine yielding node values via inorder traversal
    -- Used by interpit.interp
    -- Accepts: An AST node (may be root) in table form.
    -- Yields: AST node value as two vars of one of the following:
    --              CONST, NUMBER   = A numeric value corresponding to symbolNames[NUMBER]
    --              LIT' LITERAL    = A string or numeric literal, in string form
    --              BOOL, bool      = A bool in string form, either true or false
    --              ERR, string     = An error in string form
    -- Ex: given AST '{STMT_LIST,{PRINT_STMT,{STRLIT_OUT,'Hello World'}}}',
    --  yields {'CONST', 1}, {'CONST', 3}, {'CONST', 10}, {'LIT', 'Hello World'}
    -- Variables: the below table vars correspond to varName[currAST] and are used
    -- to maintain info for different coroutine instances
    local firstFlag = {} -- denotes the initial STMT_LIST has been encountered
    local stmtList = {} -- container to hold STMT_LISTs
    local ifList = {}   -- container to hold IF_STMTs
    local subtreeDone = {}  -- denotes an intact STMT_LIST was yielded
    local function iterateSubtree(node)
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
                        -- print('ast served')
                        -- coroutine.yield(SUBTREE, stmtList[currAST])
                        coroutine.yield(SUBTREE, table.remove(stmtList[currAST]))
                        --stmtList[currAST] = nil
                        subtreeDone[currAST] = true
                    else
                        -- denote first STMT_LIST has been seen
                        firstFlag[currAST] = true
                        coroutine.yield(CONST, node)    
                    end
                    
                -- if IF_STMT node, return the node, then on the next call return
                -- the IF_STMT subtree intact
                -- elseif node == IF_STMT then
                --     if ifList[currAST] then
                --         print('IF_STMT ast served')
                --         coroutine.yield(CONST, node)
                --         coroutine.yield(SUBTREE, ifList[currAST])
                --         ifList[currAST] = nil
                --         subtreeDone[currAST] = true
                --     end
                else
                    coroutine.yield(CONST, node)    
                end
            end
            
        -- If node is a string value:
        elseif type(node) == 'string' then
            -- print('string')
            coroutine.yield(STR, node)
        
        -- If node is a bool value:
        elseif type(node) == 'boolean' then
            print('BOOL!')
            if node then
                
                coroutine.yield(BOOL, 'true')
            else
                coroutine.yield(BOOL, 'false')
            end
        
        -- If node is a table, do recursive call to parse it:
        elseif type(node) == 'table' then
            for i = 1, #node do  
                -- print('table')

                -- If second next node is stmt list, 
                -- save it to return later intact
                if (i+1) <= #node then
                    if firstFlag[currAST] and (i+1) <= #node and node[i+1][1] == STMT_LIST then
                        -- stmtList[currAST] = node[i+1]                        
                        -- print('ast saved: '..astToStr(node[i+1])..'\n') --debug
                        table.insert(stmtList[currAST], 1, node[i+1])
                    end
                end
                
                -- recursively parse next node
                iterateSubtree(node[i]) 

                -- if we last yielded a STMT_LIST, break out of the current subtree
                if subtreeDone[currAST] then 
                    --print('brk') -- debug
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
    -- Advances astParser and assigns attributes to currKey and currVal
    local function advanceNode()
        if currAST <= 0 then return end
        local ok = nil
        ok, currKey, currVal = coroutine.resume(astParser[currAST], ASTrees[currAST])          
        assert(ok)    
    end


    -- printDebugString
    -- prints the current key/value in a conveient form. For debug.
    local function printDebugString()
        local key, val = nil
        if currKey == nil then key = "nil" 
        else key = astNames[currKey] end

        if currVal == nil then val = "nil" 
        elseif currKey == CONST then
            val = symbolNames[currVal]
        else val = currVal end

        if type(val) == 'table' then
            print(astToStr(val))
        else
            print('{ '..key..', '..val..' }')
        end
        io.read('*l') -- pause
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
            print('Assigned '..name..' = '..value) -- debug

        elseif type == ARRAY_VAR then
            -- If state.a[name] doesn't exit, create it
            local table = state.a[name]
            if not table then state.a[name] = {} end

            -- insert new value
            state.a[name][index] = convertVal(valtype, value)
            print('Assigned '..name..'['..index..'] = '..value) -- debug   
        
        elseif type == FUNC_STMT then
            state.f[name] = value
            print('Assigned '..name..' = \n'..astToStr(state.f[name])) -- debug
        
        else
            if not index then index = 'nil' end -- debug
            print('ERROR: Unhandled var assignment: '..name..', '..type..', '..val..', '..index)
        end
    end


    -- getVar
    -- Called to get the value of the given variable
    -- Accepts: name  = Variable name
    --          type  = Variable type, either SIMPLE_VAR or ARRAY_VAR, or FUNC_STMT
    --          index = Array index. Required if type = ARRAY_VAR
    -- Returns: 
    local function getVar(name, type, index)
        if type == SIMPLE_VAR then
            return state.v[name]

        elseif type == ARRAY_VAR then
            return state.a[name][index]

        elseif type == FUNC_STMT then
            return state.f[name]

        else
            if not index then index = 'nil' end
            print('ERROR: Unhandled var assignment: '..name..', '..type..', '..val..', '..index)
        end
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

        -- If type is ARRAY_VAR, next val is NUMLIT_VAL, then array index
        if type == ARRAY_VAR then
            advanceNode()
            advanceNode()
            index = strToNum(currVal)
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
    local function parseAndGetVar()
        local name, type, index = parseVar()
        local value = getVar(name, type, index)
        return name, type, value, index
    end


    -- interp Dugong processing functions --
    ----------------------------------------
    -- doSYMBOL
    -- Called when the specified SYMBOL is encountered in the AST.
    -- Each function calls advanceNode to set currKey and currVal,
    -- then acts accordingly, based on its contents.
    -- Accepts/Returns: Function specific
    -- Scope: Intentionally global

    -- doSTMT_LIST
    -- Loops through a statement list.
    -- Accepts/Returns: None
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
            if currAST <= 0 or coroutine.status(astParser[currAST]) == 'dead' then
                break
            end

            -- call appropriate function based on currVal
            print('In '..debug.getinfo(1, 'n').name) --debug output
            printDebugString()  -- debug output

            if currVal == INPUT_STMT then no_advance = doINPUT_STMT()
            elseif currVal == PRINT_STMT then no_advance = doPRINT_STMT() 
            elseif currVal == FUNC_STMT then no_advance = doFUNC_STMT() 
            elseif currVal == CALL_FUNC then no_advance = doCALL_FUNC() 
            elseif currVal == IF_STMT then no_advance = doIF_STMT() 
            elseif currVal == WHILE_STMT then no_advance = doWHILE_STMT()
            elseif currVal == ASSN_STMT then no_advance = doASSN_STMT()
            else
                print('ERROR: Unhandled STMT in '..debug.getinfo(1, 'n').name) -- debug) -- debug
                printDebugString()
            end
        end
    end


    -- doINPUT_STMT
    -- Prompts user for a string value and assigns it to state var
    -- Accepts/Returns: None
    function doINPUT_STMT()
        advanceNode()
        -- print('In '..debug.getinfo(1, 'n').name) --debug output
        -- printDebugString()  -- debug output

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
        -- print('A - In '..debug.getinfo(1, 'n').name) --debug output
        -- printDebugString()  -- debug output
        
        -- handle CR_OUT (Print out a CR)
        if currVal == CR_OUT then
            outcall('\n')

        -- handle STRLIT_OUT 
        elseif currVal == STRLIT_OUT then
            -- next val is string to print
            advanceNode()
            outcall(currVal)

        -- handle BIN_OP
        elseif currVal == BIN_OP then
            outcall(doBIN_OP())

        -- handle UN_OP
        elseif currVal == UN_OP then
            outcall(doUN_OP())
        
        -- handle SIMPLE_VAR and ARRAY_VAR
        elseif currVal == SIMPLE_VAR  or currVal == ARRAY_VAR then
            local name, type, value, index = parseAndGetVar()
            outcall(value)

        -- unhandled
        else
            print('ERROR: Unhandled case encountered in '..debug.getinfo(1, 'n').name) -- debug
            printDebugString()
        end
    end


    -- doFUNC_STMT
    -- Processes a function definition and saves it to state
    -- Accepts/Returns: None
    function doFUNC_STMT()
        advanceNode()
        -- print('In '..debug.getinfo(1, 'n').name) --debug output
        -- printDebugString()  -- debug output

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
        -- print('In '..debug.getinfo(1, 'n').name) --debug output
        -- printDebugString()  -- debug output

        -- curr val is func name, get its ast and parse it
        local ast = getVar(currVal, FUNC_STMT)
        interpSTMT_LIST(ast)
    end

    
    -- doIF_STMT
    -- Processes an if statment and the necessary case's STMT_LIST
    -- Accepts: None (single var 'cond_hit' is only used in recursive calls)
    -- Returns: None
    function doIF_STMT(cond_hit)
        advanceNode()
        print('In '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output
        local value, execute = nil
        local matched = false   -- denote if we've matched a cond at this depth

        -- function to call to attempt to run a STMT_LIST
        -- only runs it if we haven't matched the if cond yet.
        function runstmt(stmt_list)
            if cond_hit then
                -- print('cond_hit = true. SKIPPING:') --debug
                print(astToStr(stmt_list))
            else
                -- print('cond_hit = false. RUNNING.') --debug
                interpCOND_STMT(stmt_list)
            end
        end

        -- Invariant:
        -- Curr node's val is an operator (BIN_OP or UN_OP) or
        -- NUMLIT_VAL or BOOLIT_VAL, OR it's a STMT_LIST.
        -- OR If it's not, we're done with the if statment,
        -- return to take us back to doSTMT_LIST

        -- handle end of statement (denoted by currCal == something other than what we expect)
        if not (currVal == BIN_OP or currVal == UN_OP or currVal == NUMLIT_VAL
                or currVal == BOOLLIT_VAL or type(currVal) == "table") then 
                    -- print('Done w If') --debug
                    return end

        -- handle BIN_OP 
        if currVal == BIN_OP then 
            value = doBIN_OP()
            advanceNode()
            execute = currVal
            -- print('b: '..value..':'..astToStr(execute))  

        -- handle UN_OP 
        elseif currVal == UN_OP then
            value = doUN_OP()   
            advanceNode()
            execute = currVal
            -- print('u: '..value..':'..astToStr(execute))

        -- handle NUMLIT and BOOLLIT 
        elseif currVal == NUMLIT_VAL or currVal == BOOLLIT_VAL then
            advanceNode()
            value = currVal
            -- print('comparing '..value) -- debug
            advanceNode()
            execute = currVal
            -- print('l: '..value..':'..astToStr(execute))

        -- handle STMT_LIST, i.e the if's "else" branch
        elseif type(currVal) == "table" then
            value = 1 -- set to true so execute gets done if we haven't matched
            execute = currVal
            -- print('e: '..value..':'..astToStr(execute))

        -- unhandled
        else
            print('Unhandled value in IF_STMT: '..currVal)
        end

        -- Do the correct action based on value (assigned above)
        if boolToInt(value) == 1 then 
            -- print('eval TRUE -')
            matched = true
            runstmt(execute)
        -- else
        --     print ('eval FALSE -')
        --     print('Skipping:')
        --     print(astToStr(execute))
        end

        -- Process the rest of the if stmt recursively, passing if
        -- we have matched a cond (either in this iteration or previously)
        doIF_STMT((matched or cond_hit))

        -- return true to tell do_STMT_LIST not to advanceNode()
        -- (because we did it in this function already)
        return true 
    end

    
    -- doWHLIE_STATMENT
    -- Processes a while statment and its STMT_LIST accordingly
    -- Accepts/Returns: None
    function doWHILE_STMT()
        advanceNode()
        print('In '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output
    end

    
    -- doASSN_STMT
    -- Process a VAR = VALUE type statment
    -- Accepts/Returns: None
    function doASSN_STMT()
        advanceNode()
        -- print('In '..debug.getinfo(1, 'n').name) --debug output
        -- printDebugString()  -- debug output

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
            local name2, type2, value2, index2 = parseAndGetVar()
            setVar(name, type, value2, NUMLIT_VAL, index)
        end
    end

    
    -- doBIN_OP
    -- Accepts: None
    -- Returns: Result of operation 1 or 0 for boolean operators, else an int
    n = 0
    function doBIN_OP()        
        n = n+1
        advanceNode()
        print('In ('..n..'): '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output

        local lvalue, ltype = nil   -- left operand
        local rvalue, rtype = nil   -- right operand
        local operator = currVal    -- operator

        -- For both the l and r values, the following invariants hold:
        -- Next node == BIN_OP, UN_OP, NUM_LIT, SIMPLE_VAR, or ARRAY_VAR
        -- If BIN_OP or UN_OP, recursively call this func to process them.
        -- Else, the next value is an operand.

        -- evaluate lvalue
        advanceNode()
        if currVal == BIN_OP then 
            lvalue = doBIN_OP() 
        elseif currVal == UN_OP then
            lvalue = doUN_OP()
        else
            ltype = currVal
            advanceNode()        
            lvalue = convertVal(ltype, currVal)           
        end
        
        -- evaluate rvalue
        advanceNode()
        if currVal == BIN_OP then 
            rvalue = doBIN_OP() 
        elseif currVal == UN_OP then
            rvalue = doUN_OP()
        else
            rtype = currVal
            advanceNode()        
            rvalue = convertVal(rtype, currVal)
        end

        -- Necessary nodes processed, determine result and return.
        local result = false
        if operator == '&&' then
            if lvalue and rvalue then result = true end
        elseif operator == '||' then
            if lvalue or rvalue then result = true end
        elseif operator == '==' then
            if lvalue == rvalue then result = true end
        elseif operator == '!=' then
            if lvalue ~= rvalue then result = true end
        elseif operator == '<' then
            if lvalue < rvalue then result = true end
        elseif operator == '<=' then
            if lvalue >= rvalue then result = true end
        elseif operator == '>' then
            if lvalue > rvalue then result = true end
        elseif operator == '>=' then
            if lvalue >= rvalue then result = true end
        elseif operator == '+' or operator == '-' or 
                operator == '*' or operator == '/' or
                operator == '%' then result = evalArith(lvalue, rvalue, operator)
        else
            print('Unhandled operator encountered: '..operator)
        end

        -- put bools in str form?
        if result == true then result = 'true'
        elseif result == false then result = 'false'end
        -- local disp = result -- debug
        -- print('BIN_OP results: '..lvalue..' '..operator..' '..rvalue..' = '..result) -- debug
        return result
    end


    -- doUN_OP
    -- Accepts: None
    -- Returns: Result of operation - 1 or 0 for boolean operators, else an int
    m = 0
    function doUN_OP()        
        m = m+1
        advanceNode()
        -- print('In ('..m..'): '..debug.getinfo(1, 'n').name) --debug output
        -- printDebugString()  -- debug output

        local value, type, result = nil -- operand
        local operator = currVal        -- operator

        -- Tthe following invariants hold:
        -- Next node == BIN_OP, UN_OP, NUM_LIT, SIMPLE_VAR, or ARRAY_VAR
        -- If BIN_OP or UN_OP, recursively call this func to process them.
        -- Else, the current node value is our operand type,
        -- and the next value is the operand.

        advanceNode()
        if currVal == BIN_OP then 
            value = doBIN_OP() 
        elseif currVal == UN_OP then
            value = doUN_OP()
        else
            type = currVal
            advanceNode()        
            value = convertVal(type, currVal)
        end

        -- determine result
        if operator == '-' or operator == '!' then
            if type == NUMLIT_VAL then result = -value
            elseif type == BOOLLIT_VAL then 
                if value == 0 then result = 1
                else result = 0 end
            end
        else
            result = value
        end

        -- print('UN_OP results: '..operator..value..' = '..result) -- debug
        return result
    end

    
    -- interpSTMT_LST
    -- Called to process an AST STMT_LIST.
    -- Called first from interp main function body, then
    -- from any other func that encounters a STMT_LIST
    -- Acccepts: an AST node of type STMT_LIST
    function interpSTMT_LIST(ast)
        print('-- Processing AST:') -- Debug output
        print(astToStr(ast))        -- Debug output

        -- increase ast parser count by 1 and init ast parser coroutine
        currAST = currAST + 1
        ASTrees[currAST] = ast
        firstFlag[currAST] = false
        stmtList[currAST] = {}
        ifList[currAST] = nil
        subtreeDone[currAST] = false
        astParser[currAST] = coroutine.create(iterateSubtree)

        local firstFlag = false;
        while currAST > 0 and coroutine.status(astParser[currAST]) ~= 'dead' do
            print('In main loop # '..currAST) -- debug
            if not firstFlag then advanceNode() end
            doSTMT_LIST()
            currAST = currAST - 1
            firstFlag = true
            if currAST <= 0 then break end
        end
    end

    function interpCOND_STMT(ast)
        print('-- Processing COND AST:') -- Debug output
        print(astToStr(ast))        -- Debug output

        -- note currAST count. We will break when we hit it
        local baseASTCount = currAST

        -- increase ast parser count by 1 and init ast parser coroutine
        currAST = currAST + 1
        ASTrees[currAST] = ast
        firstFlag[currAST] = false
        stmtList[currAST] = nil
        ifList[currAST] = nil
        subtreeDone[currAST] = false
        astParser[currAST] = coroutine.create(iterateSubtree)
        
        local firstFlag = false;
        while currAST > 0 and coroutine.status(astParser[currAST]) ~= 'dead' do
            print('In COND loop # '..currAST) -- debug
            if not firstFlag then advanceNode() end
            doSTMT_LIST()
            currAST = currAST - 1
            firstFlag = true
            if currAST <= baseASTCount then break end
        end
    end




    -- interp function body --
    ---------------------------
    -- The root node is a STMT_LIST, start the interp process on it.
    -- After processing, return the state table
    interpSTMT_LIST(start_ast) 
    return state                
end

-- Export the interpit module
return interpit

