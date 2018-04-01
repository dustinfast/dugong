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
local CONST = 1
local BOOL = 2
local STR = 3

local parserNames = {'CONST', 'BOOL', 'STR'}

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
    assert(type(s) == 'string')

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
-- Given a boolean, return 1 if it is true, 0 if it is false.
local function boolToInt(b)
    assert(type(b) == 'boolean')

    if b then
        return 1
    else
        return 0
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


-- parseAST_FUNC
-- A helper for parseAST. Yields a functions stmt list as an intact AST
local function parseAST_FUNC()

end

-- parseAST
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
local function parseAST(node)
    -- If node is a symbolic constant, return number for that constant:
    if type(node) == 'number' then
        local name = symbolNames[node]
        if name == nil then
            coroutine.yield('ERROR', 'Unknown constant: '..node)
        else
            -- if node == FUNC_STMT then
            --     -- tield the STMT_LIST as an AST
            -- end
            coroutine.yield(CONST, node)
        end
        
    -- If node is a string value:
    elseif type(node) == 'string' then
        coroutine.yield(STR, node)
    
    -- If node is a bool value
    elseif type(node) == 'boolean' then
        if node then
            coroutine.yield(BOOL, 'true')
        else
            coroutine.yield(BOOL, 'false')
        end
    
    -- If node is a table, do recursive call to parse it:
    elseif type(node) == 'table' then
        local first = true
        for k = 1, #node do  -- Note: ipairs doesn't work here. Why?
            parseAST(node[k])
            first = false
        end
    
    -- If node is empty or of an unexpected type:
    elseif type(node) == 'nil' then
        coroutine.yield('ERROR', 'Empty tree or node encountered.')
    else
        coroutine.yield('ERROR', 'Invalid type encountered: '..type(node))
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
function interpit.interp(ast, state, incall, outcall)
    -- Each local interpretation function is given the AST for the
    -- portion of the code it is interpreting. The function-wide
    -- versions of state, incall, and outcall may be used. The
    -- function-wide version of state may be modified as appropriate.

    -- interp variables --
    ----------------------
    local astParser = coroutine.create(parseAST) -- ast parsing coroutine
    local currKey, currVal = nil -- key and val of astParser's current node.


    -- interp helper funcs --
    -------------------------

    -- advanceNode
    -- Advances astParser and assigns attributes to currKey and currVal
    local function advanceNode()
        local ok = nil
        ok, currKey, currVal = coroutine.resume(astParser, ast)          
        assert(ok)    
    end


    -- printDebugString
    -- prints the current key/value in a conveient form. For debug.
    local function printDebugString()
        local key, val = nil
        
        if currKey == nil then key = "nil" 
        else key = parserNames[currKey] end

        if currVal == nil then val = "nil" 
        elseif currKey == CONST then
            val = symbolNames[currVal]
        else val = currVal end

        print('{ '..key..', '..val..' }')
        io.read('*l') -- pause
    end


    -- setVar
    -- Called to set a varable of the given name/type to the given value
    -- Accepts: name  = Variable name
    --          type  = Variable type, either SIMPLE_VAR or ARRAY_VAR
    --          value = Variable value
    --          vtype = Type of value, either NUMLIT_VAL or BOOLLIT_VAL
    --          index = Array index. Required if type = ARRAY_VAR
    -- Returns: None
    local function setVar(name, type, value, vtype, index)
        if type == SIMPLE_VAR then
            state.v[name] = value
            print('Assigned '..name..' = '..value) -- debug

        elseif type == ARRAY_VAR then
            -- If state.a[name] doesn't exit, create it
            local table = state.a[name]
            if not table then state.a[name] = {} end

            -- insert new value
            state.a[name][index] = value
            print('Assigned '..name..'['..index..'] = '..value) -- debug   

        else
            if not index then index = 'nil' end -- debug
            print('ERROR: Unhandled var assignment: '..name..', '..type..', '..val..', '..index)
        end
    end


    -- getVar
    -- Called to get the value of the given variable
    -- Accepts: name  = Variable name
    --          type  = Variable type, either SIMPLE_VAR or ARRAY_VAR
    --          index = Array index. Required if type = ARRAY_VAR
    -- Returns: 
    local function getVar(name, type, index)
        if type == SIMPLE_VAR then
            return state.v[name]

        elseif type == ARRAY_VAR then
            return state.a[name][index]

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

    -- Accepts/Returns: None
    function doSTMT_LIST()
        while (true) do
            -- update currKey and currVal
            advanceNode()
            
            -- If coroutine dead, we're done
            if coroutine.status(astParser) == 'dead' then
                break
            end

            -- get Next node and call appropriate function based on it
            print('In '..debug.getinfo(1, 'n').name) --debug output
            printDebugString()  -- debug output

            if currVal == INPUT_STMT then doINPUT_STMT()
            elseif currVal == PRINT_STMT then doPRINT_STMT() 
            elseif currVal == FUNC_STMT then doFUNC_STMT() 
            elseif currVal == CALL_FUNC then doCALL_FUNC() 
            elseif currVal == IF_STMT then doIF_STMT() 
            elseif currVal == WHILE_STMT then doWHILE_STMT()
            elseif currVal == ASSN_STMT then doASSN_STMT()
            -- elseif currVal == SIMPLE_VAR then doSIMPLE_VAR()
            -- elseif currVal == ARRAY_VAR then dodoARRAY_VAR()
            else
                print('ERROR: Unhandled statement encountered'..debug.getinfo(1, 'n').name) -- debug) -- debug
                printDebugString()
            end
        end
    end


    -- I.e. assigns a string value an ARRAY_VAR or SIMPLE_VAR
    -- Accepts/Returns: None
    function doINPUT_STMT()
        advanceNode()
        print('In '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output

        -- get var attributes
        local name, type, index = parseVar()

        -- Prompt for input and do assignment
        local value = incall()
        setVar(name, type, value, NUMLIT_VAL, index)
    end


    -- Processes print statements
    -- Accepts/Returns:None
    function doPRINT_STMT()
        advanceNode()
        print('A - In '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output
        
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


    -- Accepts/Returns: None
    function doFUNC_STMT()
        advanceNode()
        print('In '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output

        -- curr val is func name
        local name = currVal
        -- local ast = 
    end


    -- Accepts/Returns: None
    function doCALL_FUNC()
        advanceNode()
        print('In '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output
    end

    
    -- Accepts/Returns: None
    function doIF_STMT()
        advanceNode()
        print('In '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output
    end

    
    -- Accepts/Returns: None
    function doWHILE_STMT()
        advanceNode()
        print('In '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output
    end

    
    -- Accepts/Returns: None
    function doASSN_STMT()
        advanceNode()
        print('In '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output

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

    
    -- Accepts/Returns: None/Result of the expression
    n = 0
    function doBIN_OP()        
        n = n+1
        advanceNode()
        print('START - '..n..': '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output

        local lvalue, ltype = nil   -- left operand
        local rvalue, rtype = nil   -- right operand

        -- The current node's value is our operator
        local operator = currVal

        -- For both the l and r values, the following invariants hold:
        -- Next node == BIN_OP, UN_OP, NUM_LIT, SIMPLE_VAR, or ARRAY_VAR
        -- If BIN_OP or UN_OP, recursively call this func to process them.
        -- Else, the current node value is our operand type,
        -- and the next value is the operand.

        -- evaluate lvalue
        advanceNode()
        if currVal == BIN_OP then 
            lvalue = doBIN_OP() 
        elseif currVal == UN_OP then
            lvalue = doUN_OP()
        else
            ltype = currVal
            advanceNode()        
            lvalue = currVal
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
            rvalue = currVal
        end

        -- Necessary nodes processed, get result and return.
        local result = evalArith(lvalue, rvalue, operator) -- debug
        print('BIN_OP results: '..lvalue..' '..operator..' '..rvalue..' = '..result) -- debug
        return evalArith(lvalue, rvalue, operator)
    end


    -- Accepts/Returns: None/Result of the expression
    m = 0
    function doUN_OP()        
        m = m+1
        advanceNode()
        print('START - '..m..': '..debug.getinfo(1, 'n').name) --debug output
        printDebugString()  -- debug output

        local value, vtype, result = nil
        
        -- The current node's value is our operator
        local operator = currVal

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
            vtype = currVal
            advanceNode()        
            value = currVal
        end

        if operator == '+' then
            result = value
        elseif operator == '-' then
            result = -value
        end

        -- Necessary nodes processed, return result.        
        print('UN_OP results: '..operator..value..' = '..result) -- debug
        return result
    end


    -- interp function body --
    ---------------------------
    print('-- Processing AST:') -- Debug output
    print(astToStr(ast))        -- Debug output

    -- Start the process of getting each node from the
    -- ast in the order needed for processing (preorder)
    while (true) do
        print('In main while loop') -- debug

        -- break if coroutine dead
        if coroutine.status(astParser) == 'dead' then
            break
        end

        -- update currKey and currVal
        advanceNode()
        printDebugString() -- debug output

        -- Do actions according to currKey and currVal
        if currVal == STMT_LIST then
            doSTMT_LIST()
        else
            print('ERROR: Unhandled CONST encountered: ')
            printDebugString()
            break
        end
    end
    
    return state
end


-- ***** Module Export *****
return interpit

