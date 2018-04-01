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

parserNames = {"CONST", "BOOL", "STR"}

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
    "STMT_LIST", "INPUT_STMT", "PRINT_STMT", "FUNC_STMT",
    "CALL_FUNC", "IF_STMT", "WHILE_STMT", "ASSN_STMT", "CR_OUT",
    "STRLIT_OUT", "BIN_OP", "UN_OP", "NUMLIT_VAL", "BOOLLIT_VAL",
    "SIMPLE_VAR", "ARRAY_VAR"}



----- Utility Functions -----

-- numToInt (G Chappell, 2018)
-- Given a number, return the number rounded toward zero.
local function numToInt(n)
    assert(type(n) == "number")

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
    assert(type(s) == "string")

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
    assert(type(n) == "number")

    return ""..n
end


-- boolToInt (G Chappell, 2018)
-- Given a boolean, return 1 if it is true, 0 if it is false.
local function boolToInt(b)
    assert(type(b) == "boolean")

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
function astToStr(ast)
    if type(ast) == "number" then
        local name = symbolNames[ast]
        if name == nil then
            return "<Unknown numerical constant: "..ast..">"
        else
            return name
        end
    elseif type(ast) == "string" then
        return '"'..ast..'"'
    elseif type(ast) == "boolean" then
        if ast then
            return "true"
        else
            return "false"
        end
    elseif type(ast) == "table" then
        local first = true
        local result = "{"
        for k = 1, #ast do
            if not first then
                result = result .. ","
            end
            result = result .. astToStr(ast[k])
            first = false
        end
        result = result .. "}"
        return result
    elseif type(ast) == "nil" then
        return "nil"
    else
        return "<"..type(ast)..">"
    end
end


-- printDebugString
-- prints the given key value in a convenient format for debug
function printDebugString(key, val)
    -- Build debug output
    if key == CONST then
        val = symbolNames[val]
    end
    key = parserNames[key]
    print(key)
    print(val)
    io.read("*l") -- pause
end

-- evalArith
-- Accepts: lval, rval, and operator of a binary arithmetic expr
-- Returns: result of the expression, or 0 nil if indeterminate
function evalArith (lval, rval, op)
    if op == "+" then return lval + rval
    elseif op == "-" then return lval - rval
    elseif op == "*" then return lval * rval
    elseif op == "/" then return lval / rval
    elseif op == "%" then return lval % rval
    else
      Print("ERROR: Invalid Operator Encountered: "..op)
    end
end

-- parseAST
-- A recursive coroutine yielding node values via inorder traversal
-- Accepts: An AST in table form.
-- Yields: AST node value as two vars. A key value pair of any of the following formats:
--              {"CONST", NUMBER}   = A numeric value corresponding to symbolNames[NUMBER]
--              {"LIT", LITERAL}    = A string or numeric literal, in string form
--              {"BOOL", bool}      = A bool in string form, either true or false
--              {"ERR", string}     = An error in string form
-- Ex: given AST "{STMT_LIST,{PRINT_STMT,{STRLIT_OUT,"Hello World"}}}",
--  yields {"CONST", 1}, {"CONST", 3}, {"CONST", 10}, {"LIT", "Hello World"}
function parseAST(ast)
    -- If node is a symbolic constant, return number for that constant:
    if type(ast) == "number" then
        local name = symbolNames[ast]
        if name == nil then
            coroutine.yield("ERROR", "Unknown constant: "..ast)
        else
            coroutine.yield(CONST, ast)
        end
        
    -- If node is a string value:
    elseif type(ast) == "string" then
        coroutine.yield(STR, ast)
    
    -- If node is a bool value
    elseif type(ast) == "boolean" then
        if ast then
            coroutine.yield(BOOL, "true")
        else
            coroutine.yield(BOOL, "false")
        end
    
    -- If node is a table, do recursive call to parse it:
    elseif type(ast) == "table" then
        local first = true
        for k = 1, #ast do  -- Note: ipairs doesn't work here. Why?
            parseAST(ast[k])
            first = false
        end
    
    -- If node is empty or of an unexpected type:
    elseif type(ast) == "nil" then
        coroutine.yield("ERROR", "Empty tree or node encountered.")
    else
        coroutine.yield("ERROR", "Invalid type encountered: "..type(ast))
    end
end


----- Primary Function for Client Code -----
--------------------------------------------

-- interp
-- Interpreter, given an AST returned by parseit.parse.
-- Assumes: AST is valid/correct
-- Parameters:
--   ast     - AST constructed by parseit.parse
--   state   - Table holding Dugong variables & functions
--             - AST for function xyz is in state.f["xyz"]
--             - Value of simple variable xyz is in state.v["xyz"]
--             - Value of array item xyz[42] is in state.a["xyz"][42]
--   incall  - Function to call for line input
--             - incall() inputs line, returns string with no newline
--   outcall - Function to call for string output
--             - outcall(str) outputs str with no added newline
--             - To print a newline, do outcall("\n")
-- Returns: state, updated with changed variable values
function interpit.interp(ast, state, incall, outcall)
    -- Each local interpretation function is given the AST for the
    -- portion of the code it is interpreting. The function-wide
    -- versions of state, incall, and outcall may be used. The
    -- function-wide version of state may be modified as appropriate.

    
    -- interp utility functions --
    ------------------------------

    -- getNextNode
    -- Gets and returns the key/val associated with the next AST node
    -- Accepts: None
    -- Returns: key/val
    function getNextNode()
        local ok, key, val = coroutine.resume(astParser, ast)        
        return key, val      
    end


    -- interp Dugong processing functions --
    ----------------------------------------
    -- doXXXX
    -- Called when the specified node XXXX is encountered in the AST.
    -- Each function gets the next nodes key/val then takes action
    -- based on its contents
    -- Accepts/Returns: Function specific

    -- Processes statement lists and calls appropriate handler function
    -- Accepts/Returns: None
    function doSTMT_LIST()
        while (true) do
            -- break if coroutine dead
            if coroutine.status(astParser) == "dead" then
                break
            end

            -- get Next node and call appropriate function based on it
            local key, val = getNextNode()
            print("In "..debug.getinfo(1, "n").name) --debug output
            printDebugString(key, val)  -- debug output

            if key == CONST then
                --TODO: elseif
                if val == INPUT_STMT then doINPUT_STMT()
                elseif val == PRINT_STMT then doPRINT_STMT() 
                elseif val == FUNC_STMT then doFUNC_STMNT() 
                elseif val == CALL_FUNC then doCALL_FUNC() 
                elseif val == IF_STMT then doIF_STMT() 
                elseif val == WHILE_STMT then doWHILE_STMT()
                -- if val == ASSN_STMT then doASSN_STMT() end
                -- if val == CR_OUT then doCR_OUT() end
                -- if val == STRLIT_OUT then doSTRLIT_OUT() end
                -- if val == BIN_OP then doBIN_OP() end
                -- if val == UN_OP then doUN_OP() end
                -- if val == NUMLIT_VAL then doNUMLIT_VAL() end
                -- if val == BOOLLIT_VAL then doBOOLLIT_VAL() end
                elseif val == SIMPLE_VAR then doSIMPLE_VAR()
                elseif val == ARRAY_VAR then dodoARRAY_VAR()
                else
                    print("ERROR: Unhandled statement encountered: ") -- debug
                    printDebugString(key, val)
                end
            end
        end
    end

    -- Processes Input statments
    -- Accepts/Returns: None
    function doINPUT_STMT()
        local key, val = getNextNode()
        print("In "..debug.getinfo(1, "n").name) --debug output
        printDebugString(key, val)  -- debug output
    end

    -- Processes print statements
    -- Accepts/Returns:None
    function doPRINT_STMT()
        local key, val = getNextNode()
        print("1: In "..debug.getinfo(1, "n").name) --debug output
        printDebugString(key, val)  -- debug output
        
        -- handle CR_OUT (Print out a CR)
        if val == CR_OUT then
            outcall("\n")

        -- handle STRLIT_OUT (Print out the next node, a string)
        elseif val == STRLIT_OUT then
            key, val = getNextNode()
            print("2: In "..debug.getinfo(1, "n").name) --debug output
            outcall(val)

        -- handle BIN_OP
        elseif val == BIN_OP then
            print("3: In "..debug.getinfo(1, "n").name) --debug output
            outcall(doBIN_OP())

        -- handle UN_OP
        elseif val == UN_OP then
            print("4: In "..debug.getinfo(1, "n").name) --debug output
            outcall(doBIN_OP())
        
        -- unhandled
        else
            print("ERROR: Unhandled case encountered: ") -- debug
            printDebugString(key, val)
        end
    end

    -- Processes binary expressions
    -- Accepts: None
    -- Returns: Result of the expression
    n = 0
    function doBIN_OP()        
        n = n+1
        local key, val = getNextNode()
        print(n.." : A In "..debug.getinfo(1, "n").name) --debug output
        printDebugString(key, val)  -- debug output

        local lvalue, rvalue = 0
        local operator = val

        -- evaluate lvalue
        key, val = getNextNode()
        print(n.." : B In "..debug.getinfo(1, "n").name) --debug output        
        printDebugString(key, val)  -- debug output

        if val == BIN_OP then 
            print(n.." lvalue =doBinOp")
            lvalue = doBIN_OP() 
        elseif val == UN_OP then
            lvalue = doUN_OP()
        else
            lvalue = val
        end
        print(n.." Set lvalue: "..lvalue) -- debug
        
        -- evaluate rvalue
        key, val = getNextNode()
        print(n.." : C In "..debug.getinfo(1, "n").name) --debug output        
        printDebugString(key, val)  -- debug output

        if val == BIN_OP then 
            print(n.." rvalue =doBinOp")            
            rvalue = doBIN_OP() 
        elseif val == UN_OP then
            rvalue = doUN_OP()
        else
            rvalue = val
        end
        print(n.." Set rvalue: "..rvalue) -- debug

        local result = evalArith(lvalue, rvalue, operator)
        print("BIN_OP results: "..lvalue..' '..operator..' '..rvalue..' = '..result)
        return evalArith(lvalue, rvalue, operator)
    end

    -- Processes unary expressions
    -- Accepts: None
    -- Returns: Results of the expression
    function doUN_OP()

    end


    -- interp function body --
    ---------------------------

    print("-- Processing AST:") -- Debug output
    print(astToStr(ast))        -- Debug output

    -- Ini ast parsing coroutine
    astParser = coroutine.create(parseAST)

    -- Start the process of getting each node from the
    -- ast in the order needed for processing (preorder)
    while (true) do
        print("In main while loop")
        -- break if coroutine dead
        if coroutine.status(astParser) == "dead" then
            break
        end

        -- get current node key/val
        local key, val = getNextNode()
        printDebugString(key, val) -- debug output

        -- Do actions according to node
        if key == CONST then
            if val == STMT_LIST then
                doSTMT_LIST()
            else
                print("ERROR: Unhandled CONST encountered: ")
                printDebugString(key, val)
                break
            end
        else
            print("ERROR: Unhandled key type encountered: ")
            printDebugString(key, val)
        end
    end
    
    return state
end


-- ***** Module Export *****
return interpit

