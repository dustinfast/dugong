#!/usr/bin/env lua
-- dugong.lua
-- Glenn G. Chappell
-- 29 Mar 2018
--
-- For CS F331 / CSCE A331 Spring 2018
-- REPL/Shell for Dugong Programming Language
-- Requires lexit.lua, parseit.lua, interpit.lua


-- ***** Load Modules *****


-- nice_require
-- Version of "require" with more graceful error message on failure.
function nice_require(modulename)
    assert(type(modulename) == "string")

    success, module = pcall(require, modulename)
    if not success then
        io.write("FATAL ERROR: Module '"..modulename.."'")
        io.write(" is not available.\n")
        io.write("Exiting.\n")
        io.write("\n")
        os.exit()
    end

    return module
end

lexit = nice_require "lexit"
-- Above is not used directly; check its existence to be user-friendly.
parseit = nice_require "parseit"
interpit = nice_require "interpit"


-- ***** Variables *****


local dugongstate  -- Dugong variable values


-- ***** Callback Functions for Interpreter *****


-- We define these functions so we can pass them to the interpreter.


-- inputLine
-- Input a line of text from standard input and return it in string
-- form, with no trailing newline.
function inputLine()
    local line = io.read("*l")
    if type(line) == "string" then
        return line
    else
        return ""
    end
end


-- outputString
-- Output the given string to standard output, with no added newline.
function outputString(s)
    -- print("***\n*** Outcall: ".. s .. "\n***\n")
    io.write(s)
end


-- ***** Debug functions *****

-- Function to print ast to console. For debug use.
-- Glenn G. Chappell, 2018
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
            -- if not first then
            --     print(", ")
            -- end
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

-- ***** Functions for Dugong REPL *****


-- printHelp
-- Print help for REPL.
local function printHelp()
    io.write("Type Dugong code to execute it.\n")
    io.write("Commands (these may be abbreviated;")
    io.write(" for example, \":e\" for \":exit\")\n")
    io.write("  :exit          - Exit.\n")
    io.write("  :run FILENAME  - Execute Dugong source file.\n")
    io.write("  :clear         - Clear Dugong state.\n")
    io.write("  :help          - Print help.\n")
end


-- elimSpace
-- Given a string, remove all leading & trailing whitespace, and return
-- result.
local function elimSpace(s)
    assert(type(s) == "string")

    local ss = s:gsub("^%s+", "")
    ss = ss:gsub("%s+$", "")
    return ss
end


-- elimLeadingNonspace
-- Given a string, remove leading non-whitespace, and return result.
local function elimLeadingNonspace(s)
    assert(type(s) == "string")

    local ss = s:gsub("^%S+", "")
    return ss
end


-- errMsg
-- Given an error message, prints it in flagged-error form, with a
-- newline appended.
local function errMsg(msg)
    assert(type(msg) == "string")

    io.write("*** ERROR - "..msg.."\n")
end


-- clearState
-- Clear Dugong state: functions, simple variables, arrays.
local function clearState()
    dugongstate = { f={}, v={}, a={} }
end


-- runDugong
-- Given a string, attempt to treat it as source code for a Dugong
-- program, and execute it. I/O uses standard input & output.
--
-- Parameters:
--   program  - Dugong source code
--   state    - Values of Dugong variables as in interpit.interp.
--   execmsg  - Optional string. If code parses, then, before it is
--              executed, this string is printed, followed by a newline.
--
-- Returns three values:
--   good     - true if initial portion of program parsed successfully;
--              false otherwise.
--   done     - true if parse reached end of program; false otherwise.
--   newstate - If good, done are both true, then new value of state,
--              updated with revised values of variables. Otherwise,
--              same as passed value of state.
--
-- If good and done are both true, then the code was executed.
function runDugong(program, state, execmsg)
    local good, done, ast = parseit.parse(program)
    local newstate
    if good and done then
        -- print('-- Parse OK.') -- Debug output
        -- writeAST(ast) -- Debug output
        if execmsg ~= nil then
            io.write(execmsg.."\n")
        end
        newstate = interpit.interp(ast, state, inputLine, outputString)
    else
        --print('-- Parse Failed.') -- Debug output   
        newstate = state
    end
    return good, done, newstate
end


-- runFile
-- Given filename, attempt to read source for a Dugong program from it,
-- and execute the program. If prinntmsg is true and the program parses
-- correctly, then print a message before executing the file.
function runFile(fname, printmsg)
    function readable(fname)
        local f = io.open(fname, "r")
        if f ~= nil then
            f:close()
            return true
        else
            return false
        end
    end

    local good, done

    if not readable(fname) then
        errMsg("Dugong source file not readable: '"..fname.."'")
        return
    end
    local source = ""
    for line in io.lines(fname) do
        source = source .. line .. "\n"
    end
    local execmsg
    if printmsg then
        execmsg = "EXECUTING FILE: '"..fname.."'"
    else
        execmsg = nil
    end
    good, done, dugongstate = runDugong(source, dugongstate, execmsg)
    if not (good and done) then
        errMsg("Syntax error in Dugong source file: '"..fname.."'")
    end
end


-- doReplCommand
-- Given input line beginning with ":", execute as REPL command. Return
-- true if execution of REPL should continue; false if it should end.
function doReplCommand(line)
    assert(line:sub(1,1) == ":")
    if line:sub(1,2) == ":e" then
        return false
    elseif line:sub(1,2) == ":h" then
        printHelp()
        return true
    elseif line:sub(1,2) == ":c" then
        clearState()
        io.write("Dugong state cleared\n")
        return true
    elseif line:sub(1,2) == ":r" then
        fname = elimLeadingNonspace(line:sub(3))
        fname = elimSpace(fname)
        if (fname == "") then
            errMsg("No filename given")
        else
            runFile(fname, true)  -- true: Print execution message
        end
        return true
    else
        errMsg("Unknown command")
        return true
    end
end


-- repl
-- Dugong REPL. Prompt & get a line. If it is blank, then exit. If it
-- looks like the filename of a Dugong source file, then get Dugong
-- source from it, execute, and exit. Otherwise, treat line as Dugong
-- program, and attempt to execute it. If it looks like an incomplete
-- Dugong program, then keep inputting, and continue to attempt to
-- execute. REPEAT.
function repl()
    local line, good, done, continueflag
    local source = ""

    printHelp()
    while true do
        -- Prompt
        if source == "" then
            io.write("\n>> ")
        else
            io.write(".. ")
        end

        -- Input a line + error check
        line = io.read("*l")  -- Read a line
        if not line then      -- Error (EOF?) on input
            io.write("\n")
            break
        end
        line = elimSpace(line)

        -- Handle input, as approprite
        if line:sub(1,1) == ":" then    -- Command
            source = ""
            continueflag = doReplCommand(line)
            if not continueflag then
                break
            end
        else                            -- Dugong code
            source = source .. line
            good, done, dugongstate = runDugong(source, dugongstate)
            if (not good) and done then
                source = source .. "\n" -- Continue inputting source
            else
                source = ""             -- Start over
            end
            if not done then
                errMsg("Syntax error")
            end
        end
    end
end


-- ***** Main Program *****


-- Initialize Dugong state
clearState()

-- Command-line argument? If so treat as Dugong source filename, read
-- source, and execute.
if arg[1] ~= nil then
    runFile(arg[1], false)  -- false: Do not print execution message
    -- io.write("\n")
    -- io.write("Press ENTER to quit ")
    -- io.read("*l")
-- Otherwise, fire up the Dugong REPL.
else
    repl()
end

