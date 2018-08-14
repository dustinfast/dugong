#!/usr/bin/env lua

-- The bridge between the parser and interpreter.
-- Glenn G. Chappell
-- 6 Feb 2018


lexer = require "lexit"


-- Our "program", which is sent to the lexer
-- Change this string and see what happens.
program = "-1-1-1-1"

-- Above, "\a" is an alarm character. It may make a beep sound when
-- printed. It is included as an example of an illegal character.


-- Print the input ("program")
io.write("*** Lexer Input:\n")
io.write(program)
io.write("\n\n")

-- Lex away and print the output as we go
io.write("*** Lexer Output:\n")
n = 1
for lexstr, cat in lexer.lex(program) do
    print('\n')
    n = n+1
    lexer.preferOp()
    -- if n == 2 then lexer.preferOp() end
    print(lexstr, lexer.catnames[cat])
end



