An R-WHILE Interpreter
======================

An interpreter of Haskell for R-WHILE, a reversible version of WHILE languae [1].
(The parser uses parsec.)

To compile the interpreter, you need the following applications:

- Alex, version 3.1.4
- Happy, version 1.19.4

Because the interpreter requires a lot of memory, we have switched to OCaml version.

------------------------------------------------------------------------------

[1] Jones, Neil D. Computability and Complexity: From a Programming Perspective, MIT Press, 1997.
(Revised version available from <http://www.diku.dk/~neil/Comp2book.html>)