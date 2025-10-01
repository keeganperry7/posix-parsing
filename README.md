# Lean Formalisation of POSIX Regular Expression Parsing

This repository contains the formalisation of Sulzmann and Lu's derivative-based
regular expression POSIX parsing algorithm.

## File Overview
- `Regex`: definition of regexes and Brzozowski derivatives.
- `Value`: definition of the parse tree representation.
- `Parser`: implementation of Sulzmann and Lu's parsing algorithm.
- `POSIX`: definition of the POSIX specification for parse trees.
- `Correctness`: correctness of parsing algorithm with respect to POSIX
  definition.
- `Examples`: running examples of the parsing algorithm.