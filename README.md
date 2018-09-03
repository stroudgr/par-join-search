# README for Victor

## Trying some examples

If you want to run an example of our program, you'll need [Lark](https://github.com/lark-parser/lark) and [Z3](https://github.com/Z3Prover/z3) (python version) libraries.

To try an example, run the main program:

``python main.py search name_of_program``

Simple examples that should always work : mts, sum, max, 2max, etc... See more in the folder "examples".

## Basic file structure (of my work)

First look in main.py. You'll see a [call](https://github.com/stroudgr/par-join-search/blob/8b2c4f408d135445c975a5ebb6fc0ec1ce50dfd9/main.py#L55) to the method jsp.search. The (optional) arguments determine which terms the search starts with, as well as how long to run with those start terms. The call to the function generateStartTerms generates all of the "better" start terms as I was describing. This function is imported from rightTerm.py.

rightTerms.py is where you'll find most of the work I was describing. I recommend start looking at [generateStartTerms](https://github.com/stroudgr/par-join-search/blob/8b2c4f408d135445c975a5ebb6fc0ec1ce50dfd9/rightTerm.py#L120), and the helper functions it calls. I tried to comment it so that it is clear.

I made some changes to search.py as well, but they're not as significant. If you're interested, you can check it search.py where I added some comments.
