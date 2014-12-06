pumpkin
=======

A patchwork functional programming language

Git Flow
======
1) Make sure you are using `git pull --rebase` to pull changes, fixing merge
conflicts before you push. To set this up automatically, do ```git config
branch.autosetuprebase always```

2) No branch/pull requests, since we are doing rebase on master, master should
always be up to date and free of merge conflits

Tasks
======

1. X Numerical expression/Unit []
2. X Scope/Line Breaks []
3. X Booleans []
4. X Strings/Char []
5. X Lists/Tupals []
6. Algebraic Data Types []
7. X Type Checking/Inference
8. X Simple Functions: declaration, calling, simple arguments []
9. Advanced Functions: composition, piping, first class functions, recursion []
10. Error Handeling []
11. Importation []
12. X If else
13. X Maps
14. Composition plus piping

Obs.
======
1. I turned off warnings because that fragile thing was annoying. Feel free to turn it back on
2. Eliminated one parameter function calling with this syntax: even 2
3. Haven't implemented function declaration as follows: def x : Int => 1 + 1
Implemented only as follows:
def x : Int =>
	1 + 1
4. Gabi will not write string interpolation, if you feel strongly about it, do it yourself
