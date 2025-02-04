% Problem 36

fof(p36_0, axiom, ! [X] : ? [Y] : f(X,Y)).
fof(p36_1, axiom, ! [X] : ? [Y] : g(X,Y)).
fof(p36_2, axiom, ! [X,Y] : (f(X,Y) | g(X,Y) => ! [Z] : (f(Y,Z) | g(Y,Z) => h(X,Z)))).

fof(p36_3, conjecture, ! [X] : ? [Y] : h(X,Y)).



