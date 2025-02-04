% Problem 44

fof(p44_0, axiom, ! [X] : (f(X) => ? [Y] : (g(Y) & h(X,Y)) &
                    ? [Y] : (g(Y) & ~h(X,Y)))).
fof(p44_1, axiom, ? [X] : (j(X) & ! [Y] : (g(Y) => h(X,Y)))).

fof(p44_2, conjecture, ? [X] : (j(X) & f(X))).



