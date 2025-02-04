% Problem 45

fof(p45_0, axiom, ! [X] : (f(X) & ! [Y] : (g(Y) & h(X,Y) => 
                    j(X,Y)) => ! [Y] : (g(Y) & h(X,Y) => k(Y)))).
fof(p45_0, axiom, ~ ? [Y] : l(Y) & k(Y)).
fof(p45_0, axiom, ? [X] : (f(X) & ! [Y] : (h(X,Y) => l(Y)) & 
                    ! [Y] : (g(Y) & h(X,Y) => j(X,Y)))).

fof(p45_0, conjecture, ? [X] : (f(X) & ~ ? [Y] : (g(Y) & h(X,Y)))).

