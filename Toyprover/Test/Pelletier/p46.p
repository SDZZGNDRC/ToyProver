% Problem 46

fof(p46_0, axiom, ! [X] : (f(X) & ! [Y] : (f(Y) & h(Y,X) => 
                    g(Y)) => g(X))).
fof(p46_0, axiom, ? [X] : (f(X) & ~g(X)) => 
                    ? [X] : (f(X) & ~g(X) & ! [Y] : (f(Y) & 
                    ~g(Y) => j(X,Y)))).
fof(p46_0, axiom, ! [X,Y] : (f(X) & f(Y) & h(X,Y) => 
                    ~j(X,Y))).

fof(p46_0, conjecture, ! [X] : (f(X) => g(X))).


