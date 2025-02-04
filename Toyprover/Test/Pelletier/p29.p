% Problem 29

fof(p29_0, axiom, ? [X] : f(X) & ? [X] : g(X)).

fof(p29_1, conjecture, (! [X] : (f(X) => h(X)) &
                        ! [X] : (g(X) => j(X))) <=>
                        ! [X, Y] : (f(X) & g(Y) => h(X) & j(Y))).



