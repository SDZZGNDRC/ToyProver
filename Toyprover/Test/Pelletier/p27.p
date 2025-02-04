% Problem 27

fof(p27_0, axiom, ? [X] : (f(X) & ~ g(X))).
fof(p27_1, axiom, ! [X] : (f(X) => h(X))).
fof(p27_2, axiom, ! [X] : (j(X) & i(X) => f(X))).
fof(p27_3, axiom, ? [X] : (h(X) & ~ g(X)) => ! [X] : (i(X) => ~h(X))).

fof(p27_4, conjecture, ! [X] : (j(X) => ~i(X))).




