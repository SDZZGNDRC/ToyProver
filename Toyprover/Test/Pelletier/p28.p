% Problem 28

fof(p28_0, axiom, (! [X] : p(X)) => ! [X] : q(X)).
fof(p28_1, axiom, ! [X] : (q(X) | r(X)) => ? [X] : (q(X) & s(X))).
fof(p28_2, axiom, (? [X] : s(X)) => ! [X] : (f(X) => g(X))).

fof(p28_3, conjecture, ! [X] : (p(X) & f(X) => g(X))).

