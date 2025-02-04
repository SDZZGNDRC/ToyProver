% Problem 24

fof(p24_0, axiom, ~ ? [X] : (s(X) & q(X))).
fof(p24_1, axiom, ! [X] : (p(X) => (q(X) | r(X)))).
fof(p24_2, axiom, ~ ? [X] : (p(X)) => ? [X] : q(X)).
fof(p24_3, axiom, ! [X] : (q(X) | r(X) => s(X))).

fof(p24_4, conjecture, ? [X] : (p(X) & r(X))).



