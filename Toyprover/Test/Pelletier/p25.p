% Problem 24

fof(p24_0, axiom, ? [X] : p(X)).
fof(p24_1, axiom, ! [X] : (f(X) => (~ g(X) & r(X)))).
fof(p24_2, axiom, ! [X] : (p(X) => (g(X) & f(X)))).
fof(p24_3, axiom, ! [X] : (p(X) => q(X)) | ? [X] : (p(X) & r(X))).

fof(p24_4, conjecture, ? [X] : (q(X) & p(X))).


