% Problem 10
fof(p10_0, axiom, q => r).
fof(p10_1, axiom, r => (p & q)).
fof(p10_2, axiom, p => (q | r)).
fof(p10, conjecture,
    p <=> q).

