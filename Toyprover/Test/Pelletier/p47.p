% Problem 47

fof(p47_0, axiom, ! [X] : (p1(X) => p0(X)) & ? [X] : p1(X)).
fof(p47_1, axiom, ! [X] : (p2(X) => p0(X)) & ? [X] : p2(X)).
fof(p47_2, axiom, ! [X] : (p3(X) => p0(X)) & ? [X] : p3(X)).
fof(p47_3, axiom, ! [X] : (p4(X) => p0(X)) & ? [X] : p4(X)).
fof(p47_4, axiom, ! [X] : (p5(X) => p0(X)) & ? [X] : p5(X)).

fof(p47_5, axiom, ? [X] : (q1(X)) & ! [X] : (q1(X) => q0(X))).
fof(p47_6, axiom, ! [X] : (p0(X) => (! [Y] : (q0(Y) => r(X,Y)) | 
                    ! [Y] : ((p0(Y) & s(Y,X) & ? [Z] : (q0(Z) & 
                    r(Y,Z)) => r(X,Y)))))).
fof(p47_7, axiom, ! [X,Y] : ((p3(Y) & (p5(X) | p4(X))) => 
                    s(X,Y))).
fof(p47_8, axiom, ! [X,Y] : ((p3(X) & p2(Y)) => s(X,Y))).
fof(p47_9, axiom, ! [X,Y] : ((p2(X) & p1(Y) => s(X,Y)))).
fof(p47_10, axiom, ! [X,Y] : ((p1(X) & (p2(Y) | q1(Y))) =>
                    ~r(X,Y))).
fof(p47_11, axiom, ! [X,Y] : ((p3(X) & p4(Y))=> r(X,Y))).
fof(p47_12, axiom, ! [X,Y] : ((p3(X) & p5(Y)) => ~r(X,Y))).
fof(p47_13, axiom, ! [X] : ((p4(X) | p5(X)) => ? [Y] : (q0(Y) & r(X,Y)))).
fof(p47_14, conjecture, ? [X,Y] : (p0(X) & p0(Y) & ? [Z] : (q1(Z) & r(Y,Z) & r(X,Y)))).
