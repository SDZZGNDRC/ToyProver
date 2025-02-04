% Problem 37

fof(p37_0, axiom, ! [Z] : ? [W] : ! [X] : ? [Y] : ((p(X,Z) => p(Y,W)) & 
                    p(Y,Z) & (p(Y,W) => ? [U] : q(U,W)))).
fof(p37_1, axiom, ! [X,Z] : (~p(X,Z) => ? [Y] : q(Y,Z))).
fof(p37_2, axiom, ? [X,Y] : q(X,Y) => ! [X] : r(X,X)).

fof(p37_3, conjecture, ! [X] : ? [Y] : r(X,Y)).






