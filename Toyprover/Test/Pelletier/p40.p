% Problem 40
fof(p40, conjecture,
    ((? [Y]: ! [X]: (f(X,Y) <=> f(X,X))) => 
     ~(! [X]: ? [Y]: ! [Z]: (f(X,Y) <=> ~f(Z,X))))).

