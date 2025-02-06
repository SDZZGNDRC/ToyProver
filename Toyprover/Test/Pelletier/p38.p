% Problem 38

fof(p38_0, conjecture, 
    (
        ! [X] : 
            ( ( p(a) & ( p(X) => ? [Y] : ( p(Y) & r(X,Y) ) ) )
            => ? [Z,W] : ( p(Z) & r(X,W) & r(W,Z) ) )
    )
    <=>
    (
        ! [X] : 
            ( ( ~p(a) | p(X) | ? [Z,W] : ( p(Z) & r(X,W) & r(W,Z) ) )
            & ( ~p(a) | ~? [Y] : ( p(Y) & r(X,Y) ) | ? [Z,W] : ( p(Z) & r(X,W) & r(W,Z) ) ) )
    )
).