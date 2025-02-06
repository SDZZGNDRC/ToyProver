import Toyprover.FOL.Unify

open FOLFormula

/--
info: Except.ok [(f(f(z),g(y)), f(f(z),g(y)))]
-/
#guard_msgs in
#eval unify_and_apply [
  ([FOLTerm| f(x,g(y))], [FOLTerm| f(f(z),w)])
]
/--
info: Except.ok [(f(y,y), f(y,y))]
-/
#guard_msgs in
#eval unify_and_apply [
  ([FOLTerm| f(x,y)], [FOLTerm| f(y,x)])
]
/--
info: Except.error "cyclic"
-/
#guard_msgs in
#eval unify_and_apply [
  ([FOLTerm| f(x,g(y))], [FOLTerm| f(y,x)])
]
/--
info: Except.ok [(f(f(f(x3,x3),f(x3,x3)),f(f(x3,x3),f(x3,x3))), f(f(f(x3,x3),f(x3,x3)),f(f(x3,x3),f(x3,x3)))), (f(f(x3,x3),f(x3,x3)), f(f(x3,x3),f(x3,x3))), (f(x3,x3), f(x3,x3))]
-/
#guard_msgs (whitespace := lax) in
#eval unify_and_apply [
  ([FOLTerm| x0], [FOLTerm| f(x1,x1)]),
  ([FOLTerm| x1], [FOLTerm| f(x2,x2)]),
  ([FOLTerm| x2], [FOLTerm| f(x3,x3)]),
]
