import Lean
import Batteries

import Toyprover.FOL.Basic

open Lean Elab Meta Term PrettyPrinter Delaborator

namespace FOLFormula

/-
This function return `true` when there exists a cycle in env like:
`x -> y -> z -> x` or `x -> x`
where `x`, `y`, `z` are variables. This case mean that there is a trivail cycle.

This function throw an error when there is a non trivail cycle like:
`x -> f(y,z); y -> x`
where `x`, `y`, `z` are variables and `f` is a function.

The function only returns `false` when there is no cycle.
-/
partial def istriv (env : INST) (x : String) (t : FOLTerm) : Except String Bool := do
  match t with
  | .Var y =>
    -- y == x || if let some _ := env y then ← istriv env x t else false  -- a simpler version
    if y == x then return true
    -- (y |-> t)
    else if let some t := env.apply y then
      istriv env x t
    else
      return false
  | .Fn _ args =>
    if ← args.anyM (istriv env x ·) then throw "cyclic" else return false


/-
The final env we get is like
{(x1 |-> t1), (x2 |-> t2), ..., (xn |-> tn)}
where x1, x2, ..., xn are all **distinct** variables.
And there is no **cyclic** dependency.
-/
partial def unify (env : INST) (eqs : List (FOLTerm × FOLTerm)) : Except String INST := do
  match eqs with
  | [] => return env
  | (.Fn f fargs, .Fn g gargs)::oth =>
    if f == g && fargs.length == gargs.length
    then unify env (fargs.zip gargs ++ oth)
    else throw "impossible unification"
  | (.Var x, t)::oth =>
    /-
    {(x |-> t),(x |-> s)} ∪ E
    {(s,t),(x |-> s)} ∪ E
    These two set have the same unifiers.
    -/
    if let some t' := env.apply x then unify env ((t', t)::oth)
    else
      let new_env :=
        if ← istriv env x t then env else
          (x, t)::env  -- (x |-> t) env
      unify new_env oth
  | (t, .Var x)::oth => unify env ((.Var x, t)::oth)

/-
The final unification algorithm: given a list of pairs of terms,
return the **Most General Unifier**.
-/
partial def fullunify (eqs : List (FOLTerm × FOLTerm)) := do
  return solve <| ← unify [] eqs
where
  solve (env : INST) : INST :=
    let new_env := env.comp env
    if new_env == env then env else solve new_env

partial def unify_and_apply (eqs : List (FOLTerm × FOLTerm)) := do
  let mgu ← fullunify eqs
  return eqs.map λ ((t1, t2) : FOLTerm × FOLTerm) => (t1.subst mgu, t2.subst mgu)

end FOLFormula
