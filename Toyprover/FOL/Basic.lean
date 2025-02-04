import Lean
import Batteries

open Lean Elab Meta Term

namespace FOLFormula

universe u

inductive FOLTerm where
  | Var : String → FOLTerm
  | Fn : String → List FOLTerm → FOLTerm
  deriving BEq

partial def FOLTerm.repr (t : FOLTerm) : Std.Format :=
  match t with
  | .Var v => v
  | .Fn f args => f ++ "(" ++ (Std.Format.joinSep (args.map FOLTerm.repr) ",") ++ ")"

instance : Repr FOLTerm where
  reprPrec := fun t _ => FOLTerm.repr t

inductive Formula where
  | True
  | False
  | R : String → List FOLTerm → Formula
  | Not : Formula → Formula
  | And : Formula → Formula → Formula
  | Or  : Formula → Formula → Formula
  | Imp : Formula → Formula → Formula
  | Iff : Formula → Formula → Formula
  | Forall : String → Formula → Formula
  | Exists : String → Formula → Formula
  deriving Inhabited, BEq, Repr

def Formula.repr (fm : Formula) (n : Nat) : Std.Format :=
  match fm with
  | .True => "⊤"
  | .False => "⊥"
  | .R r ts => r ++ "(" ++ (Std.Format.joinSep (ts.map FOLTerm.repr) ",") ++ ")"
  | .Not p => Std.Format.text s!"~{Formula.repr p max_prec}"
  | .And p q =>
    let t := Std.Format.text s!"{Formula.repr p 50} ∧ {Formula.repr q 50}"
    if n > 50 then Format.paren t else t
  | .Or p q =>
    let t := Std.Format.text s!"{Formula.repr p 40} ∨ {Formula.repr q 40}"
    if n > 40 then Format.paren t else t
  | .Imp p q =>
    let t := Std.Format.text s!"{Formula.repr p n} → {Formula.repr q n}"
    if n > 30 then Format.paren t else t
  | .Iff p q =>
    let t := Std.Format.text s!"{Formula.repr p 20} ↔ {Formula.repr q 20}"
    if n > 20 then Format.paren t else t
  | .Forall v p =>
    let t := Std.Format.text s!"∀ {v}, {Formula.repr p 0}"
    if n > 0 then Format.paren t else t
  | .Exists v p =>
    let t := Std.Format.text s!"∃ {v}, {Formula.repr p 0}"
    if n > 0 then Format.paren t else t

instance : Repr Formula where
  reprPrec := Formula.repr

declare_syntax_cat FOLTerm
declare_syntax_cat fol

syntax ident : FOLTerm
syntax ident "(" FOLTerm,* ")" : FOLTerm

syntax (name := formula_false) "⊥" : fol
syntax (name := formula_true) "⊤" : fol
syntax:max "(" fol ")" : fol
syntax:max ident "(" FOLTerm,* ")" : fol
syntax:max (name := formula_not) "~" fol:max : fol
syntax:50 (name := formula_and) fol:50 " and " fol:51 : fol
syntax:40 (name := formula_or) fol:40 " or " fol:40 : fol
syntax:30 (name := formula_imp) fol:31 " →' " fol:30 : fol
syntax:20 (name := formula_iff) fol:21 " ↔' " fol:20 : fol
syntax:max (name := formula_forall) "A." (ppSpace colGt ident ",") fol:11 : fol
syntax:max (name := formula_exists) "E." (ppSpace colGt ident ",") fol:11 : fol


syntax (name := FOLTerm_term) "[FOLTerm|" FOLTerm "]" : term
syntax (name := fol_term) "[fol|" fol "]" : term

partial def elabFOLTerm : Syntax → MetaM Expr
  | `(FOLTerm| $V:ident) =>
    let V' : Expr := Lean.mkStrLit V.getId.toString
    mkAppM ``FOLTerm.Var #[V']
  | `(FOLTerm| $Fn:ident ($args:FOLTerm,*)) => do
    let Fn' : Expr := Lean.mkStrLit Fn.getId.toString
    let args' ← args.getElems.mapM elabFOLTerm
    let argsList ← mkListLit (.const ``FOLTerm []) args'.toList
    mkAppM ``FOLTerm.Fn #[Fn', argsList]
  | _ => throwUnsupportedSyntax

partial def elabFol : Syntax → MetaM Expr
  | `(fol| ⊥) => mkAppM ``Formula.False #[]
  | `(fol| ⊤) => mkAppM ``Formula.True #[]
  | `(fol| ($f:fol)) => elabFol f
  | `(fol| $R:ident ($ts:FOLTerm,*)) => do
    let R' : Expr := Lean.mkStrLit R.getId.toString
    let ts' ← ts.getElems.mapM elabFOLTerm
    let tsList ← mkListLit (.const ``FOLTerm []) ts'.toList
    mkAppM ``Formula.R #[R', tsList]
  | `(fol| ~ $f:fol) => do
    let f' ← elabFol f
    mkAppM ``Formula.Not #[f']
  | `(fol| $f:fol and $g:fol) => do
    let (f', g') := (← elabFol f, ← elabFol g)
    mkAppM ``Formula.And #[f', g']
  | `(fol| $f:fol or $g:fol) => do
    let (f', g') := (← elabFol f, ← elabFol g)
    mkAppM ``Formula.Or #[f', g']
  | `(fol| $f:fol →' $g:fol) => do
    let (f', g') := (← elabFol f, ← elabFol g)
    mkAppM ``Formula.Imp #[f', g']
  | `(fol| $f:fol ↔' $g:fol) => do
    let (f', g') := (← elabFol f, ← elabFol g)
    mkAppM ``Formula.Iff #[f', g']
  | `(fol| A. $x:ident, $f:fol) => do
    let x : Expr := Lean.mkStrLit x.getId.toString
    let f' ← elabFol f
    mkAppM ``Formula.Forall #[x, f']
  | `(fol| E. $x:ident, $f:fol) => do
    let x : Expr := Lean.mkStrLit x.getId.toString
    let f' ← elabFol f
    mkAppM ``Formula.Exists #[x, f']
  | _ => throwUnsupportedSyntax

@[term_elab FOLTerm_term]
def elabFOLTerm_term : TermElab := fun stx expectedType? => do
  match stx with
  | `(term| [FOLTerm| $t:FOLTerm]) =>
    ensureHasType expectedType? (← elabFOLTerm t)
  | _ => throwUnsupportedSyntax

@[term_elab fol_term]
def elabFol_term : TermElab := fun stx expectedType? => do
  match stx with
  | `(term| [fol| $f:fol]) =>
    ensureHasType expectedType? (← elabFol f)
  | _ => throwUnsupportedSyntax

/-
Free variables of a term.
Notice that the free-variables and the variables
are exactly the same thing for `term`.
-/
partial def FOLTerm.fvs : FOLTerm → List String
  | .Var v => [v]
  | .Fn _ args => List.eraseDup <| args.foldl (fun acc t => acc ++ fvs t) []

/-
A term is said to be grounded if it does not contain any **variables**(etc. *free variables*).
-/
def FOLTerm.isGrounded (t : FOLTerm) : Bool :=
  t.fvs == []

/-
## Instantiation
-/

/-
Type of instantiation.
[(x |-> t), ...]
-/
abbrev INST := List (String × FOLTerm)

/-
TODO: Use `Array` to improve performance?
-/
def INST.apply (env : INST) (x : String) : Option FOLTerm :=
  match env with
  | [] => none
  | (y, t) :: env' =>
    if x == y then
      some t
    else
      INST.apply env' x

/-
TODO: Convert to **Tail recursion**?
-/
def INST.toFunc (env : INST) : String → Option FOLTerm :=
  match env with
  | [] => λ _ => none
  | (y, t) :: env' =>
    λ x => if x == y then
      some t
    else
      INST.toFunc env' x



/-
Substitution for FOLTerm
-/
partial def FOLTerm.subst (t : FOLTerm) (sfn : INST) : FOLTerm :=
  match t with
  | .Var v => (sfn.apply v).getD t
  | .Fn fn ts => .Fn fn (ts.map (·.subst sfn))


def INST.comp (env1 env2 : INST) : INST :=
  env1.map (λ ((x, t) : String × FOLTerm) => (x, t.subst env2))

/-
Some constructors for Formula
-/
def mk_forall : String → Formula → Formula := fun v p => .Forall v p

def mk_exists : String → Formula → Formula := fun v p => .Exists v p

def mk_and : Formula → Formula → Formula := fun p q => .And p q

def mk_or : Formula → Formula → Formula := fun p q => .Or p q

/-
A *formula* is said to *be grounded* when it contains no variables, i.e var p = ∅.
-/
def Formula.vars (fm : Formula) : List String :=
  match fm with
  | .True | .False => []
  | .R _ ts => List.eraseDup <| ts.foldl (fun acc t => acc ++ FOLTerm.fvs t) []
  | .Not p => p.vars
  | .And p q | .Or p q | .Imp p q | .Iff p q => List.eraseDup <| p.vars ++ q.vars
  | .Forall v p | .Exists v p => List.eraseDup <| [v] ++ p.vars

def Formula.isGrounded (fm : Formula) : Bool :=
  fm.vars == []


partial def Formula.overatom (fm : Formula) (f : String → List FOLTerm → α → α) (a : α) : α :=
  match fm with
  | .True | .False => a
  | .R p ts => f p ts a
  | .Not p => p.overatom f a
  | .And p q | .Or p q | .Imp p q | .Iff p q => p.overatom f (q.overatom f a)
  | .Forall _ p | .Exists _ p => p.overatom f a

/-
Substitution for a fol-formula
-/
partial def Formula.subst (fm : Formula) (sfn : INST) : Formula :=
  match fm with
  | .True | .False => fm
  | .R p ts => .R p (ts.map (·.subst sfn))
  | .Not p => .Not (p.subst sfn)
  | .And p q => .And (p.subst sfn) (q.subst sfn)
  | .Or p q => .Or (p.subst sfn) (q.subst sfn)
  | .Imp p q => .Imp (p.subst sfn) (q.subst sfn)
  | .Iff p q => .Iff (p.subst sfn) (q.subst sfn)
  -- NOTICE: FIXME: 这里需要考虑 变量重名问题, 比如变量被捕获.
  | .Forall v p => .Forall v (p.subst sfn)
  -- NOTICE: FIXME: 这里需要考虑 变量重名问题, 比如变量被捕获.
  | .Exists v p => .Exists v (p.subst sfn)

/-
Constructor for a `sfn` used in `Formula.subst`.
-/
def mk_sfn (x : String) (inst : FOLTerm) : String → Option FOLTerm :=
  fun y => if x == y then some inst else none

/-
Check if a literal is negative or not.
-/
def Formula.negative (fm : Formula) : Bool :=
  match fm with
  | .Not _ => true
  | _ => false

def Formula.positive := λ (fm : Formula) => !fm.negative

def Formula.negate (fm : Formula) : Formula :=
  match fm with
  | .Not p => p
  | _ => .Not fm

/-
Free variables of a fol-formula
-/
def Formula.fvs (fm : Formula) : List String :=
  match fm with
  | .True | .False => []
  | .R _ ts => List.eraseDup <| ts.foldl (fun acc t => acc ++ FOLTerm.fvs t) []
  | .Not p => p.fvs
  | .And p q | .Or p q | .Imp p q | .Iff p q => List.eraseDup <| p.fvs ++ q.fvs
  | .Forall v p | .Exists v p => List.erase (List.eraseDup <| p.fvs) v

def Formula.isSentence (fm : Formula) : Bool :=
  fm.fvs == []

/--
info: true
-/
#guard_msgs in
#eval [fol| A. x, E. y, P(x,y)].isSentence

partial def FOLTerm.funcs (tm : FOLTerm) : List (String × Nat) :=
  List.eraseDup <| go tm
  where
  go (term : FOLTerm) : List (String × Nat) :=
    match term with
    | .Var _ => []
    | .Fn f args => args.foldr (fun t acc => (go t) ++ acc) [(f,args.length)]

partial def Formula.funcs (fm : Formula) : List (String × Nat) :=
  List.eraseDup <| fm.overatom (fun _ tms acc => tms.foldr (fun t acc' => t.funcs ++ acc') acc) []

/-
Use universial quantifier to bound free variables.
-/
partial def Formula.generalize (fm : Formula) : Formula :=
  (fm.fvs).foldr (fun x oldFm => mk_forall x oldFm) fm

/-
Remove all **prefix** universal quantifiers.
-/
partial def Formula.specialize (fm : Formula) : Formula :=
  match fm with
  | .Forall _ p => p.specialize
  | _ => fm


partial def psimplify1 (fm : Formula) : Formula :=
  match fm with
  | .Not .False => .True
  | .Not .True => .False
  | .Not (.Not p) => p
  | .And _ .False | .And .False _ => .False
  | .And p .True | .And .True p => p
  | .Or p .False | .Or .False p => p
  | .Or _ .True | .Or .True _ => .True
  | .Imp .False _ | .Imp _ .True => .True
  | .Imp .True p => p
  | .Imp p .False => .Not p
  | .Iff p .True | .Iff .True p => p
  | .Iff p .False | .Iff .False p => .Not p
  | _ => fm


/-
Simplification for propositional logic
-/
partial def psimplify (fm : Formula) : Formula :=
  match fm with
  | .Not p => psimplify1 (.Not (psimplify p))
  | .And p q => psimplify1 (.And (psimplify p) (psimplify q))
  | .Or p q => psimplify1 (.Or (psimplify p) (psimplify q))
  | .Imp p q => psimplify1 (.Imp (psimplify p) (psimplify q))
  | .Iff p q => psimplify1 (.Iff (psimplify p) (psimplify q))
  | _ => fm

/-
Simplification for first-order logic
-/
partial def simplify1 (fm : Formula) : Formula :=
  match fm with
  | .Forall x p | .Exists x p => if p.fvs.contains x then fm else p
  | _ => psimplify1 fm

partial def simplify (fm : Formula) : Formula :=
  match fm with
  | .Not p => simplify1 (.Not (simplify p))
  | .And p q => simplify1 (.And (simplify p) (simplify q))
  | .Or p q => simplify1 (.Or (simplify p) (simplify q))
  | .Imp p q => simplify1 (.Imp (simplify p) (simplify q))
  | .Iff p q => simplify1 (.Iff (simplify p) (simplify q))
  | .Forall x p => simplify1 (.Forall x (simplify p))
  | .Exists x p => simplify1 (.Exists x (simplify p))
  | _ => fm

partial def nnf (fm : Formula) : Formula :=
  match fm with
  | .And p q => .And (nnf p) (nnf q)
  | .Or p q => .Or (nnf p) (nnf q)
  | .Imp p q => .Or (nnf (.Not p)) (nnf q)
  | .Iff p q => .Or (.And (nnf p) (nnf q)) (.And (nnf (.Not p)) (nnf (.Not q)))
  | .Not (.Not p) => nnf p
  | .Not (.And p q) => .Or (nnf (.Not p)) (nnf (.Not q))
  | .Not (.Or p q) => .And (nnf (.Not p)) (nnf (.Not q))
  | .Not (.Imp p q) => .And (nnf p) (nnf (.Not q))
  | .Not (.Iff p q) => .Or (.And (nnf p) (nnf (.Not q))) (.And (nnf (.Not p)) (nnf q))
  | .Forall x p => .Forall x (nnf p)
  | .Exists x p => .Exists x (nnf p)
  | .Not (.Forall x p) => .Exists x (nnf (.Not p))
  | .Not (.Exists x p) => .Forall x (nnf (.Not p))
  | _ => fm

def purednf (fm : Formula) : List (List (Formula)) :=
  match fm with
  | .And p q => .foldr (fun x IH => if ∀ y ∈ IH, x != y then x :: IH else IH) [] <|
                  ((purednf p).product (purednf q)).map fun pq => pq.1 ++ pq.2
  | .Or p q => ((purednf p) ++ (purednf q))
  | _ => [[fm]]

def simpdnf (fm : Formula) : List (List (Formula)) :=
  if fm == .False then [] else if fm == .True then [[]] else
  let ls := filter (purednf fm)
  let ls := Array.toList <| (ls.toArray).qsort (·.length > ·.length)
  ls.foldr (λ l acc => if ∀ y ∈ acc, ¬ (∀ a ∈ y, l.contains a) then l :: acc else acc) []
  where
  partition (l : List (Formula)) : List (Formula) × List (Formula) :=
    match l with
    | [] => ([], [])
    | p :: t =>
      let (pos, neg) := partition t
      match p with
      | .Not p' => (pos, p' :: neg)
      | _ => (p :: pos, neg)
  filter (ls : List (List (Formula))) : List (List (Formula)) :=
    ls.filter λ l => let (pos, neg) := partition l; pos.inter neg == []

partial def variant (x : String) (vars : List String) : String :=
  if vars.contains x then
    variant (x ++ "'") vars
  else
    x

/-
Pull out all quantifiers
-/
partial def Formula.pullquants (fm : Formula) : Formula :=
  match fm with
  | .And (.Forall x p) (.Forall y q) =>
    pullq true true fm mk_forall mk_and x y p q
  | .Or (.Exists x p) (.Exists y q) =>
    pullq true true fm mk_exists mk_or x y p q
  | .And (.Forall x p) q =>
    pullq true false fm mk_forall mk_and x x p q
  | .And p (.Forall y q) =>
    pullq false true fm mk_forall mk_and y y p q
  | .Or (.Forall x p) q =>
    pullq true false fm mk_forall mk_or x x p q
  | .Or p (.Forall y q) =>
    pullq false true fm mk_forall mk_or y y p q
  | .And (.Exists x p) q =>
    pullq true false fm mk_exists mk_and x x p q
  | .And p (.Exists y q) =>
    pullq false true fm mk_exists mk_and y y p q
  | .Or (.Exists x p) q =>
    pullq true false fm mk_exists mk_or x x p q
  | .Or p (.Exists y q) =>
    pullq false true fm mk_exists mk_or y y p q
  | _ => fm
where
  pullq (l r : Bool ) (fm : Formula) (quant : String → Formula → Formula) (op : Formula → Formula → Formula) (x y : String) (p q : Formula) : Formula :=
    let z := variant x fm.fvs
    let p' := if l then p.subst [(x, .Var z)] else p
    let q' := if r then q.subst [(y, .Var z)] else q
    quant z ((op p' q').pullquants)

partial def pnf (fm : Formula) : Formula :=
  prenex <| nnf <| simplify fm
where
  prenex (fm' : Formula) : Formula :=
    match fm' with
    | .Forall x p => .Forall x (prenex p)
    | .Exists x p => .Exists x (prenex p)
    | .And p q => Formula.pullquants (.And (prenex p) (prenex q))
    | .Or p q => Formula.pullquants (.Or (prenex p) (prenex q))
    | _ => fm'

partial def skolem (fm : Formula) (fns : List String) : Formula × List String :=
  match fm with
  | .Exists y p =>
    let xs := fm.fvs
    let f := variant (if xs == [] then "c_"++y else "f_"++y) fns
    let fx := FOLTerm.Fn f (xs.map (.Var))
    skolem (p.subst [(y,fx)]) (f::fns)
  | .Forall x p =>
    let (p', fns') := skolem p fns
    (.Forall x p', fns')
  | .And p q =>
    skolem2 .And p q fns
  | .Or p q =>
    skolem2 .Or p q fns
  | _ => (fm, fns)
where
  skolem2 (mk : Formula → Formula → Formula) (p q : Formula) (fns : List String) :=
    let (p', fns') := skolem p fns
    let (q', fns'') := skolem q fns'
    (mk p' q', fns'')

/-
Simplify and nnf the formula, then skolemize it, remove all exists quantifiers.
-/
partial def askolemize (fm : Formula) :=
  (skolem (nnf (simplify fm)) (fm.funcs.map (fun (f, _) => f))).fst

/-
Skolemize
-/
partial def skolemize (fm : Formula) :=
  Formula.specialize <| pnf <| askolemize fm

/--
info: P(x) ∧ ~P(f_y(x))
-/
#guard_msgs in
#eval skolemize <| .Not [fol| E. x, A. y, P(x) →' P(y)]


end FOLFormula
