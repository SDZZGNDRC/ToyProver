import Toyprover.TPTPParser.PrattParser
import Toyprover.FOL.Basic

open FOLFormula TPTP.Parser

partial def term2fol (term : Term) : Except String Formula := do
  match term with
  | ⟨.ident "$true", []⟩ => return .True
  | ⟨.ident "$false", []⟩ => return .False
  | ⟨.ident n, as⟩ =>
    if (n.get! 0).isLower then -- predicate symbol starts with lowercase letter
      return .R n <| ← as.mapM λ t => toFOLTerm t
    else throw s!"Invalid predicate symbol: {n}"
  | ⟨.op "!", body :: var :: tail⟩ =>
    let ⟨.ident v, []⟩ := var
      | throw s!"invalid bound var: {var}"
    return .Forall v <| ← term2fol ⟨.op "!", body :: tail⟩
  | ⟨.op "?", body :: var :: tail⟩ =>
    let ⟨.ident v, []⟩ := var
      | throw s!"invalid bound var: {var}"
    return .Exists v <| ← term2fol ⟨.op "?", body :: tail⟩
  | ⟨.op "!", body :: []⟩ | ⟨.op "?", body :: []⟩ => term2fol body
  | ⟨.op "~", [a]⟩ => return .Not <| ← term2fol a
  | ⟨.op "|", [a,b]⟩ => return .Or (← term2fol a) (← term2fol b)
  | ⟨.op "&", [a,b]⟩ => return .And (← term2fol a) (← term2fol b)
  | ⟨.op "<=>", [a,b]⟩ => return .Iff (← term2fol a) (← term2fol b)
  | ⟨.op "=>", [a,b]⟩ => return .Imp (← term2fol a) (← term2fol b)
  | _ => throw s!"Unexpected term {term}"
where
  toFOLTerm (term : Term) : Except String FOLTerm := do
    match term with
    | ⟨.ident n, as⟩ =>
      if (n.get! 0).isLower then  -- function symbol starts with lowercase letter
        return .Fn n <| ← as.mapM λ t => toFOLTerm t
      else if as.length == 0 then -- variable symbol starts with uppercase letter and no arguments
        return .Var n
      else
        throw s!"Unexpected term {term}"
    | _ => throw s!"Unexpected term {term}"

/-
Convert a TPTP command to a FOL formula.
-/
partial def tptp2fol (cmd : Command) : Except String Formula :=
  if cmd.cmd != "fof" then
    throw s!"Unexpected command {cmd.cmd}"
  else
  match cmd.args with
  | [_, _, val] => term2fol val
  | _ => throw s!"Unexpected args {cmd.args}"

namespace ToyProver

/-
Find out all constant and function symbols.
-/
partial def herbfuns (fm : Formula) : List (String × Nat) × List (String × Nat) :=
  let (cns, fns) := fm.funcs.partition (fun (_, ar) => ar == 0)
  let cns' := if cns.length == 0 then [("c", 0)] else cns
  (cns', fns)


mutual
partial def groundterms (cntms : List FOLTerm) (funcs : List (String × Nat)) (n : Nat) : List FOLTerm :=
  if n == 0 then cntms else
  let k : String × Nat → List FOLTerm := fun (f,m) => (groundtuples cntms funcs (n-1) m).map (fun args => .Fn f args)
  funcs.flatMap k

partial def groundtuples (cntms : List FOLTerm) (funcs : List (String × Nat)) (n m : Nat) : List (List FOLTerm) :=
  if m == 0 then if n == 0 then [[]] else [] else
  let k : Nat → List (List FOLTerm) :=
    fun k => List.map (fun (h,t) => h::t) <|
      List.product (groundterms cntms funcs k) (groundtuples cntms funcs (n-k) (m-1))
  (List.range (n+1)).flatMap k
end

abbrev DNFT := List (List Formula)
abbrev CNFT := List (List Formula)
abbrev MFNT := DNFT → (Formula → Formula) → DNFT → DNFT

/-
Options(Config) for solver?
Diagnostics for solver?
Logs for solver?
Report for solver?
  execution time
  status: timeout, success, unsat, sat, unknown
-/

structure Config where
  timeout : Nat := 1000 -- timeout in ms
  verbose : Bool := false
  debug : Bool := false

structure Context where
  config : Config
  startTime : Nat

def defaultConfig : Config := {}

abbrev SolverM := ReaderT Context IO

def SolverM.run (solver : SolverM α) (cfg : Config := defaultConfig) : IO α := do
  let startTime ← IO.monoMsNow
  let ctx := { config := cfg, startTime }
  solver ctx

def guardTimeout : SolverM Unit := do
  if ((← IO.monoMsNow) - (← read).startTime) > ((← read).config.timeout) then
    throw $ IO.userError "timeout"
  else
    return

partial def herbloop (mfn : MFNT) (tfn : DNFT → Bool) (fl0 : DNFT) (cntms : List FOLTerm) (funcs : List (String × Nat)) (fvs : List String) (n : Nat) (fl : DNFT) (tried : List (List FOLTerm)) (tuples : List (List FOLTerm)) : SolverM (List (List FOLTerm)) := do
  guardTimeout
  match tuples with
  | [] =>
    let newtuples := groundtuples cntms funcs n fvs.length
    -- if n >= 100 then panic! "herbloop: level too high" else
    herbloop mfn tfn fl0 cntms funcs fvs (n + 1) fl tried newtuples
  | tup :: tups =>
  -- NOTICE: bottle neck
    let fl' := mfn fl0 (λ fm => fm.subst (fvs.zip tup)) fl
    if !(tfn fl') then return tup::tried else
    herbloop mfn tfn fl0 cntms funcs fvs n fl' (tup::tried) tups

partial def gilmore_loop :=
  let mfn (djs0 : DNFT) (ifn : Formula → Formula) (djs : DNFT) : DNFT :=
    List.filter (λ lits => ! trivial lits) <| distrib (List.map (List.map ifn) djs0) djs
  herbloop mfn (λ djs => djs != [])
where
  trivial (lits : List Formula) : Bool :=
    let (pos, neg) := List.partition Formula.positive lits
    pos.inter (List.map (Formula.negate) neg) != []
  distrib (d1 d2 : DNFT) : DNFT :=
    -- List.foldr (fun x IH => if ∀ y ∈ IH, x != y then x :: IH else IH) [] <| -- Here do not influence the correctness, but it is faster.
      (d1.product d2).map fun pq => pq.1 ++ pq.2

partial def gilmore (fm : Formula) : SolverM Nat := do
  let sfm := skolemize <| .Not (Formula.generalize fm)
  let fvs := sfm.fvs
  let (consts, funcs) := herbfuns sfm
  let cntms : List FOLTerm := List.map (λ ((c, _) : String × Nat) => FOLTerm.Fn c []) consts
  return List.length <| (← gilmore_loop (simpdnf sfm) cntms funcs fvs 0 [[]] [] [])


def solve (path : String) : SolverM String := do
  let cmds ← TPTP.compileFile path
  -- ensure there exists some conjectures
  let conjectures := cmds.filter (·.isConjecture)
  if conjectures.isEmpty then
    throw $ IO.userError s!"Expected conjectures, got none"
  else
  let conjectures ← conjectures.mapM λ cmd => IO.ofExcept <| tptp2fol cmd
  let axioms ← (cmds.filter (·.isAxiom)).mapM λ cmd => IO.ofExcept <| tptp2fol cmd
  let input := makeImp axioms conjectures
  -- IO.println s!"input: {repr input}"

  -- start solver
  try
    let res := (← gilmore input)
    return s!"success: {res}"
  catch e =>
    return e.toString
where
  makeImp (axioms conjectures : List Formula) : Formula :=
    let target := match conjectures with
      | [] => Formula.True
      | h::tail => tail.foldl Formula.And h
    match axioms with
    | [] => target
    | h :: tail =>
      let a := tail.foldl Formula.And h
      Formula.Imp a target


def solver (path : String) : IO Unit := do
  let res ← (solve path).run
  IO.println res

end ToyProver
