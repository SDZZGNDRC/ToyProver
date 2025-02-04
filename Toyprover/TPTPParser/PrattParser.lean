import Lean
import Std
import Batteries
axiom Iota : Type

namespace TPTP

namespace Tokenizer
open Lean Std

inductive Status where
  | default
  | ident
  | string
  | comment
  deriving Repr, BEq

inductive Token where
  | op (op : String)
  | ident (ident : String)
  deriving Repr, Inhabited, BEq

def Token.toString : Token → String
  | .op a => a
  | .ident a => a

structure State where
  status : Status := .default
  currToken : String := ""
  res : Array Token := #[]
  deriving Repr

def tokens := #[
  "|", "&", "<=>", "=>",
  "~", ",", "(", ")", "!", "?", "^", ":", "[", "]", "."
]

def tokenHashSet : Std.HashSet String := Std.HashSet.ofArray tokens

def tokenPrefixes : Std.HashSet String :=
  Std.HashSet.ofArray $ tokens.flatMap (fun t => Id.run do
    let mut res := #[]
    let mut pref := ""
    for c in t.data do
      pref := pref.push c
      res := res.insertIdx! 0 pref
    return res
  )

abbrev TokenizerM := StateT State (Except String)

def setStatus (status : Status) : TokenizerM Unit := do
  modify fun (s : State) => {s with status := status}

def getStatus : TokenizerM Status := do
  return (← get).status

def addToCurrToken (char : Char) : TokenizerM Unit := do
  modify fun (s : State) => {s with currToken := s.currToken.push char}

def getCurrToken : TokenizerM String := do
  return (← get).currToken

def addCurrToken : TokenizerM Unit := do
  modify fun (s : State) => {
    s with
    res := s.res.push $
      match s.status with
      | .default => .op s.currToken
      | .ident => .ident s.currToken
      | .string => .ident s.currToken
      | .comment => panic! s!"Cannot add comment as token"
    currToken := ""
  }

def finalizeToken : TokenizerM Unit := do
  if (← getStatus) == .string || (← getCurrToken) != "" then
    match ← getStatus with
    | .default =>
      if tokenHashSet.contains (← getCurrToken) then
        addCurrToken
      else
        let invalid_token ← getCurrToken
        throw s!"Invalid token: {invalid_token}(ascii: {invalid_token.toAsciiByteArray})"
    | .ident | .string => addCurrToken
    | .comment => throw s!"Cannot finalize comment"
    setStatus .default

def tokenizeAux (str : String) : TokenizerM Unit := do
  for char in str.data do
    match ← getStatus with
    | .default =>
      if char.isWhitespace then
        finalizeToken
      else if char.isAlpha || char == '$' then
        finalizeToken
        setStatus .ident
        addToCurrToken char
      else if char == '\'' then
        finalizeToken
        setStatus .string
      else if char == '%' then
        finalizeToken
        setStatus .comment
      else if tokenPrefixes.contains ((← getCurrToken).push char) then
        addToCurrToken char
      else if tokenPrefixes.contains (⟨[char]⟩) then
        finalizeToken
        addToCurrToken char
      else throw s!"Invalid token: {char.toString.toAsciiByteArray}"
    | .ident =>
      if char.isWhitespace then
        finalizeToken
      else if char.isAlphanum || char == '_' then
        addToCurrToken char
      else
        finalizeToken
        addToCurrToken char
        setStatus .default
    | .string =>
      if char == '\'' then
        finalizeToken
      else
        addToCurrToken char
    | .comment =>
      if char == '\n' then
        setStatus .default

  finalizeToken

def tokenize (s : String) : Except String (Array Token) := do
  return (← (tokenizeAux s).run {}).2.res

end Tokenizer

namespace Parser
open Tokenizer
/- Pratt parser following `https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html`-/

structure State where
  tokens : Array Token
  curr : Nat := 0
  deriving Repr

abbrev ParserM := StateT State (Except String)

def isEOF : ParserM Bool := do return (← get).curr == (← get).tokens.size

def peek : ParserM Token := do
  let i := (← get).curr
  let ts := (← get).tokens
  if i >= ts.size then throw "Unexpected end of file"
  return ts[i]!

def peek? : ParserM (Option Token) := do
  if ← isEOF then return none else return some (← peek)

def next : ParserM Token := do
  let c ← peek
  modify fun (s : State) => {s with curr := s.curr + 1}
  return c

def infixBindingPower? : String → Option (Nat × Nat)
  | "|" | "&" | "<=>" | "=>" => some (60, 61)
  | _ => none

def prefixBindingPower? : String → Option Nat
  | "~" => some 70
  | _ => none

def BinderBindingPower? : String → Option Nat
  | "!" | "?" => some 70
  | _ => none

inductive Term where
  | mk : Token → List Term → Term
  deriving Repr, Inhabited, BEq

def Term.func : Term → Token := fun ⟨n, _⟩ => n
def Term.args : Term → List Term := fun ⟨_, ts⟩ => ts

partial def Term.toString : Term → String := fun ⟨n, ts⟩ =>
  match ts with
  | [] => n.toString
  | _ => n.toString ++ "(" ++ String.join ((ts.map Term.toString).intersperse ",") ++ ")"

instance : ToString Term where
  toString := Term.toString

def parseToken (t : Token) : ParserM Unit := do
  let nextToken ← next
  if nextToken != t then throw s!"Expected {repr t}, got {repr nextToken}"

def parseIdent : ParserM String := do
  let nextToken ← next
  let .ident id := nextToken
    | throw s!"Expected identifier, got '{repr nextToken}'"
  return id

partial def parseSep (seq : Token) (p : ParserM α) : ParserM (List α) := do
  let t ← p
  if (← peek?) == some seq then
    parseToken seq
    let l ← parseSep seq p
    return t::l
  else
    return [t]

mutual
partial def parseTerm (minbp : Nat := 0) : ParserM Term := do
  let lhs ← parseLhs
  let res ← addOpAndRhs lhs minbp
  return res

partial def parseLhs : ParserM Term := do
  let nextToken ← next
  if let .ident _ := nextToken then
    if (← peek?) == some (.op "(") then
      parseToken (.op "(")
      let args ← parseSep (.op ",") (parseTerm 0)
      parseToken (.op ")")
      return Term.mk nextToken args
    else
    return Term.mk nextToken []
  else if nextToken == .op "(" then
    let lhs ← parseTerm 0
    parseToken (.op ")")
    return lhs
  else if nextToken == .op "[" then
    let args ← parseSep (.op ",") (parseTerm 0)
    parseToken (.op "]")
    return Term.mk nextToken args
  else if let some rbp := BinderBindingPower? nextToken.toString then
    parseToken (.op "[")
    let vars ← parseSep (.op ",") parseTypeDecl
    parseToken (.op "]")
    parseToken (.op ":")
    let rhs ← parseTerm rbp
    return Term.mk nextToken (rhs :: vars)
  else if let some rbp := prefixBindingPower? nextToken.toString then
    let rhs ← parseTerm rbp
    return Term.mk nextToken [rhs]
  else
    throw s!"Expected term, got '{repr nextToken}'"

partial def addOpAndRhs (lhs : Term) (minbp : Nat) : ParserM Term := do
  if ← isEOF then
    return lhs
  else
    let op ← peek
    let some (lbp, rbp) := infixBindingPower? op.toString
      | return lhs
    if lbp < minbp then
      return lhs
    else
      let op ← next
      let rhs ← parseTerm rbp
      return ← addOpAndRhs (Term.mk op [lhs, rhs]) minbp

partial def parseTypeDecl : ParserM Term := do
  if (← peek?) == some (.op "(") then
    parseToken (.op "(")
    let t ← parseIdent
    if (← peek?) == some (.op ":") then
      parseToken (.op ":")
      let ty ← parseTerm
      parseToken (.op ")")
      return Term.mk (.ident t) [ty]
    else
      parseToken (.op ")")
      return Term.mk (.ident t) []
  else
    let ident ← parseIdent
    if (← peek?) == some (.op ":") then
      parseToken (.op ":")
      let ty ← parseTerm
      return Term.mk (.ident ident) [ty]
    else
      return Term.mk (.ident ident) []
end

structure Command where
  cmd : String
  args : List Term
  deriving Repr

def Command.isConjecture : Command → Bool
  | ⟨_, [_, ⟨.ident "conjecture",[]⟩, _]⟩ => true
  | _ => false

def Command.isAxiom : Command → Bool
  | ⟨_, [_, ⟨.ident "axiom",[]⟩, _]⟩ => true
  | _ => false

def parseCommand : ParserM Command := do
  let cmd ← parseIdent
  match cmd with
  | "cnf" | "fof" =>
    parseToken (.op "(")
    let name ← parseIdent
    parseToken (.op ",")
    let kind ← parseIdent
    parseToken (.op ",")
    let val ← match kind with
      | "type" => parseTypeDecl
      | _ => parseTerm
    if (← peek?) == .some (.op ",") then
      parseToken (.op ",")
      discard $ parseTerm
    parseToken (.op ")")
    parseToken (.op ".")
    return ⟨cmd, [Term.mk (.ident name) [], Term.mk (.ident kind) [], val]⟩
  | "include" =>
    parseToken (.op "(")
    let str ← parseIdent
    parseToken (.op ")")
    parseToken (.op ".")
    return ⟨cmd, [Term.mk (.ident str) []]⟩
  | _ => throw "Command '{cmd}' not supported"


partial def parseFile : ParserM (List Command) := do
  if ← isEOF then
    return []
  else
    let c ← parseCommand
    return c::(← parseFile)

def parse (s : String) : Except String (List Command) := do
  let tokens ← Tokenizer.tokenize s
  let res ← parseFile.run {tokens}
  return res.1

namespace Term

open Parser
open Lean
open Meta

partial def toLeanExpr (t : Parser.Term) : MetaM Expr := do
  match t with
  | ⟨.ident "$true", []⟩ => return mkConst `True
  | ⟨.ident "$false", []⟩ => return mkConst `False
  | ⟨.ident n, as⟩ => do
    let some decl := (← getLCtx).findFromUserName? n.toName
      | throwError "Unknown variable name {n}"
    return mkAppN (mkFVar decl.fvarId) (← as.mapM toLeanExpr).toArray
  | ⟨.op "!", body :: var :: tail⟩ =>
    withVar var fun v => do
      mkForallFVars #[v] (← toLeanExpr ⟨.op "!", body :: tail⟩)
  | ⟨.op "?", body :: var :: tail⟩ =>
    withVar var fun v => do
      mkAppM `Exists #[← mkLambdaFVars #[v] (← toLeanExpr ⟨.op "?", body :: tail⟩)]
  | ⟨.op "!", body :: []⟩ | ⟨.op "?", body :: []⟩ =>
    body.toLeanExpr
  | ⟨.op "~", [a]⟩ => mkAppM `Not #[← a.toLeanExpr]
  | ⟨.op "|", [a,b]⟩   => mkAppM `Or (← [a,b].mapM toLeanExpr).toArray
  | ⟨.op "&", [a,b]⟩   => mkAppM `And (← [a,b].mapM toLeanExpr).toArray
  | ⟨.op "<=>", [a,b]⟩ => mkAppM `Iff (← [a,b].mapM toLeanExpr).toArray
  | ⟨.op "=>", [a,b]⟩ => mkArrow (← a.toLeanExpr) (← b.toLeanExpr)
  | _ => throwError "Could not translate to Lean Expr: {repr t}"
where
  withVar {α : Type _} (var : Term) (k : Expr → MetaM α) : MetaM α := do
    let ⟨.ident v, ty⟩ := var
      | throwError s!"invalid bound var: {repr var}"
    let ty ← match ty with
      | [ty] => ty.toLeanExpr
      | [] => pure $ mkConst `Iota
      | _ => throwError "invalid bound var: {repr var}"
    withLocalDeclD v.toName ty k

end Term

end Parser

open Parser
open Lean
open Meta

partial def findFile (name : String) (dir : System.FilePath) : IO (Option System.FilePath) := do
  -- search in [dir], and its parents recursively
  if (name : System.FilePath).isRelative then
    match ← search dir with
    | .none =>
      match ← IO.getEnv "TPTP" with
      | .none => return .none
      | .some dir' => search dir'
    | .some res => return res
  else if ← System.FilePath.pathExists name then
    return .some name
  else
    return .none
where
  search (dir : System.FilePath) : IO (Option System.FilePath) := do
    let curName := dir / name
    if ← System.FilePath.pathExists curName then
      return .some curName
    else
      let some dir' := dir.parent
        | return .none
      return ← search dir'

partial def resolveIncludes (cmds : List Parser.Command) (dir : System.FilePath) : IO (List Parser.Command) := do
  let mut res : Array Parser.Command := #[]
  for cmd in cmds do
    match cmd with
    | ⟨"include", [⟨.ident name, []⟩]⟩ =>
      let some path ← findFile (name : String) (dir : System.FilePath)
        | throw $ IO.userError s!"Cannot find: {name}"
      IO.println s!"Reading included file: {path}"
      let s ← IO.FS.readFile path
      let cmds' ← IO.ofExcept <| Parser.parse s
      let cmds' ← resolveIncludes cmds' path
      for cmd' in cmds' do
        res := res.push cmd'
    | _ => res := res.push cmd
  return res.toList

/-- First argument is the Prop itself, second argument is the proof of the Prop, third argument is an array of
    paramNames, and the final argument is a bool which indicates if of kind "conjecture" (i.e. whether the facts
    come from the goal) -/
abbrev Formulas := Array (Expr × Expr × Array Name × Bool)

def compileCmds (cmds : List Parser.Command) (acc : Formulas) (k : Formulas → MetaM α) : MetaM α := do
  match cmds with
  | ⟨cmd, args⟩ :: cs =>
    match cmd with
    | "cnf" | "fof" =>
      match args with
      | [⟨.ident name, []⟩, ⟨.ident kind, _⟩, val] => do
        let val ← val.toLeanExpr
        let notVal ← mkAppM `Not #[val]
        let val := if kind == "conjecture" then notVal else val
        let isFromGoal := kind == "conjecture"
        withLocalDeclD ("H_".toName ++ name.toName) val fun x => do
          let acc := acc.push (val, ← mkAppM ``eq_true #[x], #[], isFromGoal)
          compileCmds cs acc k
      | _ => throwError "Unknown declaration kind: {args.map repr}"
    | "include" => throwError "includes should have been unfolded first: {args.map repr}"
    | cmd => throwError "Unknown command: {cmd}"
  | [] => k acc


def compileFile (path : String) : IO (List Parser.Command) := do
  let code := (← IO.FS.readFile path).replace "\r" ""
  -- IO.println s!"Reading file: {code}"
  let cmds ← IO.ofExcept <| Parser.parse code
  let cmds ← resolveIncludes cmds <| (path : System.FilePath).parent.get!
  return cmds


end TPTP
