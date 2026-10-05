module

public import Lean

@[expose] public section
open Lean

/-- Lossless names, including numeric components. -/
def nameJson : Name → Json
  | .anonymous => Json.arr #[]
  | .str p s => Json.arr #[nameJson p, toJson s]
  | .num p n => Json.arr #[nameJson p, toJson n]

partial def parseName (j : Json) : Except String Name := do
  let a ← j.getArr?
  if a.isEmpty then return .anonymous
  if a.size != 2 then throw "Invalid serialized name"
  let p ← parseName a[0]!
  match a[1]! with
  | .str s => return .str p s
  | _ => return .num p (← a[1]!.getNat?)

/-- Exactly the compiler-generated auxiliaries created by the three matchers. -/
def privateHelpers : List Name :=
  [`FiniteGraphFreeGroup.graphRealizationEndpointLabel.match_1.eq_1,
   `FiniteGraphFreeGroup.graphRealizationEndpointLabel.match_1.eq_2,
   `FiniteGraphFreeGroup.graphRealizationEndpointLabel.match_1.splitter,
   `FiniteGraphFreeGroup.graphVertexStarPre.match_1.eq_1,
   `FiniteGraphFreeGroup.graphVertexStarPre.match_1.eq_2,
   `FiniteGraphFreeGroup.graphVertexStarPre.match_1.splitter,
   `PresentationComplex.wordLoop.match_1.eq_1,
   `PresentationComplex.wordLoop.match_1.eq_2,
   `PresentationComplex.wordLoop.match_1.splitter]

/-- No name outside the explicit nine-element mapping is rewritten. -/
def normalizedName (privateModule n : Name) : Name :=
  let helper := privateToUserName n
  if privateHelpers.contains helper && n == mkPrivateNameCore privateModule helper then
    mkPrivateNameCore `CanonicalConstruction helper
  else n

def hasPrivateReference (e : Expr) : Bool :=
  (e.find? fun e => match e with
    | .const n _ => isPrivateName n
    | .proj n _ _ => isPrivateName n
    | _ => false).isSome

structure ExprTable where
  ids : Std.HashMap Expr Nat := {}
  nodes : Array Json := #[]

/-- A deterministic DAG serialization of alpha-equivalent expressions.
Binder names/annotations and metadata are ignored, like Lean's Expr.eqv;
constants, universes, applications, literals, projections and let flags remain.
-/
partial def intern (privateModule : Name) (e : Expr) : StateM ExprTable Nat := do
  if let .mdata _ b := e then return ← intern privateModule b
  if let some n := (← get).ids[e]? then return n
  let node ← match e with
    | .bvar n => pure <| Json.arr #[toJson "bvar", toJson n]
    | .sort l => pure <| Json.arr #[toJson "sort", toJson (reprStr l)]
    | .const n ls => pure <| Json.arr #[toJson "const", nameJson (normalizedName privateModule n), toJson (ls.map reprStr)]
    | .app f a => do pure <| Json.arr #[toJson "app", toJson (← intern privateModule f), toJson (← intern privateModule a)]
    | .lam _ t b _ => do pure <| Json.arr #[toJson "lam", toJson (← intern privateModule t), toJson (← intern privateModule b)]
    | .forallE _ t b _ => do pure <| Json.arr #[toJson "forall", toJson (← intern privateModule t), toJson (← intern privateModule b)]
    | .letE _ t v b flag => do pure <| Json.arr #[toJson "let", toJson (← intern privateModule t), toJson (← intern privateModule v), toJson (← intern privateModule b), toJson flag]
    | .lit l => pure <| Json.arr #[toJson "lit", toJson (reprStr l)]
    | .proj n i b => do pure <| Json.arr #[toJson "proj", nameJson (normalizedName privateModule n), toJson i, toJson (← intern privateModule b)]
    | .fvar n => pure <| Json.arr #[toJson "fvar", nameJson n.name]
    | .mvar n => pure <| Json.arr #[toJson "mvar", nameJson n.name]
    | .mdata _ _ => unreachable!
  let id := (← get).nodes.size
  modify fun s => { ids := s.ids.insert e id, nodes := s.nodes.push node }
  return id

def exprJson (privateModule : Name) (e : Expr) : Json :=
  let (root, table) := intern privateModule e |>.run {}
  Json.arr #[toJson root, Json.arr table.nodes]

/-- Extract one environment per process; never retain two Mathlib environments. -/
def main (args : List String) : IO UInt32 := do
  let [moduleName, namesPath, outputPath, mode] := args
    | throw <| IO.userError "Expected module, names path, snapshot path, canonical|solution"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := moduleName.toName }] {} (level := .exported)
  let names ← if mode == "canonical" then do
      let some moduleIdx := env.getModuleIdx? moduleName.toName
        | throw <| IO.userError "Canonical module missing"
      let names := env.constants.toList.filterMap fun (name, _) =>
        if env.getModuleIdxFor? name == some moduleIdx then some name else none
      let names := names.toArray.qsort (fun a b => a.toString < b.toString)
      IO.FS.writeFile namesPath (Json.arr (names.map nameJson)).compress
      pure names
    else if mode == "solution" then do
      let j ← IO.ofExcept <| Json.parse (← IO.FS.readFile namesPath)
      (← IO.ofExcept j.getArr?).mapM fun j => IO.ofExcept (parseName j)
    else throw <| IO.userError "Invalid extraction mode"
  let targets := [`PresentationComplex.presentation_complex, `PresentationComplex.every_group_fundamental_group]
  if !targets.all names.contains || names.isEmpty then
    throw <| IO.userError "Missing headline declarations"
  let privateNames := names.filter isPrivateName
  if privateNames.size != 9 then throw <| IO.userError "Unexpected private auxiliary inventory"
  let privateModule := if mode == "canonical" then moduleName.toName else `PresentationPackage.Construction
  -- Canonical original names are carried through the name file. The helper
  -- suffix must be in the explicit allowlist; target names are constructed
  -- injectively with Lean's own private-name constructor.
  for name in privateNames do
    if !privateHelpers.contains (privateToUserName name) then
      throw <| IO.userError s!"Unexpected private helper {name}"
    if mode == "canonical" && name != mkPrivateNameCore moduleName.toName (privateToUserName name) then
      throw <| IO.userError s!"Unexpected private name prefix {name}"
  let mapped := privateNames.toList.map fun n => mkPrivateNameCore `PresentationPackage.Construction (privateToUserName n)
  if mapped.eraseDups.length != 9 then throw <| IO.userError "Private name mapping is not bijective"
  let out ← IO.FS.Handle.mk outputPath .write
  let mut definitions := 0
  for name in names do
    let lookup := if mode == "solution" && isPrivateName name then
        mkPrivateNameCore `PresentationPackage.Construction (privateToUserName name)
      else name
    let some info := env.find? lookup | throw <| IO.userError s!"Missing declaration {name}"
    if isPrivateName name then
      IO.println s!"Mapped private auxiliary: {name} -> {lookup}"
      let expectedDefinition := name.getString! == "splitter"
      if (expectedDefinition && !info.isDefinition) || (!expectedDefinition && !info.isTheorem) then
        throw <| IO.userError s!"Unexpected private helper kind {lookup}"
    else if hasPrivateReference info.type || (info.value?.map hasPrivateReference).getD false then
      throw <| IO.userError s!"Public declaration references private helper: {name}"
    let value := if info.isDefinition then info.value?.map (exprJson privateModule) else none
    if info.isDefinition then
      definitions := definitions + 1
      if value.isNone then throw <| IO.userError s!"Missing exposed definition body {name}"
    out.putStrLn <| (Json.arr #[nameJson (normalizedName privateModule lookup), Json.arr (info.levelParams.toArray.map nameJson),
      exprJson privateModule info.type, value.getD Json.null]).compress
  if definitions == 0 then throw <| IO.userError "No construction definition bodies"
  IO.println "Private auxiliary mapping: six equation theorems and three splitter definitions; public declarations have no private references"
  IO.println s!"Extracted {names.size} declaration types and {definitions} definition bodies from {moduleName}"
  return 0
