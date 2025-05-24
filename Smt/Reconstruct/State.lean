/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import cvc5

namespace Smt

open Lean

structure Reconstruct.Context where
  /-- The user names of the variables in the local context. -/
  userNames : Std.HashMap String FVarId := {}
  /-- Whether to enable native components for proof reconstruction. Speeds up normalization and
      reduction proof steps. However, it adds the Lean compiler to the trusted code base. -/
  native : Bool := false

structure Reconstruct.State where
  termCache : Std.HashMap cvc5.Term Expr := {}
  proofCache : Std.HashMap cvc5.Proof Expr := {}
  count : Nat := 0
  currAssums : Array Expr := #[]
  skippedGoals : Array MVarId := #[]

abbrev ReconstructM := ReaderT Reconstruct.Context (StateT Reconstruct.State MetaM)

abbrev SortReconstructor := cvc5.Sort → ReconstructM (Option Expr)

abbrev TermReconstructor := cvc5.Term → ReconstructM (Option Expr)

abbrev ProofReconstructor := cvc5.Proof → ReconstructM (Option Expr)

namespace Reconstruct

def useNative : ReconstructM Bool :=
  read >>= pure ∘ (·.native)

@[extern "smt_reconstruct_sort"]
opaque reconstructSort (s : cvc5.Sort) : ReconstructM Expr

@[extern "smt_reconstruct_term"]
opaque reconstructTerm (s : cvc5.Term) : ReconstructM Expr

@[extern "smt_reconstruct_proof"]
opaque reconstructProof (s : cvc5.Proof) : ReconstructM Expr

def reconstructSortLevelAndSort (s : cvc5.Sort) : ReconstructM (Level × Expr) := do
  let t ← reconstructSort s
  let .sort u ← Meta.inferType t | throwError "expected a sort, but got\n{t}"
  return ⟨u, t⟩

@[extern "smt_reconstruct_terms"]
opaque reconstructTerms (u : Level) (α : Expr) (ts : Array cvc5.Term) : ReconstructM Expr

def withNewTermCache (k : ReconstructM α) : ReconstructM α := do
  let termCache := (← get).termCache
  modify fun state => { state with termCache := {} }
  let r ← k
  modify fun state => { state with termCache := termCache }
  return r

def traceReconstructTerm (t : cvc5.Term) (r : Except Exception Expr) : ReconstructM MessageData :=
  return m!"{t} ↦ " ++ match r with
    | .ok e    => m!"{e}"
    | .error _ => m!"{bombEmoji}"

def withNewProofCache (k : ReconstructM α) : ReconstructM α := do
  let proofCache := (← get).proofCache
  modify fun state => { state with proofCache := {} }
  let r ← k
  modify fun state => { state with proofCache := proofCache }
  return r

def withProofCache (r : cvc5.Proof → ReconstructM Expr) (pf : cvc5.Proof) : ReconstructM Expr := do
  match (← get).proofCache[pf]? with
  | some e => return e
  | none   => reconstruct r pf
where
  reconstruct r pf := do
    let e ← r pf
    modify fun state => { state with proofCache := state.proofCache.insert pf e }
    return e

def incCount : ReconstructM Nat :=
  modifyGet fun state => (state.count, { state with count := state.count + 1 })

def withAssums (as : Array Expr) (k : ReconstructM α) : ReconstructM α := do
  modify fun state => { state with currAssums := state.currAssums ++ as }
  let r ← k
  modify fun state => { state with currAssums := state.currAssums.take (state.currAssums.size - as.size) }
  return r

def findAssumWithType? (t : Expr) : ReconstructM (Option Expr) := do
  for a in (← get).currAssums.reverse do
    let t' ← a.fvarId!.getType
    if t' == t then
      return some a
  return none

def skipStep (mv : MVarId) : ReconstructM Unit := mv.withContext do
  let state ← get
  let t ← Meta.mkForallFVars state.currAssums (← mv.getType)
  let ctx := state.currAssums.foldr (fun e ctx => ctx.erase e.fvarId!) (← getLCtx)
  let mv' ← Meta.withLCtx ctx (← Meta.getLocalInstances) (Meta.mkFreshExprMVar t)
  let e := mkAppN mv' state.currAssums
  set { state with skippedGoals := state.skippedGoals.push mv'.mvarId! }
  mv.assign e

def addThm (type : Expr) (val : Expr) : ReconstructM Expr := do
  let name := Name.num `s (← incCount)
  let mv ← Meta.mkFreshExprMVar type .natural name
  mv.mvarId!.assign val
  trace[smt.reconstruct.proof] "have {name} : {type} := {val}"
  return mv

def addTac (type : Expr) (tac : MVarId → MetaM Unit) : ReconstructM Expr := do
  let name := Name.num `s (← incCount)
  let mv ← Meta.mkFreshExprMVar type .natural name
  tac mv.mvarId!
  trace[smt.reconstruct.proof] "have {name} : {type} := {mv}"
  return mv

def addTrust (type : Expr) (pf : cvc5.Proof) : ReconstructM Expr := do
  let name := Name.num `s (← incCount)
  let mv ← Meta.mkFreshExprMVar type .natural name
  skipStep mv.mvarId!
  trace[smt.reconstruct.proof] m!"have {name} : {type} := sorry"
  trace[smt.reconstruct.proof]
    m!"rule : {pf.getRule}\npremises : {pf.getChildren.map (·.getResult)}\nargs : {pf.getArguments}\nconclusion : {pf.getResult}"
  return mv

def traceReconstructStep (r : Except Exception Expr) : ReconstructM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

end Reconstruct

end Smt
