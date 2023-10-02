/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Lean

import Smt.Reconstruction.Certifying.Pull
import Smt.Reconstruction.Certifying.Util

open Lean Elab Tactic Meta

namespace Smt.Reconstruction.Certifying

def invertPermutation {m : Type → Type v} [Monad m] : List Nat → m (List Nat) := fun p => do
  let size := p.length
  let p: Array Nat := ⟨p⟩
  let mut answer: Array Nat := ⟨List.replicate size 0⟩
  for i in [ : size] do
    answer := answer.setD (p.get! i) i
  return answer.toList

def splitAnd (n : Nat) (val : Expr) : MetaM (List Expr) :=
  match n with
  | 0 => pure [val]
  | n' + 1 => do
    let curr ← mkAppM ``And.left #[val]
    let rest ← splitAnd n' (← mkAppM ``And.right #[val])
    return (curr :: rest)

def andTerms (props : List Expr) : MetaM Expr :=
  match props with
  | [] => throwError "[andProps]: empty list"
  | [e] => pure e
  | e₁::e₂::es => do
    let rest ← andTerms (e₂ :: es)
    mkAppM ``And.intro #[e₁, rest]

def permutateOrCore (val : Expr) (perm : List Nat)
    (suffIdx : Option Nat) : MetaM Expr := do
  let type ← instantiateMVars (← expandLet (← Meta.inferType val))
  let suffIdx: Nat ←
    match suffIdx with
    | some i => pure i
    | none   => pure $ (← getLength type) - 1
  let props ← collectPropsInOrChain' suffIdx type
  let goal ← createOrChain (permutateList props perm)
  let notGoal := mkApp (mkConst `Not) goal
  withLocalDeclD (← mkFreshId) notGoal $ fun bv => do
    let liPerm := listExpr (permutateList props perm) (.sort .zero)
    let li := listExpr props (Expr.sort Level.zero)
    let notAndPerm := mkApp2 (mkConst ``deMorgan₃) liPerm bv
    let terms ← splitAnd suffIdx notAndPerm
    let invPerm ← invertPermutation perm
    let invPermTerms := permutateList terms invPerm
    let termsJoined ← andTerms invPermTerms
    let notOrPf := mkApp2 (mkConst ``deMorgan₄) li termsJoined
    let lambda ← mkLambdaFVars #[bv] notOrPf
    let mtLambda ← mkAppM ``mt #[lambda]
    let notNotVal ← mkAppM ``notNotIntro #[val]
    let notNotAnswer := mkApp mtLambda notNotVal
    mkAppM ``notNotElim #[notNotAnswer]

-- TODO: find a way to remove '?' without breaking the parser
syntax (name := permutateOr) "permutateOr" term "," ("[" term,* "]")? ("," term)? : tactic

def parsePermuteOr : Syntax → TacticM (List Nat × Option Nat)
  | `(tactic| permutateOr $_, [ $[$hs],* ]) =>
    hs.toList.mapM stxToNat >>= λ li => return ⟨li, none⟩
  | `(tactic| permutateOr $_, [ $[$hs],* ], $i) =>
    hs.toList.mapM stxToNat >>= λ li =>
      elabTerm i none >>= λ i' =>
        return ⟨li, getNatLit? i'⟩
  | _ => throwError "[permutateOr]: wrong usage"

@[tactic permutateOr] def evalPermutateOr : Tactic := fun stx =>
  withMainContext do
    trace[smt.debug] m!"[permutateOr] start time: {← IO.monoNanosNow}ns"
    let hyp ← elabTerm stx[1] none
    let ⟨hs, suffIdx⟩ ← parsePermuteOr stx
    let answer ← permutateOrCore hyp hs suffIdx
    let mvar ← getMainGoal
    let type ← instantiateMVars (← Meta.inferType answer) 
    let fname ← mkFreshId
    let (_, mvar') ← MVarId.intro1P $ ← mvar.assert fname type answer
    replaceMainGoal [mvar']
    evalTactic (← `(tactic| exact $(mkIdent fname)))
    trace[smt.debug] m!"[permutateOr] end time: {← IO.monoNanosNow}ns"

example : A ∨ B ∨ C ∨ D ∨ E → E ∨ C ∨ D ∨ B ∨ A := by
  intro h
  permutateOr h, [4, 2, 3, 1, 0]

end Smt.Reconstruction.Certifying
