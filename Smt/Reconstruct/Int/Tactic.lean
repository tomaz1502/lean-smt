/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

import Qq
import Smt.Recognizers
import Smt.Reconstruct.Int.Polynorm

namespace Smt.Reconstruct.Int

open Lean Qq

abbrev PolyM := StateT (Array Q(Int)) MetaM

def getIndex (e : Q(Int)) : PolyM Nat := do
  let is ← get
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    set (is.push e)
    return size

partial def reify (e : Q(Int)) : PolyM Q(PolyNorm.Expr) := do
  if let some n := e.natLitOf? q(Int) then
    return q(.val (OfNat.ofNat $n))
  else if let some e := e.negOf? q(Int) then
    return q(.neg $(← reify e))
  else if let some (x, y) := e.hAddOf? q(Int) q(Int) then
    return q(.add $(← reify x) $(← reify y))
  else if let some (x, y) := e.hSubOf? q(Int) q(Int) then
    return q(.sub $(← reify x) $(← reify y))
  else if let some (x, y) := e.hMulOf? q(Int) q(Int) then
    return q(.mul $(← reify x) $(← reify y))
  else
    let v : Nat ← getIndex e
    return q(.var $v)

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, (l : Q(Int)), (r : Q(Int))) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, is) ← (reify l).run #[]
  let (r, is) ← (reify r).run is
  let ctx : Q(PolyNorm.Context) ← if h : 0 < is.size
    then do let is : Q(RArray Int) ← (RArray.ofArray is h).toExpr q(Int) id; pure q(«$is».get)
    else pure q(fun _ => 0)
  let hp : Q(«$l».toPoly = «$r».toPoly) := (.app q(@Eq.refl PolyNorm.Polynomial) q(«$l».toPoly))
  let he := q(@PolyNorm.Expr.eval_eq_from_toPoly_eq $ctx $l $r $hp)
  mv.assign he

def nativePolyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, (l : Q(Int)), (r : Q(Int))) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, is) ← (reify l).run #[]
  let (r, is) ← (reify r).run is
  let ctx : Q(PolyNorm.Context) ← if h : 0 < is.size
    then do let is : Q(RArray Int) ← (RArray.ofArray is h).toExpr q(Int) id; pure q(«$is».get)
    else pure q(fun _ => 0)
  let hp ← nativeDecide q(«$l».toPoly = «$r».toPoly)
  let he := q(@PolyNorm.Expr.eval_eq_from_toPoly_eq $ctx $l $r $hp)
  mv.assign he
where
  nativeDecide (p : Q(Prop)) : MetaM Q($p) := do
    let hp : Q(Decidable $p) ← Meta.synthInstance q(Decidable $p)
    let auxDeclName ← mkNativeAuxDecl `_nativePolynorm q(Bool) q(decide $p)
    let b : Q(Bool) := .const auxDeclName []
    return .app q(@of_decide_eq_true $p $hp) (.app q(Lean.ofReduceBool $b true) q(Eq.refl true))
  mkNativeAuxDecl (baseName : Name) (type value : Expr) : MetaM Name := do
    let auxName ← match (← getEnv).asyncPrefix? with
      | none          => Lean.mkAuxName baseName 1
      | some declName => Lean.mkAuxName (declName ++ baseName) 1
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := [], type, value
      hints := .abbrev
      safety := .safe
    }
    addAndCompile decl
    pure auxName

namespace Tactic

syntax (name := polyNorm) "poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic polyNorm] def evalPolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Int.polyNorm mv
    replaceMainGoal []

syntax (name := nativePolyNorm) "native_poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic nativePolyNorm] def evalNativePolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Int.nativePolyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Int.Tactic

example (x y z : Int) : 1 * (x + y) * z  = z * y + x * z := by
  poly_norm

example (x y z : Int) : 1 * (x + y) * z  = z * y + x * z := by
  native_poly_norm
