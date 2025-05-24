/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Qq
import Smt.Recognizers
import Smt.Reconstruct.Rat.Polynorm

namespace Smt.Reconstruct.Rat

open Qq in
def PolyNorm.Monomial.toExpr (m : Monomial) (ppCtx : Var → Q(Rat)) : Q(Rat) :=
  if h : m.vars = [] then
    toExprCoeff m.coeff
  else
    if m.coeff = 1 then
      (m.vars.drop 1).foldl (fun acc v => q($acc * $(ppCtx v))) (ppCtx (m.vars.head h))
    else
      m.vars.foldl (fun acc v => q($acc * $(ppCtx v))) (toExprCoeff m.coeff)
where
  toExprCoeff (c : Rat) : Q(Rat) :=
  let num : Q(Rat) := mkRatLit c.num.natAbs
  if c.den == 1 then
    if c.num ≥ 0 then
      q($num)
    else
      q(-$num)
  else
    let den : Q(Rat) := mkRatLit c.den
    if c.num ≥ 0 then
      q($num / $den)
    else
      q(-$num / $den)
  mkRatLit (n : Nat) : Q(Rat) :=
    let l : Q(Nat) := Lean.mkRawNatLit n
    q(OfNat.ofNat $l)

open Lean Qq

abbrev PolyM := StateT (Array Q(Int) × Array Q(Rat)) MetaM

def getIntIndex (e : Q(Int)) : PolyM Nat := do
  let ⟨is, rs⟩ ← get
  if let some i := is.findIdx? (· == e) then
    return i
  else
    let size := is.size
    set (is.push e, rs)
    return size

def getRatIndex (e : Q(Rat)) : PolyM Nat := do
  let ⟨is, rs⟩ ← get
  if let some i := rs.findIdx? (· == e) then
    return i
  else
    let size := rs.size
    set (is, rs.push e)
    return size

partial def reifyRatVal (e : Q(Rat)) : PolyM Rat := do
  if let some n := e.natLitOf? q(Rat) then
    return n
  else if let some e := e.negOf? q(Rat) then
    return -(← reifyRatVal e)
  else if let some (x, y) := e.hAddOf? q(Rat) q(Rat) then
    return (← reifyRatVal x) + (← reifyRatVal y)
  else if let some (x, y) := e.hSubOf? q(Rat) q(Rat) then
    return (← reifyRatVal x) - (← reifyRatVal y)
  else if let some (x, y) := e.hMulOf? q(Rat) q(Rat) then
    return (← reifyRatVal x) * (← reifyRatVal y)
  else if let some (x, y) := e.hDivOf? q(Rat) q(Rat) then
    return (← reifyRatVal x) / (← reifyRatVal y)
  else
    throwError "[poly_norm] expected a rational number, got {e}"

partial def reifyInt (e : Q(Int)) : PolyM Q(PolyNorm.IntExpr) := do
  if let some n := e.natLitOf? q(Int) then
    return q(.val (OfNat.ofNat $n))
  else if let some e := e.negOf? q(Int) then
    return q(.neg $(← reifyInt e))
  else if let some (x, y) := e.hAddOf? q(Int) q(Int) then
    return q(.add $(← reifyInt x) $(← reifyInt y))
  else if let some (x, y) := e.hSubOf? q(Int) q(Int) then
    return q(.sub $(← reifyInt x) $(← reifyInt y))
  else if let some (x, y) := e.hMulOf? q(Int) q(Int) then
    return q(.mul $(← reifyInt x) $(← reifyInt y))
  else
    let v : Nat ← getIntIndex e
    return q(.var $v)

partial def reifyRat (e : Q(Rat)) : PolyM Q(PolyNorm.RatExpr) := do
  if let some n := e.natLitOf? q(Rat) then
    return q(.val (OfNat.ofNat $n))
  else if let some e := e.negOf? q(Rat) then
    return q(.neg $(← reifyRat e))
  else if let some (x, y) := e.hAddOf? q(Rat) q(Rat) then
    return q(.add $(← reifyRat x) $(← reifyRat y))
  else if let some (x, y) := e.hSubOf? q(Rat) q(Rat) then
    return q(.sub $(← reifyRat x) $(← reifyRat y))
  else if let some (x, y) := e.hMulOf? q(Rat) q(Rat) then
    return q(.mul $(← reifyRat x) $(← reifyRat y))
  else if let some (x, y) := e.hDivOf? q(Rat) q(Rat) then
    return q(.divConst $(← reifyRat x) $(PolyNorm.Monomial.toExpr.toExprCoeff (← reifyRatVal y)))
  else if let some e := e.intCastOf? q(Rat) then
    return q(.cast $(← reifyInt e))
  else
    let v : Nat ← getRatIndex e
    return q(.var $v)

def polyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (reifyRat l).run (#[], #[])
  let (r, (is, rs)) ← (reifyRat r).run (is, rs)
  let ictx : Q(PolyNorm.IntContext) ← if h : 0 < is.size
    then do let is : Q(RArray Int) ← (RArray.ofArray is h).toExpr q(Int) id; pure q(«$is».get)
    else pure q(fun _ => 0)
  let rctx : Q(PolyNorm.RatContext) ← if h : 0 < rs.size
    then do let rs : Q(RArray Rat) ← (RArray.ofArray rs h).toExpr q(Rat) id; pure q(«$rs».get)
    else pure q(fun _ => 0)
  let h : Q(«$l».toPoly = «$r».toPoly) := .app q(@Eq.refl.{1} PolyNorm.Polynomial) q(«$l».toPoly)
  mv.assign q(@PolyNorm.RatExpr.eval_eq_from_toPoly_eq $ictx $rctx $l $r $h)

def nativePolyNorm (mv : MVarId) : MetaM Unit := do
  let some (_, l, r) := (← mv.getType).eq?
    | throwError "[poly_norm] expected an equality, got {← mv.getType}"
  let (l, (is, rs)) ← (reifyRat l).run (#[], #[])
  let (r, (is, rs)) ← (reifyRat r).run (is, rs)
  let ictx : Q(PolyNorm.IntContext) ← if h : 0 < is.size
    then do let is : Q(RArray Int) ← (RArray.ofArray is h).toExpr q(Int) id; pure q(«$is».get)
    else pure q(fun _ => 0)
  let rctx : Q(PolyNorm.RatContext) ← if h : 0 < rs.size
    then do let rs : Q(RArray Rat) ← (RArray.ofArray rs h).toExpr q(Rat) id; pure q(«$rs».get)
    else pure q(fun _ => 0)
  let h ← nativeDecide q(«$l».toPoly = «$r».toPoly)
  mv.assign q(@PolyNorm.RatExpr.eval_eq_from_toPoly_eq $ictx $rctx $l $r $h)
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
    Rat.polyNorm mv
    replaceMainGoal []

syntax (name := nativePolyNorm) "native_poly_norm" : tactic

open Lean.Elab Tactic in
@[tactic nativePolyNorm] def evalNativePolyNorm : Tactic := fun _ =>
  withMainContext do
    let mv ← Tactic.getMainGoal
    Rat.nativePolyNorm mv
    replaceMainGoal []

end Smt.Reconstruct.Rat.Tactic

example (x y z : Rat) : 1 * (x + y) * z / 4 = 1 / (2 * 2) * (z * y + x * z) := by
  poly_norm

example (x y : Int) (z : Rat) : 1 * (↑x + ↑y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  poly_norm

example (x y : Int) (z : Rat) : 1 * ↑(x + y) * z / 4 = 1 / (2 * 2) * (z * ↑y + ↑x * z) := by
  native_poly_norm
