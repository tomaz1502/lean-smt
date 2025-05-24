import Lean.Meta.Tactic.AC.Main
import Smt.Reconstruct.Builtin.Lemmas
import Qq

namespace Lean.Meta.AC

open Lean.Elab Tactic Qq

/-- Similar to `rewriteUnnormalized`, but rewrite is only applied at the top level. -/
def rewriteUnnormalizedTop (mv : MVarId) : MetaM Unit := do
  let some (α, l, r) := (← mv.getType).eq?
    | throwError "[ac_rfl_top] expected a top level equality with AC operator on lhs and/or rhs, got {← mv.getType}"
  let lvl ← Meta.getLevel α
  let (nl, pl) ← normalize l
  let (nr, pr) ← normalize r
  if nl == r then
    let some pl := pl | throwError "[ac_rfl_top] expected {l} to have an AC operator"
    mv.assign pl
  else if l == nr then
    let some pr := pr | throwError "[ac_rfl_top] expected {r} to have an AC operator"
    mv.assign (mkApp4 (.const ``Eq.symm [lvl]) α r l pr)
  else if nl == nr then
    let some pl := pl | throwError "[ac_rfl_top] expected {l} to have an AC operator"
    let some pr := pr | throwError "[ac_rfl_top] expected {r} to have an AC operator"
    mv.assign (mkApp6 (.const ``Eq.same_root [lvl]) α l nl r pl pr)
  else
    throwError "[ac_rfl_top] expected {l} and {r} to have the same AC operator"
where
  normalize (e : Expr) : MetaM (Expr × Option Expr) := do
    let bin op l r := e | return (e, none)
    let some pc ← preContext op | return (e, none)
    let (p, ne) ← buildNormProof pc l r
    return (ne, some p)

open Lean.Meta.AC Lean.Data.AC Std in
def buildNativeNormProof (preContext : PreContext) (l r : Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let (atoms, acExpr) ← toACExpr preContext.op l r
  let proof ← abstractAtoms preContext atoms fun varsData => do
    let u ← getLevel (← inferType atoms[0]!)
    let α : Q(Type u) ← inferType atoms[0]!
    let context : Q(Data.AC.Context $α) ← mkContext α u varsData
    let isNeutrals := varsData.map (·.2.isSome)
    let vars := varsData.map (·.1)
    let acExprNormed := Data.AC.evalList ACExpr preContext $ Data.AC.norm (preContext, isNeutrals) acExpr
    let lhs : Q(Data.AC.Expr) := convert acExpr
    let rhs : Q(Data.AC.Expr) := convert acExprNormed
    let proof := mkAppN (mkConst ``Context.eq_of_norm [u]) #[α, context, lhs, rhs, ←nativeDecide q((norm $context $lhs == norm $context $rhs) = true)]
    let proofType ← mkEq (convertTarget vars acExpr) (convertTarget vars acExprNormed)
    let proof := mkExpectedPropHint proof proofType
    return proof
  let some (_, _, tgt) := (← inferType proof).eq? | panic! "unexpected proof type"
  return (proof, tgt)
where
  mkContext (α : Expr) (u : Level) (vars : Array (Expr × Option Expr)) : MetaM Expr := do
    let arbitrary := vars[0]!.1
    let plift := mkApp (mkConst ``PLift [.zero])
    let pliftUp := mkApp2 (mkConst ``PLift.up [.zero])
    let noneE tp   := mkApp  (mkConst ``Option.none [.zero]) (plift tp)
    let someE tp v := mkApp2 (mkConst ``Option.some [.zero]) (plift tp) (pliftUp tp v)
    let vars ← vars.mapM fun ⟨x, inst?⟩ =>
      let isNeutral :=
        let isNeutralClass := mkApp3 (mkConst ``LawfulIdentity [u]) α preContext.op x
        match inst? with
        | none => noneE isNeutralClass
        | some isNeutral => someE isNeutralClass isNeutral
      return mkApp4 (mkConst ``Variable.mk [u]) α preContext.op x isNeutral

    let vars := vars.toList
    let vars ← mkListLit (mkApp2 (mkConst ``Variable [u]) α preContext.op) vars

    let comm :=
      let commClass := mkApp2 (mkConst ``Commutative [u]) α preContext.op
      match preContext.comm with
      | none => noneE commClass
      | some comm => someE commClass comm

    let idem :=
      let idemClass := mkApp2 (mkConst ``IdempotentOp [u]) α preContext.op
      match preContext.idem with
      | none => noneE idemClass
      | some idem => someE idemClass idem

    return mkApp7 (mkConst ``Lean.Data.AC.Context.mk [u]) α preContext.op preContext.assoc comm idem vars arbitrary

  convert : ACExpr → Expr
    | .op l r => mkApp2 (mkConst ``Data.AC.Expr.op) (convert l) (convert r)
    | .var x => mkApp (mkConst ``Data.AC.Expr.var) $ mkNatLit x

  convertTarget (vars : Array Expr) : ACExpr → Expr
    | .op l r => mkApp2 preContext.op (convertTarget vars l) (convertTarget vars r)
    | .var x => vars[x]!
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

def nativeRewriteUnnormalizedTop (mv : MVarId) : MetaM Unit := do
  let some (α, l, r) := (← mv.getType).eq?
    | throwError "[ac_rfl_top] expected a top level equality with AC operator on lhs and/or rhs, got {← mv.getType}"
  let lvl ← Meta.getLevel α
  let (nl, pl) ← normalize l
  let (nr, pr) ← normalize r
  if nl == r then
    let some pl := pl | throwError "[ac_rfl_top] expected {l} to have an AC operator"
    mv.assign pl
  else if l == nr then
    let some pr := pr | throwError "[ac_rfl_top] expected {r} to have an AC operator"
    mv.assign (mkApp4 (.const ``Eq.symm [lvl]) α r l pr)
  else if nl == nr then
    let some pl := pl | throwError "[ac_rfl_top] expected {l} to have an AC operator"
    let some pr := pr | throwError "[ac_rfl_top] expected {r} to have an AC operator"
    mv.assign (mkApp6 (.const ``Eq.same_root [lvl]) α l nl r pl pr)
  else
    throwError "[ac_rfl_top] expected {l} and {r} to have the same AC operator"
where
  normalize (e : Expr) : MetaM (Expr × Option Expr) := do
    let bin op l r := e | return (e, none)
    let some pc ← preContext op | return (e, none)
    let (p, ne) ← buildNormProof pc l r
    return (ne, some p)

syntax (name := acRflTop) "ac_rfl_top" : tactic

@[tactic acRflTop] def evalacRflTop : Lean.Elab.Tactic.Tactic := fun _ => do
  let goal ← getMainGoal
  goal.withContext (rewriteUnnormalizedTop goal)

syntax (name := nativeAcRflTop) "native_ac_rfl_top" : tactic

@[tactic nativeAcRflTop] def evalnativeAcRflTop : Lean.Elab.Tactic.Tactic := fun _ => do
  let goal ← getMainGoal
  goal.withContext (nativeRewriteUnnormalizedTop goal)

local instance : Std.Associative (α := Nat) (· + ·) := ⟨Nat.add_assoc⟩
local instance : Std.Commutative (α := Nat) (· + ·) := ⟨Nat.add_comm⟩

example (a b c d : Nat) : 2 * (a + b + c + d) = 2 * (d + (b + c) + a) := by
  try ac_rfl_top
  ac_rfl

example (a b c d : Nat) : a + b + c + d + (2 * (a + b)) = d + (b + c) + a + (2 * (b + a)) := by
  try ac_rfl_top
  ac_rfl

example (a b c d : Nat) : a + b + c + d + (a + b) = d + (b + c) + a + (b + a) := by
  ac_rfl_top

example (a b c d : Nat) : 2 * (a + b + c + d) = 2 * (d + (b + c) + a) := by
  try native_ac_rfl_top
  ac_rfl

example (a b c d : Nat) : a + b + c + d + (2 * (a + b)) = d + (b + c) + a + (2 * (b + a)) := by
  try native_ac_rfl_top
  ac_rfl

example (a b c d : Nat) : a + b + c + d + (a + b) = d + (b + c) + a + (b + a) := by
  native_ac_rfl_top

end Lean.Meta.AC
