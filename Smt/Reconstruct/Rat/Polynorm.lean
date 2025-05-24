/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

import Smt.Reconstruct.Rat.Core

namespace Smt.Reconstruct.Rat.PolyNorm

structure Var where
  type : Bool
  val  : Nat
deriving DecidableEq, Repr

instance : LE Var where
  le v₁ v₂ := v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val ≤ v₂.val)

instance : LT Var where
  lt v₁ v₂ := v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val < v₂.val)

instance (v₁ v₂ : Var) : Decidable (v₁ ≤ v₂) :=
  if h : v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val ≤ v₂.val) then isTrue h else isFalse h

instance (v₁ v₂ : Var) : Decidable (v₁ < v₂) :=
  if h : v₁.type < v₂.type ∨ (v₁.type = v₂.type ∧ v₁.val < v₂.val) then isTrue h else isFalse h

def Context := Var → Rat

def IntContext := Nat → Int
def RatContext := Nat → Rat

structure Monomial where
  coeff : Rat
  vars : List Var
deriving Inhabited, Repr, DecidableEq

namespace Monomial

def neg (m : Monomial) : Monomial :=
  { m with coeff := -m.coeff }

def add (m₁ m₂ : Monomial) (_ : m₁.vars = m₂.vars) : Monomial :=
  { coeff := m₁.coeff + m₂.coeff, vars := m₁.vars }

-- Invariant: monomial variables remain sorted.
def mul (m₁ m₂ : Monomial) : Monomial :=
  let coeff := m₁.coeff * m₂.coeff
  let vars := m₁.vars.foldr insert m₂.vars
  { coeff, vars }
where
  insert (x : Var) : List Var → List Var
    | [] => [x]
    | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def divConst (m : Monomial) (c : Rat) : Monomial :=
  { m with coeff := m.coeff / c }

def eval (ctx : Context) (m : Monomial) : Rat :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem eval_neg {m : Monomial} : m.neg.eval ctx = -m.eval ctx := by
  simp only [neg, eval, Rat.neg_mul]

section

variable {op : α → α → α}

-- Can be generalized to `List.foldl_assoc`.
theorem foldl_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (z1 z2 : α):
  List.foldl (fun z a => op z (g a)) (op z1 z2) l =
  op z1 (List.foldl (fun z a => op z (g a)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, assoc]

theorem foldr_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c)) (z1 z2 : α):
  List.foldr (fun z a => op a (g z)) (op z1 z2) l =
  op z1 (List.foldr (fun z a => op a (g z)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldr_cons, ih, assoc]

end
-- Can be generalized.
theorem foldl_mul_insert {ctx : Context} :
  List.foldl (fun z a => z * (ctx a)) 1 (mul.insert y ys) =
  (ctx y) * List.foldl (fun z a => z * (ctx a)) 1 ys := by
  induction ys with
  | nil => simp [mul.insert]
  | cons x ys ih =>
    by_cases h : y ≤ x
    · simp [mul.insert, h, foldl_assoc Rat.mul_assoc (ctx y) (ctx x), Rat.mul_assoc]
    · simp only [mul.insert, h, List.foldl_cons, ite_false, Rat.mul_comm,
                 foldl_assoc Rat.mul_assoc, ih]
      rw [← Rat.mul_assoc, Rat.mul_comm (ctx x) (ctx y), Rat.mul_assoc]

theorem eval_add {m n : Monomial} (h : m.vars = n.vars) :
  (m.add n h).eval ctx = m.eval ctx + n.eval ctx := by
  simp only [add, eval, Rat.add_mul, h]

theorem eval_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).eval ctx = m₁.eval ctx * m₂.eval ctx := by
  simp only [eval, mul, Rat.mul_assoc]; congr 1
  rw [← Rat.mul_assoc, Rat.mul_comm _ m₂.coeff, Rat.mul_assoc]; congr 1
  induction m₁.vars with
  | nil => simp [Rat.mul_assoc]
  | cons y ys ih =>
    simp [foldl_mul_insert, ←foldl_assoc Rat.mul_assoc, ih]

theorem eval_divConst {m : Monomial} : (m.divConst c).eval ctx = m.eval ctx / c := by
  simp only [eval, divConst, Rat.mul_div_right_comm]

end Monomial

abbrev Polynomial := List Monomial

namespace Polynomial

def neg (p : Polynomial) : Polynomial :=
  p.map Monomial.neg

-- NOTE: implementation merges monomials with same variables.
-- Invariant: monomials remain sorted.
def add (p q : Polynomial) : Polynomial :=
  p.foldr insert q
where
  insert (m : Monomial) : Polynomial → Polynomial
    | [] => [m]
    | n :: ns =>
      if m.vars < n.vars then
        m :: n :: ns
      else if h : m.vars = n.vars then
        let m' := m.add n h
        if m'.coeff = 0 then ns else m' :: ns
      else
        n :: insert m ns

def sub (p q : Polynomial) : Polynomial :=
  p.add q.neg

-- Invariant: monomials remain sorted.
def mulMonomial (m : Monomial) (p : Polynomial) : Polynomial :=
  p.foldr (fun n acc => Polynomial.add [m.mul n] acc) []

-- Invariant: monomials remain sorted.
def mul (p q : Polynomial) : Polynomial :=
  p.foldl (fun acc m => (q.mulMonomial m).add acc) []

def divConst (p : Polynomial) (c : Rat) : Polynomial :=
  p.map (·.divConst c)

def eval (ctx : Context) (p : Polynomial) : Rat :=
  p.foldl (fun acc m => acc + m.eval ctx) 0

theorem foldl_add_insert (ctx : Context) :
  List.foldl (fun z a => z + (Monomial.eval ctx a)) 0 (add.insert m p) =
  (Monomial.eval ctx m) + List.foldl (fun z a => z + (Monomial.eval ctx a)) 0 p := by
  induction p with
  | nil => simp [add.insert]
  | cons n p ih =>
    simp only [add.insert]
    split <;> rename_i hlt <;> simp only [List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc]
    · split <;> rename_i heq
      · split <;> rename_i hneq
        · rw [←Rat.add_assoc, Rat.add_comm, ←Monomial.eval_add heq]
          simp [Monomial.eval, hneq]
        · simp only [List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Monomial.eval_add, heq, Rat.add_assoc]
      · simp only [List.foldl_cons, Rat.add_comm 0, ih, Monomial.foldl_assoc Rat.add_assoc]
        rw [←Rat.add_assoc, Rat.add_comm (Monomial.eval ctx n), Rat.add_assoc]

theorem eval_neg {p : Polynomial} : p.neg.eval ctx = -p.eval ctx := by
  simp only [eval, neg]
  induction p with
  | nil => simp
  | cons m p ih =>
    simp only [List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Rat.neg_add, ←ih, List.map, Monomial.eval_neg]

theorem eval_add {p q : Polynomial} : (p.add q).eval ctx = p.eval ctx + q.eval ctx := by
  simp only [eval, add]
  induction p with
  | nil => simp [add.insert]
  | cons x ys ih =>
    simp only [List.foldr_cons, List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Rat.add_assoc]
    rw [← ih, foldl_add_insert]

theorem eval_sub {p q : Polynomial} : (p.sub q).eval ctx = p.eval ctx - q.eval ctx := by
  simp only [sub, eval_neg, eval_add, Rat.sub_eq_add_neg]

theorem eval_mulMonomial {p : Polynomial} : (p.mulMonomial m).eval ctx = m.eval ctx * p.eval ctx := by
  simp only [eval, mulMonomial, add]
  induction p with
  | nil => simp
  | cons n p ih =>
    simp only [List.foldl_cons, List.foldr_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, Rat.mul_add, ←ih]
    simp [foldl_add_insert, Monomial.eval_mul]

theorem eval_cons {p : List Monomial} {ctx : Context} : eval ctx (m :: p) = m.eval ctx + eval ctx p := by
  simp only [eval, List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc]

theorem eval_nil_add : eval ctx (p.add []) = eval ctx p := by
  induction p with
  | nil => simp [add]
  | cons n p ih =>
    simp [eval_add, List.foldr_cons, eval_cons, ih, show eval ctx [] = 0 by rfl]

theorem eval_add_insert {g : Monomial → Polynomial} :
  eval ctx (List.foldl (fun acc m => (g m).add acc) n p) = eval ctx n + eval ctx (List.foldl (fun acc m => (g m).add acc) [] p) := by
  revert n
  induction p with
  | nil => simp [eval]
  | cons k p ih =>
    intro n
    simp only [List.foldl_cons, List.foldr, @ih n]
    rw [ih, @ih ((g k).add []), ← Rat.add_assoc, eval_nil_add, eval_add, Rat.add_comm _ (eval ctx n)]

theorem eval_foldl {g : Monomial → Polynomial} :
  eval ctx (List.foldl (fun acc m => ((g m).add (acc))) [] p) = List.foldl (fun acc m => (g m).eval ctx + acc) 0 p := by
  induction p with
  | nil => simp [eval]
  | cons n p ih =>
    simp only [List.foldl_cons, Rat.add_comm, List.foldr] at *
    rw [Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc, ←ih, eval_add_insert, eval_nil_add]

theorem eval_mul {p q : Polynomial} : (p.mul q).eval ctx = p.eval ctx * q.eval ctx :=by
  simp only [mul]
  induction p with
  | nil => simp [eval]
  | cons n p ih =>
    simp only [List.foldl_cons, eval_cons, Rat.add_mul, ← ih]
    rw [eval_foldl, eval_add_insert, ←eval_mulMonomial, eval_nil_add, eval_foldl]

theorem eval_divConst {p : Polynomial} : (p.divConst c).eval ctx = p.eval ctx / c := by
  simp only [eval, divConst]
  induction p with
  | nil => simp [Rat.zero_div]
  | cons x ys ih =>
    simp only [List.map_cons, List.foldl_cons, Rat.add_comm 0, Monomial.foldl_assoc Rat.add_assoc]
    rw [Monomial.eval_divConst, ih, Rat.add_div]

end Polynomial

inductive IntExpr where
  | val (v : Int)
  | var (v : Nat)
  | neg (a : IntExpr)
  | add (a b : IntExpr)
  | sub (a b : IntExpr)
  | mul (a b : IntExpr)
deriving Inhabited, Repr

namespace IntExpr

def toPoly : IntExpr → Polynomial
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := 1, vars := [⟨false, v⟩] }]
  | .neg a => a.toPoly.neg
  | .add a b => Polynomial.add a.toPoly b.toPoly
  | .sub a b => Polynomial.sub a.toPoly b.toPoly
  | .mul a b => Polynomial.mul a.toPoly b.toPoly

def eval (ctx : IntContext) : IntExpr → Int
  | .val v => v
  | .var v => ctx v
  | .neg a => -a.eval ctx
  | .add a b => a.eval ctx + b.eval ctx
  | .sub a b => a.eval ctx - b.eval ctx
  | .mul a b => a.eval ctx * b.eval ctx

theorem eval_toPoly {rctx : RatContext} {e : IntExpr} : e.eval ictx = e.toPoly.eval (fun ⟨b, n⟩ => if b then rctx n else ictx n) := by
  induction e with
  | val v =>
    simp only [eval, toPoly]
    split <;> rename_i hv
    · rewrite [hv]; rfl
    · simp [Polynomial.eval, Monomial.eval]
  | var v =>
    simp [eval, toPoly, Polynomial.eval, Monomial.eval]
  | neg a ih =>
    simp only [eval, toPoly, Polynomial.eval_neg, Rat.intCast_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_add, Rat.intCast_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_sub, Rat.intCast_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_mul, Rat.intCast_mul, ih₁, ih₂]

end IntExpr

inductive RatExpr where
  | val (v : Rat)
  | var (v : Nat)
  | neg (a : RatExpr)
  | add (a b : RatExpr)
  | sub (a b : RatExpr)
  | mul (a b : RatExpr)
  | divConst (a : RatExpr) (c : Rat)
  | cast (a : IntExpr)
deriving Inhabited, Repr

namespace RatExpr

def toPoly : RatExpr → Polynomial
  | .val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | .var v => [{ coeff := 1, vars := [⟨true, v⟩] }]
  | .neg a => a.toPoly.neg
  | .add a b => Polynomial.add a.toPoly b.toPoly
  | .sub a b => Polynomial.sub a.toPoly b.toPoly
  | .mul a b => Polynomial.mul a.toPoly b.toPoly
  | .divConst a c => Polynomial.divConst a.toPoly c
  | .cast a => a.toPoly

def eval (ictx : IntContext) (rctx : RatContext)  : RatExpr → Rat
  | .val v => v
  | .var v => rctx v
  | .neg a => -a.eval ictx rctx
  | .add a b => a.eval ictx rctx + b.eval ictx rctx
  | .sub a b => a.eval ictx rctx - b.eval ictx rctx
  | .mul a b => a.eval ictx rctx * b.eval ictx rctx
  | .divConst a c => a.eval ictx rctx / c
  | .cast a => a.eval ictx

theorem eval_toPoly {e : RatExpr} : e.eval ictx rctx = e.toPoly.eval (fun ⟨b, n⟩ => if b then rctx n else ictx n) := by
  induction e with
  | val v =>
    simp only [eval, toPoly]
    split <;> rename_i hv
    · rewrite [hv]; rfl
    · simp [Polynomial.eval, Monomial.eval]
  | var v =>
    simp [eval, toPoly, Polynomial.eval, Monomial.eval]
  | neg a ih =>
    simp only [eval, toPoly, Polynomial.eval_neg, ih]
  | add a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_add, ih₁, ih₂]
  | sub a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_sub, ih₁, ih₂]
  | mul a b ih₁ ih₂ =>
    simp only [eval, toPoly, Polynomial.eval_mul, ih₁, ih₂]
  | divConst a c ih =>
    simp only [eval, toPoly, Polynomial.eval_divConst, ih]
  | cast a =>
    simpa only [eval] using IntExpr.eval_toPoly

theorem eval_eq_from_toPoly_eq {e₁ e₂ : RatExpr} (h : e₁.toPoly = e₂.toPoly) : e₁.eval ictx rctx = e₂.eval ictx rctx := by
  rw [eval_toPoly, eval_toPoly, h]

end Smt.Reconstruct.Rat.PolyNorm.RatExpr
