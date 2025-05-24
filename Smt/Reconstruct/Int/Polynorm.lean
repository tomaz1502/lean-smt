/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Harun Khan
-/

namespace Smt.Reconstruct.Int.PolyNorm

abbrev Var := Nat

def Context := Var → Int

structure Monomial where
  coeff : Int
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

def eval (ctx : Context) (m : Monomial) : Int :=
  m.coeff * m.vars.foldl (fun acc v => acc * ctx v) 1

theorem eval_neg {m : Monomial} : m.neg.eval ctx = -m.eval ctx := by
  simp only [neg, eval, Int.neg_mul_eq_neg_mul]

section

variable {op : α → α → α}

-- Can be generalized to `List.foldl_assoc`.
theorem foldl_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))
  (z1 z2 : α) :
  List.foldl (fun z a => op z (g a)) (op z1 z2) l =
  op z1 (List.foldl (fun z a => op z (g a)) z2 l) := by
  induction l generalizing z1 z2 with
  | nil => rfl
  | cons y ys ih =>
    simp only [List.foldl_cons, ih, assoc]

theorem foldr_assoc {g : β → α} (assoc : ∀ a b c, op (op a b) c = op a (op b c))
  (z1 z2 : α) :
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
    · simp [mul.insert, h, foldl_assoc Int.mul_assoc (ctx y) (ctx x), Int.mul_assoc]
    · simp only [mul.insert, h, List.foldl_cons, ite_false, Int.mul_comm,
                 foldl_assoc Int.mul_assoc, ih]
      rw [←Int.mul_assoc, Int.mul_comm (ctx x) (ctx y), Int.mul_assoc]

theorem eval_add {m n : Monomial} (h : m.vars = n.vars) :
  (m.add n h).eval ctx = m.eval ctx + n.eval ctx := by
  simp only [add, eval, Int.add_mul, h]

theorem eval_mul {m₁ m₂ : Monomial} : (m₁.mul m₂).eval ctx = m₁.eval ctx * m₂.eval ctx := by
  simp only [eval, mul, Int.mul_assoc]; congr 1
  rw [← Int.mul_assoc, Int.mul_comm _ m₂.coeff, Int.mul_assoc]; congr 1
  induction m₁.vars with
  | nil => simp [Int.mul_assoc]
  | cons y ys ih =>
    simp [foldl_mul_insert, ←foldl_assoc Int.mul_assoc, ih]

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

def eval (ctx : Context) (p : Polynomial) : Int :=
  p.foldl (fun acc m => acc + m.eval ctx) 0

theorem foldl_add_insert (ctx : Context) :
  List.foldl (fun z a => z + (Monomial.eval ctx a)) 0 (add.insert m p) =
  (Monomial.eval ctx m) + List.foldl (fun z a => z + (Monomial.eval ctx a)) 0 p := by
  induction p with
  | nil => simp [add.insert]
  | cons n p ih =>
    simp only [add.insert]
    split <;> rename_i hlt <;> simp only [List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc]
    · split <;> rename_i heq
      · split <;> rename_i hneq
        · rw [←Int.add_assoc, Int.add_comm, ←Monomial.eval_add heq]
          simp [Monomial.eval, hneq]
        · simp [-Int.add_zero, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Monomial.eval_add, heq, Int.add_assoc]
      · simp only [List.foldl_cons, Int.add_comm 0, ih, Monomial.foldl_assoc Int.add_assoc]
        rw [←Int.add_assoc, Int.add_comm (Monomial.eval ctx n), Int.add_assoc]

theorem eval_neg {p : Polynomial} : p.neg.eval ctx = -p.eval ctx := by
  simp only [eval, neg]
  induction p with
  | nil => simp
  | cons m p ih =>
    simp only [List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc,Int.neg_add, ←ih, List.map, Monomial.eval_neg]

theorem eval_add {p q : Polynomial} : (p.add q).eval ctx = p.eval ctx + q.eval ctx := by
  simp only [eval, add]
  induction p with
  | nil => simp [add.insert]
  | cons x ys ih =>
    simp only [List.foldr_cons, List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Int.add_assoc]
    rw [← ih, foldl_add_insert]

theorem eval_sub {p q : Polynomial} : (p.sub q).eval ctx = p.eval ctx - q.eval ctx := by
  simp only [sub, eval_neg, eval_add, Int.sub_eq_add_neg]

theorem eval_mulMonomial {p : Polynomial} : (p.mulMonomial m).eval ctx = m.eval ctx * p.eval ctx := by
  simp only [eval, mulMonomial, add]
  induction p with
  | nil => simp
  | cons n p ih =>
    simp only [List.foldl_cons, List.foldr_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, Int.mul_add, ←ih]
    simp [foldl_add_insert, Monomial.eval_mul]

theorem eval_cons {p : List Monomial} {ctx : Context} : eval ctx (m :: p) = m.eval ctx + eval ctx p := by
  simp only [eval, List.foldl_cons, Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc]

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
    rw [ih, @ih ((g k).add []), ← Int.add_assoc, eval_nil_add, eval_add, Int.add_comm _ (eval ctx n)]

theorem eval_foldl {g : Monomial → Polynomial} :
  eval ctx (List.foldl (fun acc m => ((g m).add (acc))) [] p) = List.foldl (fun acc m => (g m).eval ctx + acc) 0 p := by
  induction p with
  | nil => simp [eval]
  | cons n p ih =>
    simp only [List.foldl_cons, Int.add_comm, List.foldr] at *
    rw [Int.add_comm 0, Monomial.foldl_assoc Int.add_assoc, ←ih, eval_add_insert, eval_nil_add]

theorem eval_mul {p q : Polynomial} : (p.mul q).eval ctx = p.eval ctx * q.eval ctx := by
  simp only [mul]
  induction p with
  | nil => simp [eval]
  | cons n p ih =>
    simp only [List.foldl_cons, eval_cons, Int.add_mul, ← ih]
    rw [eval_foldl, eval_add_insert, ←eval_mulMonomial, eval_nil_add, eval_foldl]

end Polynomial

inductive Expr where
  | val (v : Int)
  | var (v : Nat)
  | neg (a : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
deriving Inhabited, Repr

namespace Expr

def toPoly : Expr → Polynomial
  | val v => if v = 0 then [] else [{ coeff := v, vars := [] }]
  | var v => [{ coeff := 1, vars := [v] }]
  | neg a => a.toPoly.neg
  | add a b => Polynomial.add a.toPoly b.toPoly
  | sub a b => Polynomial.sub a.toPoly b.toPoly
  | mul a b => Polynomial.mul a.toPoly b.toPoly

def eval (ctx : Context) : Expr → Int
  | val v => v
  | var v => ctx v
  | neg a => -a.eval ctx
  | add a b => a.eval ctx + b.eval ctx
  | sub a b => a.eval ctx - b.eval ctx
  | mul a b => a.eval ctx * b.eval ctx

theorem eval_toPoly {e : Expr} : e.eval ctx = e.toPoly.eval ctx := by
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

theorem eval_eq_from_toPoly_eq {e₁ e₂ : Expr} (h : e₁.toPoly = e₂.toPoly) : e₁.eval ctx = e₂.eval ctx := by
  rw [eval_toPoly, eval_toPoly, h]

end Smt.Reconstruct.Int.PolyNorm.Expr
