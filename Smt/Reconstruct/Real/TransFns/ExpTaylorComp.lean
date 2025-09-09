/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Mascarenhas
-/

/-
Definition of a computable version of the taylor polynomial of `exp` to be used in the reconstruction.
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Smt.Reconstruct.Real.TransFns.Utils

open Set Real

namespace Smt.Reconstruct.Real.TransFns

theorem iteratedDeriv_exp (n : Nat) : iteratedDeriv n exp = exp := by
    induction' n with n hn
    · simp
    · simp [iteratedDeriv_succ, hn]


lemma taylor_exp_eq (d : ℕ) (x : ℝ) :
    taylorWithinEval Real.exp d Set.univ 0 x =
      ∑ i ∈ Finset.range (d + 1), x^i / Nat.factorial i := by
  rw [taylor_within_apply]
  congr
  ext k
  rw [iteratedDerivWithin_eq_iteratedDeriv (f := Real.exp) (d := k) (s := Set.univ)]
  · rw [iteratedDeriv_exp]
    simp
    exact inv_mul_eq_div (↑k.factorial) (x ^ k)
  · exact contDiff_exp
  · exact uniqueDiffOn_univ
  · exact trivial

lemma ext_taylor_exp_eq (d : ℕ) :
    taylorWithinEval Real.exp d Set.univ 0 =
    fun x : Real => ∑ i ∈ Finset.range (d + 1), x ^ i / Nat.factorial i := by
  ext x
  exact taylor_exp_eq d x


def expTaylor' (i : Nat) (x : Rat) : Rat :=
  match i with
  | 0 => 1
  | i + 1 => expTaylor' i x + (x ^ (i + 1)) / (i + 1).factorial

/- def u : Rat := 1 -/
/- def d : Nat := 7 -/

/- #eval expTaylor' 7 0 -/


/- #eval expTaylor' d u / (1 - u ^ (d + 1) / (Nat.factorial (d + 1))) -/

@[simp]
noncomputable def expTaylor (i : Nat) (x : Real) : Real :=
  match i with
  | 0 => 1
  | i + 1 => expTaylor i x + (x ^ (i + 1)) / (i + 1).factorial

example : expTaylor 7 0 = 1 := by norm_num [Nat.factorial]

theorem expEmbedding (d : Nat) (x : Real) : taylorWithinEval Real.exp d Set.univ 0 x = expTaylor d x := by
  rw [taylor_exp_eq]
  induction d
  next => simp
  next d IH =>
    simp
    rw [<- IH, Finset.sum_range_succ (n := d + 1)]

@[simp]
noncomputable def sinTaylor (i : Nat) (x : Real) : Real :=
  match i with
  | 0 => 0
  | i + 1 =>
    let m := match (i + 1) % 4 with
    | 0 => 0
    | 1 => 1
    | 2 => 0
    | _ => -1
    m * x ^ (i + 1) / (i + 1).factorial + sinTaylor i x

def f : Nat → Real
| 0 => 0
| 1 => 1
| 2 => 0
| _ => -1

def sinTaylor' (i : Nat) (x : Rat) : Rat :=
  match i with
  | 0 => 0
  | i + 1 =>
    let m := f' ((i + 1) % 4)
    m * x ^ (i + 1) / (i + 1).factorial + sinTaylor' i x
where f' : Nat → Rat := fun n => match n with
| 0 => 0
| 1 => 1
| 2 => 0
| _ => -1

/- def u : Rat := (-61517) / 66204 -/
/- def d := 3 -/

/- def abovePos : Rat := sinTaylor' d u + (u ^ (d + 1)) / (d + 1).factorial -/
/- def belowNeg : Rat := sinTaylor' d u - (u ^ (d + 1)) / (d + 1).factorial -/

/- #eval belowNeg -/


lemma taylor_sin_eq (d : ℕ) (x : ℝ) :
    taylorWithinEval Real.sin d Set.univ 0 x =
      ∑ i ∈ Finset.range (d + 1), f (i % 4) * x^i / Nat.factorial i := by
  rw [taylor_within_apply]
  congr
  ext k
  obtain ⟨h1, _⟩ := iteratedDeriv_sin_cos k
  rw [iteratedDerivWithin_eq_iteratedDeriv (f := Real.sin) (d := k) (s := Set.univ)]
  · simp
    if hk0: k % 4 = 0 then
      rw [hk0] at h1
      simp at h1
      rw [hk0, f, h1]
      simp
    else if hk1 : k % 4 = 1 then
      rw [hk1] at h1
      simp at h1
      rw [hk1, f, h1]
      field_simp
    else if hk2 : k % 4 = 2 then
      rw [hk2] at h1
      simp at h1
      rw [hk2, f, h1]
      field_simp
    else
      have hk3 : k % 4 = 3 := by omega
      rw [hk3] at h1
      simp at h1
      rw [hk3, f, h1]
      · field_simp
      · decide
      · decide
      · decide
  · exact Real.contDiff_sin
  · exact uniqueDiffOn_univ
  · exact trivial

theorem sinEmbedding (d : Nat) (x : Real) : taylorWithinEval Real.sin d Set.univ 0 x = sinTaylor d x := by
  rw [taylor_sin_eq]
  induction d
  next => simp [f, sinTaylor]
  next d' IH =>
    simp [sinTaylor, f]
    rw [<- IH, Finset.sum_range_succ (n := d' + 1)]
    simp [f]
    rw [add_comm]

def sinTaylor'' (i : Nat) (x : Rat) : String :=
  match i with
  | 0 => "0"
  | i + 1 =>
    let m := match (i + 1) % 4 with
    | 0 => "0"
    | 1 => "1"
    | 2 => "0"
    | _ => "(-1)"
    let s := if m != "0" then
      m ++ " * " ++ (toString x) ++ " ^ " ++ (toString (i + 1)) ++ " / " ++ (toString (i + 1).factorial) ++ "! + "
      else ""
    s ++ sinTaylor'' i x


def test (d : Nat) (t l u : Rat) : Rat :=
  let p : ℚ → ℚ := fun x : Rat => sinTaylor' d x - (x ^ (d + 1)) / (d + 1).factorial
  ((p l - p u) / (l - u)) * (t - l) + p l

def test' (d : Nat) (t : Rat) : Rat :=
  let p : ℚ → ℚ := fun x : Rat => sinTaylor' d x - (x ^ (d + 1)) / (d + 1).factorial
  p t



/- noncomputable def x : Real := 1477484227914781812028990517570718421056690579467919648356975 / 2759701275951058854945193317695890595161897905032946982262784 -/

/- noncomputable def y : Real := -/
/-   Smt.Reconstruct.Real.TransFns.sinTaylor 3 (332386883638153 / 582321343247964) - -/
/-     12206060291110832203049620386386484601735185816612672485281 / -/
/-       2759701275951058854945193317695890595161897905032946982262784 -/

/- noncomputable example : x = y := by -/
  /- unfold x y sinTaylor Nat.factorial -/
  /- norm_num [x, y, Nat.factorial] -/
  /- qify -/
  /- native_decide -/


  /- ((p l - p u) / (l - u)) * (t - l) + p l -/

/- #eval sinTaylor' 3 5 -/

/- def l : Rat := ( (- 2954961095) / 8765939232) -/
/- def u : Rat := ( (- 19) / 200) -/
/- def t := (l + u) / 2 -/
/- #eval t -/

/- #eval test' 5 ((l + u) / 2) l u -/


/- def lb : Rat := 3.0 -/
/- def ub : Rat := (-1) / 10 -/
/- def d : Nat := 1 -/

/- #eval sinTaylor' d ub + ub ^ (d + 1) / (d + 1).factorial -/
/- #eval sinTaylor' d ub - ub ^ (d + 1) / (d + 1).factorial -/
/- #eval sinTaylor' d ub -/

/- #eval sinTaylor'' 3 ub -/

end Smt.Reconstruct.Real.TransFns
