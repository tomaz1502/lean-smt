/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Adrien Champion, Tomaz Gomes Mascarenhas
-/

import Batteries.Data.Rat.Basic
import Smt.Reconstruct.Int.Core

-- Source: Batteries/Data/Rat/Lemmas.lean

/-! # Additional lemmas about the Rational Numbers -/

namespace Rat

theorem ext : {p q : Rat} → p.num = q.num → p.den = q.den → p = q
  | ⟨_,_,_,_⟩, ⟨_,_,_,_⟩, rfl, rfl => rfl

@[simp] theorem mk_den_one {r : Int} :
    ⟨r, 1, Nat.one_ne_zero, (Nat.coprime_one_right _)⟩ = (r : Rat) := rfl

@[simp] theorem zero_num : (0 : Rat).num = 0 := rfl
@[simp] theorem zero_den : (0 : Rat).den = 1 := rfl
@[simp] theorem one_num : (1 : Rat).num = 1 := rfl
@[simp] theorem one_den : (1 : Rat).den = 1 := rfl

@[simp] theorem maybeNormalize_eq {num den g} (dvd_num dvd_den den_nz reduced) :
    maybeNormalize num den g dvd_num dvd_den den_nz reduced =
    { num := num.divExact g dvd_num, den := den / g, den_nz, reduced } := by
  unfold maybeNormalize; split
  · subst g; simp
  · rfl

theorem normalize_eq {num den} (den_nz) : normalize num den den_nz =
    { num := num / num.natAbs.gcd den
      den := den / num.natAbs.gcd den
      den_nz := normalize.den_nz den_nz rfl
      reduced := normalize.reduced den_nz rfl } := by
  simp only [normalize, maybeNormalize_eq, Int.divExact_eq_ediv]

@[simp] theorem normalize_zero (nz) : normalize 0 d nz = 0 := by
  simp [normalize, Int.zero_tdiv, Int.natAbs_zero, Nat.div_self (Nat.pos_of_ne_zero nz)]; rfl

theorem mk_eq_normalize (num den nz c) : ⟨num, den, nz, c⟩ = normalize num den nz := by
  simp [normalize_eq, c.gcd_eq_one]

theorem normalize_self (r : Rat) : normalize r.num r.den r.den_nz = r := (mk_eq_normalize ..).symm

theorem normalize_mul_left {a : Nat} (d0 : d ≠ 0) (a0 : a ≠ 0) :
    normalize (↑a * n) (a * d) (Nat.mul_ne_zero a0 d0) = normalize n d d0 := by
  simp [normalize_eq, mk'.injEq, Int.natAbs_mul, Nat.gcd_mul_left,
    Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero a0), Int.natCast_mul,
    Int.mul_ediv_mul_of_pos _ _ (Int.ofNat_pos.2 <| Nat.pos_of_ne_zero a0)]

theorem normalize_mul_right {a : Nat} (d0 : d ≠ 0) (a0 : a ≠ 0) :
    normalize (n * a) (d * a) (Nat.mul_ne_zero d0 a0) = normalize n d d0 := by
  rw [← normalize_mul_left (d0 := d0) a0]
  congr 1
  · apply Int.mul_comm
  · apply Nat.mul_comm

theorem normalize_eq_iff (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    normalize n₁ d₁ z₁ = normalize n₂ d₂ z₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  constructor <;> intro h
  · simp only [normalize_eq, mk'.injEq] at h
    have hn₁ := Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left n₁.natAbs d₁
    have hn₂ := Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left n₂.natAbs d₂
    have hd₁ := Int.ofNat_dvd.2 <| Nat.gcd_dvd_right n₁.natAbs d₁
    have hd₂ := Int.ofNat_dvd.2 <| Nat.gcd_dvd_right n₂.natAbs d₂
    rw [← Int.ediv_mul_cancel (Int.dvd_trans hd₂ (Int.dvd_mul_left ..)),
      Int.mul_ediv_assoc _ hd₂, ← Int.natCast_ediv, ← h.2, Int.natCast_ediv,
      ← Int.mul_ediv_assoc _ hd₁, Int.mul_ediv_assoc' _ hn₁,
      Int.mul_right_comm, h.1, Int.ediv_mul_cancel hn₂]
  · rw [← normalize_mul_right _ z₂, ← normalize_mul_left z₂ z₁, Int.mul_comm d₁, h]

theorem maybeNormalize_eq_normalize {num : Int} {den g : Nat} (dvd_num dvd_den den_nz reduced)
    (hn : ↑g ∣ num) (hd : g ∣ den) :
    maybeNormalize num den g dvd_num dvd_den den_nz reduced =
      normalize num den (mt (by simp [·]) den_nz) := by
  simp only [maybeNormalize_eq, mk_eq_normalize, Int.divExact_eq_ediv]
  have : g ≠ 0 := mt (by simp [·]) den_nz
  rw [← normalize_mul_right _ this, Int.ediv_mul_cancel hn]
  congr 1; exact Nat.div_mul_cancel hd

@[simp] theorem normalize_eq_zero (d0 : d ≠ 0) : normalize n d d0 = 0 ↔ n = 0 := by
  have' := normalize_eq_iff d0 Nat.one_ne_zero
  rw [normalize_zero (d := 1)] at this; rw [this]; simp

theorem normalize_num_den' (num den nz) : ∃ d : Nat, d ≠ 0 ∧
    num = (normalize num den nz).num * d ∧ den = (normalize num den nz).den * d := by
  refine ⟨num.natAbs.gcd den, Nat.gcd_ne_zero_right nz, ?_⟩
  simp [normalize_eq, Int.ediv_mul_cancel (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..),
    Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]

theorem normalize_num_den (h : normalize n d z = ⟨n', d', z', c⟩) :
    ∃ m : Nat, m ≠ 0 ∧ n = n' * m ∧ d = d' * m := by
  have := normalize_num_den' n d z; rwa [h] at this

theorem normalize_eq_mkRat {num den} (den_nz) : normalize num den den_nz = mkRat num den := by
  simp [mkRat, den_nz]

theorem mkRat_num_den (z : d ≠ 0) (h : mkRat n d = ⟨n', d', z', c⟩) :
    ∃ m : Nat, m ≠ 0 ∧ n = n' * m ∧ d = d' * m :=
  normalize_num_den ((normalize_eq_mkRat z).symm ▸ h)

theorem mkRat_def (n d) : mkRat n d = if d0 : d = 0 then 0 else normalize n d d0 := rfl

theorem mkRat_self (a : Rat) : mkRat a.num a.den = a := by
  rw [← normalize_eq_mkRat a.den_nz, normalize_self]

theorem mk_eq_mkRat (num den nz c) : ⟨num, den, nz, c⟩ = mkRat num den := by
  simp [mk_eq_normalize, normalize_eq_mkRat]

@[simp] theorem zero_mkRat (n) : mkRat 0 n = 0 := by simp [mkRat_def]

@[simp] theorem mkRat_zero (n) : mkRat n 0 = 0 := by simp [mkRat_def]

theorem mkRat_eq_zero (d0 : d ≠ 0) : mkRat n d = 0 ↔ n = 0 := by simp [mkRat_def, d0]

theorem mkRat_ne_zero (d0 : d ≠ 0) : mkRat n d ≠ 0 ↔ n ≠ 0 := not_congr (mkRat_eq_zero d0)

theorem mkRat_mul_left {a : Nat} (a0 : a ≠ 0) : mkRat (↑a * n) (a * d) = mkRat n d := by
  if d0 : d = 0 then simp [d0] else
  rw [← normalize_eq_mkRat d0, ← normalize_mul_left d0 a0, normalize_eq_mkRat]

theorem mkRat_mul_right {a : Nat} (a0 : a ≠ 0) : mkRat (n * a) (d * a) = mkRat n d := by
  rw [← mkRat_mul_left (d := d) a0]
  congr 1
  · apply Int.mul_comm
  · apply Nat.mul_comm

theorem mkRat_eq_iff (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    mkRat n₁ d₁ = mkRat n₂ d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  rw [← normalize_eq_mkRat z₁, ← normalize_eq_mkRat z₂, normalize_eq_iff]

@[simp] theorem divInt_ofNat (num den) : num /. (den : Nat) = mkRat num den := by
  simp [divInt, normalize_eq_mkRat]

theorem mk_eq_divInt (num den nz c) : ⟨num, den, nz, c⟩ = num /. (den : Nat) := by
  simp [mk_eq_mkRat]

theorem divInt_self (a : Rat) : a.num /. a.den = a := by rw [divInt_ofNat, mkRat_self]

@[simp] theorem zero_divInt (n) : 0 /. n = 0 := by cases n <;> simp [divInt]

@[simp] theorem divInt_zero (n) : n /. 0 = 0 := mkRat_zero n

theorem neg_divInt_neg (num den) : -num /. -den = num /. den := by
  match den with
  | Nat.succ n =>
    simp only [divInt, Int.neg_ofNat_succ]
    simp [normalize_eq_mkRat, Int.neg_neg]
  | 0 => rfl
  | Int.negSucc n =>
    simp only [divInt, Int.neg_negSucc]
    simp [normalize_eq_mkRat, Int.neg_neg]

theorem divInt_neg' (num den) : num /. -den = -num /. den := by rw [← neg_divInt_neg, Int.neg_neg]

theorem divInt_eq_iff (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    n₁ /. d₁ = n₂ /. d₂ ↔ n₁ * d₂ = n₂ * d₁ := by
  rcases Int.eq_nat_or_neg d₁ with ⟨_, rfl | rfl⟩ <;>
  rcases Int.eq_nat_or_neg d₂ with ⟨_, rfl | rfl⟩ <;>
  simp_all [divInt_neg', Int.ofNat_eq_zero, Int.neg_eq_zero,
    mkRat_eq_iff, Int.neg_mul, Int.mul_neg, Int.eq_neg_comm, eq_comm]

theorem divInt_mul_left {a : Int} (a0 : a ≠ 0) : (a * n) /. (a * d) = n /. d := by
  if d0 : d = 0 then simp [d0] else
  simp [divInt_eq_iff (Int.mul_ne_zero a0 d0) d0, Int.mul_assoc, Int.mul_left_comm]

theorem divInt_mul_right {a : Int} (a0 : a ≠ 0) : (n * a) /. (d * a) = n /. d := by
  simp [← divInt_mul_left (d := d) a0, Int.mul_comm]

theorem divInt_num_den (z : d ≠ 0) (h : n /. d = ⟨n', d', z', c⟩) :
    ∃ m, m ≠ 0 ∧ n = n' * m ∧ d = d' * m := by
  rcases Int.eq_nat_or_neg d with ⟨_, rfl | rfl⟩ <;>
    simp_all [divInt_neg', Int.ofNat_eq_zero, Int.neg_eq_zero]
  · have ⟨m, h₁, h₂⟩ := mkRat_num_den z h; exists m
    simp [Int.ofNat_eq_zero, Int.natCast_mul, h₁, h₂]
  · have ⟨m, h₁, h₂⟩ := mkRat_num_den z h; exists -m
    rw [← Int.neg_inj, Int.neg_neg] at h₂
    simp [Int.ofNat_eq_zero, Int.natCast_mul, h₁, h₂, Int.mul_neg, Int.neg_eq_zero]

@[simp] theorem ofInt_ofNat : ofInt (OfNat.ofNat n) = OfNat.ofNat n := rfl

@[simp] theorem ofInt_num : (ofInt n : Rat).num = n := rfl
@[simp] theorem ofInt_den : (ofInt n : Rat).den = 1 := rfl

@[simp] theorem ofNat_num : (OfNat.ofNat n : Rat).num = OfNat.ofNat n := rfl
@[simp] theorem ofNat_den : (OfNat.ofNat n : Rat).den = 1 := rfl

theorem add_def (a b : Rat) :
    a + b = normalize (a.num * b.den + b.num * a.den) (a.den * b.den)
      (Nat.mul_ne_zero a.den_nz b.den_nz) := by
  show Rat.add .. = _; delta Rat.add; dsimp only; split
  · exact (normalize_self _).symm
  · have : a.den.gcd b.den ≠ 0 := Nat.gcd_ne_zero_left a.den_nz
    rw [maybeNormalize_eq_normalize _ _ _ _
        (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..)
        (Nat.dvd_trans (Nat.gcd_dvd_right ..) <|
         Nat.dvd_trans (Nat.gcd_dvd_right ..) (Nat.dvd_mul_left ..)),
      ← normalize_mul_right _ this]; congr 1
    · simp only [Int.add_mul, Int.mul_assoc, Int.ofNat_mul_ofNat,
        Nat.div_mul_cancel (Nat.gcd_dvd_left ..), Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]
    · rw [Nat.mul_right_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left ..)]

theorem add_def' (a b : Rat) : a + b = mkRat (a.num * b.den + b.num * a.den) (a.den * b.den) := by
  rw [add_def, normalize_eq_mkRat]

theorem normalize_add_normalize (n₁ n₂) {d₁ d₂} (z₁ z₂) :
    normalize n₁ d₁ z₁ + normalize n₂ d₂ z₂ =
    normalize (n₁ * d₂ + n₂ * d₁) (d₁ * d₂) (Nat.mul_ne_zero z₁ z₂) := by
  cases e₁ : normalize n₁ d₁ z₁; rcases normalize_num_den e₁ with ⟨g₁, zg₁, rfl, rfl⟩
  cases e₂ : normalize n₂ d₂ z₂; rcases normalize_num_den e₂ with ⟨g₂, zg₂, rfl, rfl⟩
  simp only [add_def]; rw [← normalize_mul_right _ (Nat.mul_ne_zero zg₁ zg₂)]; congr 1
  · rw [Int.add_mul]; simp [Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm, Int.mul_comm]
  · simp [Nat.mul_left_comm, Nat.mul_comm]

theorem mkRat_add_mkRat (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    mkRat n₁ d₁ + mkRat n₂ d₂ = mkRat (n₁ * d₂ + n₂ * d₁) (d₁ * d₂) := by
  rw [← normalize_eq_mkRat z₁, ← normalize_eq_mkRat z₂, normalize_add_normalize, normalize_eq_mkRat]

theorem divInt_add_divInt (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    n₁ /. d₁ + n₂ /. d₂ = (n₁ * d₂ + n₂ * d₁) /. (d₁ * d₂) := by
  rcases Int.eq_nat_or_neg d₁ with ⟨_, rfl | rfl⟩ <;>
  rcases Int.eq_nat_or_neg d₂ with ⟨_, rfl | rfl⟩ <;>
  simp_all [← Int.natCast_mul, Int.ofNat_eq_zero, Int.neg_eq_zero, divInt_neg', Int.mul_neg,
    Int.neg_add, Int.neg_mul, mkRat_add_mkRat]

@[simp] theorem neg_num (a : Rat) : (-a).num = -a.num := rfl
@[simp] theorem neg_den (a : Rat) : (-a).den = a.den := rfl

theorem neg_normalize (n d z) : -normalize n d z = normalize (-n) d z := by
  simp only [normalize, maybeNormalize_eq, Int.divExact_eq_tdiv, Int.natAbs_neg, Int.neg_tdiv]
  rfl

theorem neg_mkRat (n d) : -mkRat n d = mkRat (-n) d := by
  if z : d = 0 then simp [z]; rfl else simp [← normalize_eq_mkRat z, neg_normalize]

theorem neg_divInt (n d) : -(n /. d) = -n /. d := by
  rcases Int.eq_nat_or_neg d with ⟨_, rfl | rfl⟩ <;> simp [divInt_neg', neg_mkRat]

theorem sub_def (a b : Rat) :
    a - b = normalize (a.num * b.den - b.num * a.den) (a.den * b.den)
      (Nat.mul_ne_zero a.den_nz b.den_nz) := by
  show Rat.sub .. = _; delta Rat.sub; dsimp only; split
  · exact (normalize_self _).symm
  · have : a.den.gcd b.den ≠ 0 := Nat.gcd_ne_zero_left a.den_nz
    rw [maybeNormalize_eq_normalize _ _ _ _
        (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..)
        (Nat.dvd_trans (Nat.gcd_dvd_right ..) <|
         Nat.dvd_trans (Nat.gcd_dvd_right ..) (Nat.dvd_mul_left ..)),
      ← normalize_mul_right _ this]; congr 1
    · simp only [Int.sub_mul, Int.mul_assoc, ← Int.natCast_mul,
        Nat.div_mul_cancel (Nat.gcd_dvd_left ..), Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]
    · rw [Nat.mul_right_comm, Nat.div_mul_cancel (Nat.gcd_dvd_left ..)]

theorem sub_def' (a b : Rat) : a - b = mkRat (a.num * b.den - b.num * a.den) (a.den * b.den) := by
  rw [sub_def, normalize_eq_mkRat]

protected theorem sub_eq_add_neg (a b : Rat) : a - b = a + -b := by
  simp [add_def, sub_def, Int.neg_mul, Int.sub_eq_add_neg]

theorem divInt_sub_divInt (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    n₁ /. d₁ - n₂ /. d₂ = (n₁ * d₂ - n₂ * d₁) /. (d₁ * d₂) := by
  simp only [Rat.sub_eq_add_neg, neg_divInt,
    divInt_add_divInt _ _ z₁ z₂, Int.neg_mul, Int.sub_eq_add_neg]

theorem mul_def (a b : Rat) :
    a * b = normalize (a.num * b.num) (a.den * b.den) (Nat.mul_ne_zero a.den_nz b.den_nz) := by
  show Rat.mul .. = _; delta Rat.mul; dsimp only
  have H1 : a.num.natAbs.gcd b.den ≠ 0 := Nat.gcd_ne_zero_right b.den_nz
  have H2 : b.num.natAbs.gcd a.den ≠ 0 := Nat.gcd_ne_zero_right a.den_nz
  simp only [Int.divExact_eq_tdiv, Nat.divExact_eq_div]
  rw [mk_eq_normalize, ← normalize_mul_right _ (Nat.mul_ne_zero H1 H2)]; congr 1
  · rw [Int.natCast_mul, ← Int.mul_assoc, Int.mul_right_comm (Int.tdiv ..),
      Int.tdiv_mul_cancel (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..), Int.mul_assoc,
      Int.tdiv_mul_cancel (Int.ofNat_dvd_left.2 <| Nat.gcd_dvd_left ..)]
  · rw [← Nat.mul_assoc, Nat.mul_right_comm, Nat.mul_right_comm (_/_),
      Nat.div_mul_cancel (Nat.gcd_dvd_right ..), Nat.mul_assoc,
      Nat.div_mul_cancel (Nat.gcd_dvd_right ..)]

protected theorem mul_comm (a b : Rat) : a * b = b * a := by
  simp [mul_def, normalize_eq_mkRat, Int.mul_comm, Nat.mul_comm]

@[simp] protected theorem zero_mul (a : Rat) : 0 * a = 0 := by simp [mul_def]
@[simp] protected theorem mul_zero (a : Rat) : a * 0 = 0 := by simp [mul_def]
@[simp] protected theorem one_mul (a : Rat) : 1 * a = a := by simp [mul_def, normalize_self]
@[simp] protected theorem mul_one (a : Rat) : a * 1 = a := by simp [mul_def, normalize_self]

theorem normalize_mul_normalize (n₁ n₂) {d₁ d₂} (z₁ z₂) :
    normalize n₁ d₁ z₁ * normalize n₂ d₂ z₂ =
    normalize (n₁ * n₂) (d₁ * d₂) (Nat.mul_ne_zero z₁ z₂) := by
  cases e₁ : normalize n₁ d₁ z₁; rcases normalize_num_den e₁ with ⟨g₁, zg₁, rfl, rfl⟩
  cases e₂ : normalize n₂ d₂ z₂; rcases normalize_num_den e₂ with ⟨g₂, zg₂, rfl, rfl⟩
  simp only [mul_def]; rw [← normalize_mul_right _ (Nat.mul_ne_zero zg₁ zg₂)]; congr 1
  · simp [Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm]
  · simp [Nat.mul_left_comm, Nat.mul_comm]

theorem mkRat_mul_mkRat (n₁ n₂ : Int) (d₁ d₂) :
    mkRat n₁ d₁ * mkRat n₂ d₂ = mkRat (n₁ * n₂) (d₁ * d₂) := by
  if z₁ : d₁ = 0 then simp [z₁] else if z₂ : d₂ = 0 then simp [z₂] else
  rw [← normalize_eq_mkRat z₁, ← normalize_eq_mkRat z₂, normalize_mul_normalize, normalize_eq_mkRat]

theorem divInt_mul_divInt (n₁ n₂ : Int) {d₁ d₂} (z₁ : d₁ ≠ 0) (z₂ : d₂ ≠ 0) :
    (n₁ /. d₁) * (n₂ /. d₂) = (n₁ * n₂) /. (d₁ * d₂) := by
  rcases Int.eq_nat_or_neg d₁ with ⟨_, rfl | rfl⟩ <;>
  rcases Int.eq_nat_or_neg d₂ with ⟨_, rfl | rfl⟩ <;>
  simp_all [← Int.natCast_mul, divInt_neg', Int.mul_neg, Int.neg_mul, mkRat_mul_mkRat]

theorem inv_def (a : Rat) : a.inv = a.den /. a.num := by
  unfold Rat.inv; split
  · next h => rw [mk_eq_divInt, ← Int.natAbs_neg,
      Int.natAbs_of_nonneg (Int.le_of_lt <| Int.neg_pos_of_neg h), neg_divInt_neg]
  split
  · next h => rw [mk_eq_divInt, Int.natAbs_of_nonneg (Int.le_of_lt h)]
  · next h₁ h₂ =>
    apply (divInt_self _).symm.trans
    simp [Int.le_antisymm (Int.not_lt.1 h₂) (Int.not_lt.1 h₁)]

@[simp] protected theorem inv_zero : (0 : Rat).inv = 0 := by unfold Rat.inv; rfl

@[simp] theorem inv_divInt (n d : Int) : (n /. d).inv = d /. n := by
  if z : d = 0 then simp [z] else
  cases e : n /. d; rcases divInt_num_den z e with ⟨g, zg, rfl, rfl⟩
  simp [inv_def, divInt_mul_right zg]

theorem div_def (a b : Rat) : a / b = a * b.inv := rfl

theorem ofScientific_true_def : Rat.ofScientific m true e = mkRat m (10 ^ e) := by
  unfold Rat.ofScientific; rw [normalize_eq_mkRat]; rfl

theorem ofScientific_false_def : Rat.ofScientific m false e = (m * 10 ^ e : Nat) := by
  unfold Rat.ofScientific; rfl

theorem ofScientific_def : Rat.ofScientific m s e =
    if s then mkRat m (10 ^ e) else (m * 10 ^ e : Nat) := by
  cases s; exact ofScientific_false_def; exact ofScientific_true_def

/-- `Rat.ofScientific` applied to numeric literals is the same as a scientific literal. -/
@[simp]
theorem ofScientific_ofNat_ofNat :
    Rat.ofScientific (no_index (OfNat.ofNat m)) s (no_index (OfNat.ofNat e))
      = OfScientific.ofScientific m s e := rfl

@[simp] theorem intCast_den (a : Int) : (a : Rat).den = 1 := rfl

@[simp] theorem intCast_num (a : Int) : (a : Rat).num = a := rfl

/-!
The following lemmas are later subsumed by e.g. `Int.cast_add` and `Int.cast_mul` in Mathlib
but it is convenient to have these earlier, for users who only need `Int` and `Rat`.
-/

@[simp, norm_cast] theorem intCast_inj {a b : Int} : (a : Rat) = (b : Rat) ↔ a = b := by
  constructor
  · rintro ⟨⟩; rfl
  · simp_all

theorem intCast_zero : ((0 : Int) : Rat) = (0 : Rat) := rfl

theorem intCast_one : ((1 : Int) : Rat) = (1 : Rat) := rfl

@[simp, norm_cast] theorem intCast_add (a b : Int) :
    ((a + b : Int) : Rat) = (a : Rat) + (b : Rat) := by
  rw [add_def]
  simp [normalize_eq]

@[simp, norm_cast] theorem intCast_neg (a : Int) : ((-a : Int) : Rat) = -(a : Rat) := rfl

@[simp, norm_cast] theorem intCast_sub (a b : Int) :
    ((a - b : Int) : Rat) = (a : Rat) - (b : Rat) := by
  rw [sub_def]
  simp [normalize_eq]

@[simp, norm_cast] theorem intCast_mul (a b : Int) :
    ((a * b : Int) : Rat) = (a : Rat) * (b : Rat) := by
  rw [mul_def]
  simp [normalize_eq]

variable (x y a b c q : Rat)

protected def abs (x : Rat) := if x < 0 then -x else x

protected def pow (m : Rat) : Nat → Rat
  | 0 => 1
  | n + 1 => Rat.pow m n * m

instance : NatPow Rat where
  pow := Rat.pow

def ceil' (r : Rat) := -((-r).floor)

theorem num_divInt_den (q : Rat) : q.num /. q.den = q :=
  divInt_self _

theorem mk'_eq_divInt {n d h c} : (⟨n, d, h, c⟩ : Rat) = n /. d :=
  (num_divInt_den _).symm

theorem divInt_num (q : Rat) : (q.num /. q.den).num = q.num := by
  simp [mkRat, q.den_nz, normalize, Rat.reduced]

theorem divInt_num'
  {n : Int} {d : Nat}
  (nz_d : d ≠ 0 := by omega)
  (reduced : n.natAbs.Coprime d := by assumption)
: (n /. d).num = n := by
  simp [mkRat, nz_d, normalize, reduced]

theorem divInt_den (q : Rat) : (q.num /. q.den).den = q.den := by
  simp [mkRat, q.den_nz, normalize, Rat.reduced]

theorem divInt_den'
  {n : Int} {d : Nat}
  (nz_d : d ≠ 0 := by omega)
  (reduced : n.natAbs.Coprime d := by assumption)
: (n /. d).den = d := by
  simp [mkRat, nz_d, normalize, reduced]

@[elab_as_elim]
def numDenCasesOn.{u} {C : Rat → Sort u}
: ∀ (a : Rat) (_ : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (n /. d)), C a
| ⟨n, d, h, c⟩, H => by rw [mk'_eq_divInt]; exact H n d (Nat.pos_of_ne_zero h) c

@[elab_as_elim]
def numDenCasesOn'.{u} {C : Rat → Sort u} (a : Rat)
  (H : ∀ (n : Int) (d : Nat), d ≠ 0 → C (n /. d))
: C a :=
  numDenCasesOn a fun n d h _ => H n d (Nat.pos_iff_ne_zero.mp h)

@[elab_as_elim]
def numDenCasesOn''.{u} {C : Rat → Sort u} (a : Rat)
  (H : ∀ (n : Int) (d : Nat) (nz red), C (mk' n d nz red))
: C a :=
  numDenCasesOn a fun n d h h' ↦ by
    let h_pos := Nat.pos_iff_ne_zero.mp h
    rw [← mk_eq_divInt _ _ h_pos h']
    exact H n d h_pos _

theorem normalize_eq_mk'
  (n : Int) (d : Nat) (h : d ≠ 0) (c : Nat.gcd (Int.natAbs n) d = 1)
: normalize n d h = mk' n d h c :=
  (mk_eq_normalize ..).symm

protected theorem normalize_den_ne_zero
: ∀ {d : Int} {n : Nat}, (h : n ≠ 0) → (normalize d n h).den ≠ 0 := by
  intro d n nz
  simp only [Rat.normalize_eq, ne_eq]
  intro h
  apply nz
  rw [← Nat.zero_mul (d.natAbs.gcd n)]
  apply Nat.div_eq_iff_eq_mul_left _ _ |>.mp
  · assumption
  · exact Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero nz)
  · exact Nat.gcd_dvd_right _ _

protected theorem eq_mkRat : ∀ a : Rat, a = mkRat a.num a.den := fun a => by
  simp [Rat.mkRat_def, a.den_nz, Rat.normalize_eq, a.reduced]

@[simp]
theorem mk'_zero (d) (h : d ≠ 0) (w) : mk' 0 d h w = 0 := by
  congr
  apply Nat.coprime_zero_left d |>.mp w

theorem eq_iff_mul_eq_mul {p q : Rat} : p = q ↔ p.num * q.den = q.num * p.den := by
  conv =>
    lhs
    rw [← num_divInt_den p, ← num_divInt_den q]
  apply Rat.divInt_eq_iff <;>
    · rw [← Int.natCast_zero, Ne, Int.ofNat_inj]
      apply den_nz

protected theorem not_le {q q' : Rat} : ¬q ≤ q' ↔ q' < q := by
  exact (Bool.not_eq_false _).to_iff

protected theorem not_lt {q q' : Rat} : ¬q < q' ↔ q' ≤ q := by
  rw [not_congr (Rat.not_le (q := q') (q' := q)) |>.symm]
  simp only [Decidable.not_not]

protected theorem lt_iff_blt {x y : Rat} : x < y ↔ x.blt y := by
  simp only [LT.lt]

protected theorem le_iff_blt {x y : Rat} : x ≤ y ↔ ¬ y.blt x := by
  simp [LE.le]

protected theorem lt_asymm {x y : Rat} : x < y → ¬ y < x := by
  simp [Rat.lt_iff_blt, Rat.blt]
  intro h
  cases h with
  | inl h =>
    simp only [h, implies_true, Int.not_lt_of_lt_rev h.1, or_false, if_false_left, not_and,
      Int.not_lt, true_and]
    intro nz_ynum ynum_neg
    have z_ynum : y.num = 0 := Int.le_antisymm ynum_neg h.right
    contradiction
  | inr h =>
    split at h
    case isTrue xnum_0 =>
      simp only [Int.not_lt_of_lt_rev h, xnum_0, Int.lt_irrefl, imp_self, or_false, Int.zero_mul,
        if_false_left, not_and, Int.not_lt, true_and]
      intro nz_ynum ynum_neg
      have z_ynum : y.num = 0 := Int.le_antisymm ynum_neg (Int.le_of_lt h)
      contradiction
    case inr xnum_ne_0 =>
      let ⟨h, h'⟩ := h
      simp only [Int.not_lt_of_lt_rev h', and_false, if_false_right, not_and, Int.not_lt]
      cases h
      case inl h =>
        simp only [h, implies_true, and_true]
        intro _
        apply Int.lt_of_le_of_ne h xnum_ne_0
      case inr h =>
        constructor <;> intros <;> simp_all [Int.lt_asymm]

protected theorem add_comm : a + b = b + a := by
  simp [add_def, Int.add_comm, Int.mul_comm, Nat.mul_comm]

@[simp]
protected theorem add_zero : ∀ a : Rat, a + 0 = a
| ⟨num, den, _h, _h'⟩ => by
  simp [Rat.add_def]
  simp only [Rat.normalize_eq_mkRat, Rat.mk_eq_normalize]

@[simp]
protected theorem zero_add : 0 + a = a :=
  Rat.add_comm a 0 ▸ Rat.add_zero a

protected theorem add_assoc : a + b + c = a + (b + c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
  numDenCasesOn' b fun n₂ d₂ h₂ =>
  numDenCasesOn' c fun n₃ d₃ h₃ => by
    simp only [
      ne_eq, Int.natCast_eq_zero, h₁, not_false_eq_true, h₂,
      Rat.divInt_add_divInt, Int.mul_eq_zero, or_self, h₃
    ]
    rw [Int.mul_assoc, Int.add_mul, Int.add_mul, Int.mul_assoc, Int.add_assoc]
    congr 2
    ac_rfl

protected theorem mul_eq_zero_iff : a * b = 0 ↔ a = 0 ∨ b = 0 := by
  constructor
  · simp only [Rat.mul_def, Rat.normalize_eq_zero]
    intro h
    cases Int.mul_eq_zero.mp h
    · apply Or.inl
      rw [Rat.eq_mkRat a, Rat.mkRat_eq_zero]
      assumption
      exact a.den_nz
    · apply Or.inr
      rw [Rat.eq_mkRat b, Rat.mkRat_eq_zero]
      assumption
      exact b.den_nz
  · intro
    | .inl h => simp only [h, Rat.zero_mul]
    | .inr h => simp only [h, Rat.mul_zero]

protected theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 := by
  simp only [not_congr (Rat.mul_eq_zero_iff a b), not_or, ne_eq]

@[simp]
theorem neg_neg : - -q = q := by
  rw [← Rat.mkRat_self q]
  simp [Rat.neg_mkRat]

@[simp]
theorem num_eq_zero : q.num = 0 ↔ q = 0 := by
  induction q
  constructor
  · rintro rfl
    exact mk'_zero _ _ _
  · exact congrArg num

theorem num_ne_zero : q.num ≠ 0 ↔ q ≠ 0 := not_congr (num_eq_zero q)

@[simp]
theorem num_nonneg : 0 ≤ q.num ↔ 0 ≤ q := by
  simp [Int.le_iff_lt_or_eq, instLE, Rat.blt, Int.not_lt]
  omega

theorem nonneg_iff_sub_nonpos : 0 ≤ q ↔ -q ≤ 0 := by
  rw [← num_nonneg]
  conv => rhs; simp [LE.le, Rat.blt]
  rfl

theorem nonneg_sub_iff_nonpos : 0 ≤ -q ↔ q ≤ 0 := by
  simp [nonneg_iff_sub_nonpos, Rat.neg_neg]

@[simp]
theorem num_nonpos : q.num ≤ 0 ↔ q ≤ 0 := by
  conv => lhs ; rw [← Int.neg_nonneg]
  simp only [Rat.neg_num q ▸ @num_nonneg (-q)]
  conv => rhs ; rw [← nonneg_sub_iff_nonpos]

theorem not_nonpos : ¬ q ≤ 0 ↔ 0 < q := by
  simp [Rat.lt_iff_blt, Rat.blt]
  rw [← num_nonpos]
  exact Int.not_le

@[simp]
theorem num_pos : 0 < q.num ↔ 0 < q := by
  let tmp := not_congr (num_nonpos (q := q))
  rw [Int.not_le] at tmp
  simp [tmp, Rat.not_nonpos]

theorem pos_iff_neg_nonpos : 0 < q ↔ -q < 0 := by
  rw [← num_pos]
  conv => rhs ; simp [Rat.lt_iff_blt] ; unfold Rat.blt ; simp
  constructor <;> intro h
  · apply Or.inl
    exact (num_pos q).mp h
  · let h : 0 < q := by
      cases h
      case inl h => exact h
      case inr h => exact h.2.2
    apply (num_pos q).mpr h

@[simp]
theorem num_neg : q.num < 0 ↔ q < 0 := by
  let tmp := @num_pos (-q)
  simp [Rat.neg_num q, Int.lt_neg_of_lt_neg] at tmp
  rw [tmp]
  apply Rat.neg_neg q ▸ Rat.pos_iff_neg_nonpos (q := -q)

@[simp]
theorem num_neg_eq_neg_num (q : Rat) : (-q).num = -q.num :=
  rfl

@[simp]
protected theorem le_refl : x ≤ x := by
  simp [Rat.le_iff_blt, Rat.blt]
  if h : x = 0 then
    simp [h]
    rw [← Rat.num_neg, Rat.zero_num]
    exact Int.lt_irrefl 0
  else
    simp [h]
    rw [← Rat.num_neg, ← Rat.num_pos]
    omega

protected theorem lt_irrefl : ¬ x < x := by
  simp [Rat.not_lt, Rat.le_refl]

protected theorem le_of_lt : x < y → x ≤ y := by
  intro h_lt
  apply Decidable.byContradiction
  intro h
  let _ := Rat.not_le.mp h
  let _ := Rat.lt_asymm h_lt
  contradiction

protected theorem ne_of_lt : x < y → x ≠ y := by
  intro h_lt h_eq
  exact Rat.lt_irrefl x (h_eq ▸ h_lt)

protected theorem nonneg_total : 0 ≤ x ∨ 0 ≤ -x := by
  rw [← num_nonneg (q := -x), ← num_nonneg (q := x)]
  rw [Rat.neg_num, Int.neg_nonneg]
  exact Int.le_total _ _

protected theorem nonneg_antisymm : 0 ≤ x → 0 ≤ -x → x = 0 := by
  rw [← Rat.num_eq_zero, ← Rat.num_nonneg, ← Rat.num_nonneg, Rat.num_neg_eq_neg_num]
  omega

protected theorem neg_sub : -(x - y) = y - x := by
  cases x with | mk' nx dx _ _ =>
  cases y with | mk' ny dy _ _ =>
  simp only [Neg.neg, Rat.sub_eq_add_neg]
  simp only [Rat.neg, Int.neg_mul, add_def, normalize_eq, mk'.injEq]
  rw [Nat.mul_comm dx dy]
  constructor
  · rw [← Int.neg_ediv_of_dvd]
    rw [← Int.sub_eq_add_neg, Int.neg_sub]
    rw [← Int.sub_eq_add_neg]
    rw [← Int.natAbs_neg, Int.neg_sub]
    · conv => lhs ; arg 1 ; arg 2 ; rw [← Int.natAbs_natCast (dy * dx)]
      exact Int.natAbs_gcd_dvd' (nx * ↑dy + -(ny * ↑dx)) (↑(dy * dx) : Int).natAbs
  · rw [← Int.sub_eq_add_neg]
    rw [← Int.sub_eq_add_neg]
    rw [← Int.natAbs_neg, Int.neg_sub]

@[simp]
protected theorem sub_self : x - x = 0 :=
  numDenCasesOn' x fun nx dx h_dx => by
    rw [Rat.divInt_sub_divInt _ _ (Int.natCast_ne_zero.mpr h_dx) (Int.natCast_ne_zero.mpr h_dx)]
    simp

protected theorem add_neg_self : x + -x = 0 :=
  Rat.sub_eq_add_neg x x ▸ Rat.sub_self x

protected theorem eq_neg_of_add_eq_zero_left : x + y = 0 → x = - y :=
  numDenCasesOn'' x fun nx dx h_dx h_dx_red =>
  numDenCasesOn'' y fun ny dy h_dy h_dy_red => by
    simp only [Rat.neg_divInt, Rat.add_def, Neg.neg]
    simp only [Rat.neg, normalize_eq_zero]
    simp only [eq_iff_mul_eq_mul, ← Int.neg_mul_eq_neg_mul]
    intro h
    apply Int.eq_neg_of_eq_neg
    exact Int.neg_eq_of_add_eq_zero h |>.symm

protected theorem le_iff_sub_nonneg (x y : Rat) : x ≤ y ↔ 0 ≤ y - x :=
  numDenCasesOn'' x fun nx dx h_dx _ =>
  numDenCasesOn'' y fun ny dy h_dy _ => by
    let dy_dx_nz : dy * dx ≠ 0 :=
      Nat.mul_ne_zero h_dy h_dx
    change Rat.blt _ _ = false ↔ _
    unfold Rat.blt
    simp only
      [ Bool.and_eq_true, decide_eq_true_eq, Bool.ite_eq_false_distrib,
        decide_eq_false_iff_not, Rat.not_lt, ite_eq_left_iff,
        not_and, Rat.not_le, ← Rat.num_nonneg ]
    if h : ny < 0 ∧ 0 ≤ nx then
      simp only [h, and_self, ↓reduceIte, Bool.true_eq_false, num_nonneg, false_iff]
      simp only [Rat.sub_def, Rat.not_le, normalize_eq, Rat.neg]
      simp [← Rat.num_neg]
      apply Int.ediv_neg_of_neg_of_pos
      · apply Int.sub_neg_of_lt
        apply Int.lt_of_lt_of_le (b := 0)
        · apply Int.mul_neg_of_neg_of_pos h.1
          apply Int.natCast_pos.mpr
          apply Nat.pos_of_ne_zero h_dx
        · apply Int.mul_nonneg h.2
          exact Int.zero_le_natCast
      · apply Int.natCast_pos.mpr
        apply Nat.pos_iff_ne_zero.mpr
        exact Nat.gcd_ne_zero_right dy_dx_nz
    else
      simp [h]
      split
      case isTrue nb_0 =>
        simp [nb_0, Rat.sub_eq_add_neg, Rat.zero_add, Rat.nonneg_sub_iff_nonpos, ← Rat.num_nonpos]
      case isFalse nb_nz =>
        simp only [Rat.sub_def, normalize_eq, ← Rat.num_nonneg]
        if ny_pos : 0 < ny then
          simp only [ny_pos, forall_const]
          if h_na : 0 < nx then
            simp_all only [not_and, Int.not_le, forall_const]
            rw [← Int.sub_nonneg]
            apply Iff.symm
            apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz
          else
            let na_nonpos := Int.not_lt.mp h_na
            simp_all only [not_and, Int.not_le, false_implies, true_iff, ge_iff_le]
            apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz |>.mpr
            · apply Int.sub_nonneg_of_le
              apply Int.le_trans (b := 0)
              apply Int.mul_nonpos_of_nonpos_of_nonneg
              · exact Int.not_lt.mp h_na
              · exact Int.natCast_nonneg ↑dy
              · apply Int.mul_nonneg _ (Int.natCast_nonneg ↑dx)
                exact Int.le_of_lt ny_pos
        else
          simp [ny_pos, Int.not_lt, ← Int.sub_nonneg]
          rw [Int.sub_zero]
          rw [Int.sub_zero]
          apply Iff.symm
          apply Int.div_gcd_nonneg_iff_of_nz dy_dx_nz

protected theorem sub_nonneg {a b : Rat} : 0 ≤ a - b ↔ b ≤ a := by
  rw [Rat.le_iff_sub_nonneg b a]

@[simp]
theorem divInt_nonneg_iff_of_pos_right {a b : Int} (hb : 0 < b) : 0 ≤ a /. b ↔ 0 ≤ a := by
  cases hab : a /. b with | mk' n d hd hnd =>
  rw [mk'_eq_divInt, divInt_eq_iff (Int.ne_of_lt hb).symm (mod_cast hd)] at hab
  rw [
    ← Rat.num_nonneg, ← Int.mul_nonneg_iff_of_pos_right hb, ← hab,
    Int.mul_nonneg_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd),
  ]

theorem divInt_pos_iff_of_pos_right {a b : Int} (hb : 0 < b) : 0 < a /. b ↔ 0 < a := by
  cases hab : a /. b with | mk' n d hd hnd =>
  rw [mk'_eq_divInt, divInt_eq_iff (Int.ne_of_lt hb).symm (mod_cast hd)] at hab
  rw [ ← Rat.num_pos, <- Int.mul_pos_iff_of_pos_right hb, <- hab,
       Int.mul_pos_iff_of_pos_right (mod_cast Nat.pos_of_ne_zero hd)]

theorem divInt_neg_iff_of_neg_right {a b : Int} (hb : 0 < b) : 0 > a /. b ↔ 0 > a := by
  have f : ¬ (0 ≤ a /. b) ↔ ¬ (0 ≤ a) := not_congr (divInt_nonneg_iff_of_pos_right hb)
  rw [Int.not_le, Rat.not_le] at f
  exact f

protected theorem divInt_le_divInt
  {a b c d : Int} (b0 : 0 < b) (d0 : 0 < d)
: a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← Int.sub_nonneg]
  simp [Rat.sub_eq_add_neg, Rat.neg_divInt, Int.ne_of_gt b0, Int.ne_of_gt d0, Int.mul_pos d0 b0]
  rw [Rat.divInt_add_divInt]
  simp only [Rat.divInt_nonneg_iff_of_pos_right (Int.mul_pos d0 b0), Int.neg_mul]
  rw [← Int.sub_nonneg (a := c * b)]
  rw [← Int.sub_eq_add_neg]
  · apply Int.lt_iff_le_and_ne.mp d0 |>.2 |>.symm
  · apply Int.lt_iff_le_and_ne.mp b0 |>.2 |>.symm

theorem mul_assoc (a b c : Rat) : a * b * c = a * (b * c) :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ =>
      numDenCasesOn' c fun n₃ d₃ h₃ => by
        simp [h₁, h₂, h₃, Int.mul_comm, Nat.mul_assoc, Int.mul_left_comm, mkRat_mul_mkRat]

theorem cast_lt1 {a b : Int} : Rat.ofInt a < Rat.ofInt b -> a < b := by
  intro h
  simp [Rat.instLT, Rat.ofInt] at h
  simp [Rat.blt] at h
  cases h with
  | inl h =>
    let ⟨h1, h2⟩ := h
    exact Int.lt_of_lt_of_le h1 h2
  | inr h =>
    cases Classical.em (a = 0) with
    | inl ha => simp [ha] at h; exact lt_of_eq_of_lt ha h
    | inr ha =>
      simp [ha] at h
      exact h.2

theorem cast_lt2 {a b : Int} : a < b → Rat.ofInt a < Rat.ofInt b := by
  intro h
  simp only [instLT, ofInt, mk_den_one]
  simp [Rat.blt]
  cases Classical.em (a = 0) with
  | inl ha => simp [ha]; rw [ha] at h; exact h
  | inr ha =>
      simp only [ha, ↓reduceIte]
      right
      constructor
      · omega
      · exact h

theorem cast_lt {a b : Int} : a < b ↔ Rat.ofInt a < Rat.ofInt b :=
  ⟨ Rat.cast_lt2, Rat.cast_lt1 ⟩

theorem cast_le1 {a b : Int} : Rat.ofInt a ≤ Rat.ofInt b -> a ≤ b := by
  intro h
  simp only [instLE, ofInt, mk_den_one] at h
  simp [Rat.blt] at h
  cases Classical.em (b = 0) with
  | inl hb =>
    simp [hb] at h
    rw [hb]
    exact h
  | inr hb =>
    simp [hb] at h
    let ⟨h1, h2⟩ := h
    cases Classical.em (a ≤ b) with
    | inl hab => exact hab
    | inr hab =>
      have : ¬ a ≤ b → ¬ (b ≤ 0 ∨ 0 < a) := fun a_1 a => hab (h2 a)
      have := this hab
      rw [not_or] at this
      let ⟨h3, h4⟩ := this
      rw [Int.not_le] at h3
      rw [Int.not_lt] at h4
      have := Int.lt_of_le_of_lt h4 h3
      exact Int.le_of_lt this

theorem cast_le2 {a b : Int} : a ≤ b → Rat.ofInt a ≤ Rat.ofInt b := by
  intro h
  simp [Rat.instLE, Rat.ofInt]
  simp [Rat.blt]
  cases Classical.em (b = 0) with
  | inl hb =>
    simp [hb]
    rw [hb] at h
    exact h
  | inr hb =>
    simp [hb]
    constructor <;> omega

theorem cast_le {a b : Int} : a ≤ b ↔ Rat.ofInt a ≤ Rat.ofInt b :=
  ⟨ Rat.cast_le2, Rat.cast_le1 ⟩

theorem cast_ge {a b : Int} : a ≥ b ↔ Rat.ofInt a ≥ Rat.ofInt b :=
  ⟨ Rat.cast_le2, Rat.cast_le1 ⟩

theorem cast_gt {a b : Int} : a > b ↔ Rat.ofInt a > Rat.ofInt b :=
  ⟨ Rat.cast_lt2, Rat.cast_lt1 ⟩

theorem cast_eq {a b : Int} : a = b ↔ Rat.ofInt a = Rat.ofInt b := by
  constructor
  · intro h; rw [h]
  · intro h; exact Rat.intCast_inj.mp h

theorem floor_def' (a : Rat) : a.floor = a.num / a.den := by
  rw [Rat.floor]
  split
  · next h => simp [h]
  · next => rfl

theorem intCast_eq_divInt (z : Int) : (z : Rat) = z /. 1 := mk'_eq_divInt

theorem le_floor {z : Int} : ∀ {r : Rat}, z ≤ Rat.floor r ↔ (z : Rat) ≤ r
  | ⟨n, d, h, c⟩ => by
    simp only [Rat.floor_def']
    rw [mk'_eq_divInt]
    have h' := Int.ofNat_lt.2 (Nat.pos_of_ne_zero h)
    conv =>
      rhs
      rw [Rat.intCast_eq_divInt, Rat.divInt_le_divInt Int.zero_lt_one h', Int.mul_one]
    exact Int.le_ediv_iff_mul_le h'

theorem mul_add (a b c : Rat) : a * (b + c) = a * b + a * c :=
  Rat.numDenCasesOn' a fun a_num a_den a_den_nz =>
    Rat.numDenCasesOn' b fun b_num b_den b_den_nz =>
      Rat.numDenCasesOn' c fun c_num c_den c_den_nz => by
        have a_den_nz' : (a_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr a_den_nz
        have b_den_nz' : (b_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr b_den_nz
        have c_den_nz' : (c_den : Int) ≠ 0 := Int.ofNat_ne_zero.mpr c_den_nz
        have ab_den_nz : (a_den * b_den : Int) ≠ 0 := Int.mul_ne_zero a_den_nz' b_den_nz'
        have bc_den_nz : (b_den * c_den : Int) ≠ 0 := Int.mul_ne_zero b_den_nz' c_den_nz'
        have ac_den_nz : (a_den * c_den : Int) ≠ 0 := Int.mul_ne_zero a_den_nz' c_den_nz'
        have abc_den_nz : (a_den * (b_den * c_den) : Int) ≠ 0 := Int.mul_ne_zero a_den_nz' bc_den_nz
        have abac_den_nz : (a_den * b_den * (a_den * c_den) : Int) ≠ 0 := Int.mul_ne_zero ab_den_nz ac_den_nz
        rw [Rat.divInt_mul_divInt a_num b_num a_den_nz' b_den_nz']
        rw [Rat.divInt_mul_divInt a_num c_num a_den_nz' c_den_nz']
        rw [Rat.divInt_add_divInt (a_num * b_num) (a_num * c_num) ab_den_nz ac_den_nz]
        rw [Rat.divInt_add_divInt b_num c_num b_den_nz' c_den_nz']
        rw [Rat.divInt_mul_divInt a_num (b_num * c_den + c_num * b_den) a_den_nz' bc_den_nz]
        rw [Rat.divInt_eq_iff abc_den_nz abac_den_nz]
        rw [Int.mul_assoc]
        rw [Int.mul_comm _ (a_den * (b_den * c_den))]
        rw [Int.mul_assoc a_num b_num]
        rw [Int.mul_assoc a_num c_num]
        rw [<- Int.mul_add a_num]
        rw [Int.mul_comm b_num (a_den * c_den)]
        rw [Int.mul_assoc a_den c_den b_num]
        rw [Int.mul_comm c_num (a_den * b_den)]
        rw [Int.mul_assoc a_den b_den c_num]
        rw [<- Int.mul_add a_den]
        simp [Int.mul_assoc, Int.mul_comm]
        rw [<- Int.mul_assoc a_den (b_num * c_den + c_num * b_den)]
        rw [Int.mul_comm a_den (b_num * c_den + c_num * b_den)]
        simp [Int.mul_assoc]
        rw [<- Int.mul_assoc b_den a_den c_den]
        rw [Int.mul_comm b_den a_den]
        rw [Int.mul_assoc a_den b_den c_den]

@[simp]
protected theorem neg_zero : -(0:Rat) = 0 := rfl

protected theorem add_mul (a b c : Rat) : (a + b) * c = a * c + b * c := by
  simp [Rat.mul_comm, Rat.mul_add]

protected theorem neg_add (a b : Rat) : -(a + b) = -a + -b := by
  rw [←Rat.sub_eq_add_neg, ←Rat.neg_neg b, ←Rat.sub_eq_add_neg, Rat.neg_sub]
  simp [Rat.sub_eq_add_neg, Rat.add_comm, Rat.neg_neg]

theorem neg_eq_neg_one_mul (a : Rat) : -a = -1 * a :=
  numDenCasesOn a fun n d h h1 => by
    simp [Rat.neg_mkRat, Rat.mul_def, Rat.normalize_eq_mkRat]
    simp [← Rat.divInt_ofNat]
    rw [divInt_num' (Nat.pos_iff_ne_zero.mp h) h1, divInt_den' (Nat.pos_iff_ne_zero.mp h) h1]

protected theorem neg_mul (a b : Rat) : -(a * b) = -a * b := by
  rw [neg_eq_neg_one_mul, neg_eq_neg_one_mul a, Rat.mul_assoc]

protected theorem mul_neg (a b : Rat) : a * -b = -(a * b) := by
  rw [neg_eq_neg_one_mul (a * b), neg_eq_neg_one_mul b, ← Rat.mul_assoc, Rat.mul_comm a, Rat.mul_assoc]

protected theorem mul_div_right_comm (a b c : Rat) : a * b / c = a / c * b := by
  rw [div_def, div_def, Rat.mul_assoc, Rat.mul_comm b c.inv, Rat.mul_assoc]

protected theorem zero_div (a : Rat) : 0 / a = 0 := by
  simp [div_def]

protected theorem add_div (a b c : Rat) : (a + b) / c = a / c + b / c := by
  simp [div_def, Rat.add_mul]

theorem le_total (a b : Rat) : a ≤ b ∨ b ≤ a := by
  simpa only [← Rat.le_iff_sub_nonneg, Rat.neg_sub] using Rat.nonneg_total (b - a)

theorem divInt_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a /. b := by
  have : 0 = b ∨ 0 < b := Int.le_iff_eq_or_lt.mp hb
  obtain rfl | hb := this
  · simp
  rwa [divInt_nonneg_iff_of_pos_right hb]

theorem mul_nonneg {a b : Rat} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
  numDenCasesOn' a fun n₁ d₁ h₁ =>
    numDenCasesOn' b fun n₂ d₂ h₂ => by
      have d₁0 : 0 < (d₁ : Int) := mod_cast Nat.pos_of_ne_zero h₁
      have d₂0 : 0 < (d₂ : Int) := mod_cast Nat.pos_of_ne_zero h₂
      simp only [d₁0, d₂0, Int.mul_pos, divInt_nonneg_iff_of_pos_right,
        divInt_mul_divInt _ _ (Ne.symm (Int.ne_of_lt d₁0)) (Ne.symm (Int.ne_of_lt d₁0))]
      intro h1 h2
      have h1' : 0 ≤ Rat.divInt n₁ d₁ := divInt_nonneg h1 (Int.ofNat_zero_le d₁)
      have h2' : 0 ≤ Rat.divInt n₂ d₂ := divInt_nonneg h2 (Int.ofNat_zero_le d₂)
      rw [divInt_mul_divInt n₁ n₂ (Int.ofNat_ne_zero.mpr h₁) ((Int.ofNat_ne_zero.mpr h₂))]
      apply divInt_nonneg
      · exact Int.mul_nonneg h1 h2
      · exact Lean.Omega.Int.ofNat_mul_nonneg

def addN : List Rat → Rat
  | []      => 0
  | [x]     => x
  | x :: xs => x + addN xs

@[simp] theorem addN_append : addN (xs ++ ys) = addN xs + addN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [addN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, addN, addN, addN_append, Rat.add_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem addN_cons_append : addN (x :: xs) = x + addN xs := by
  cases xs <;> simp only [addN, Rat.add_zero]

def mulN : List Rat → Rat
  | []      => 1
  | [x]     => x
  | x :: xs => x * mulN xs

@[simp] theorem mulN_append : mulN (xs ++ ys) = mulN xs * mulN ys := by
  match xs, ys with
  | [], _
  | [x], []
  | [x], y :: ys       => simp [mulN]
  | x₁ :: x₂ :: xs, ys =>
    rw [List.cons_append, mulN, mulN, mulN_append, Rat.mul_assoc]
    all_goals (intro h; nomatch h)

@[simp] theorem mulN_cons_append : mulN (x :: xs) = x * mulN xs := by
  cases xs <;> simp only [mulN, Rat.mul_one]

end Rat
