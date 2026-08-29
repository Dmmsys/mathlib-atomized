/-
Copyright (c) 2024 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm

/-!
# SeminormFromConst


In this file, we prove [BGR, Proposition 1.3.2/2][bosch-guntzer-remmert] : starting from a
power-multiplicative seminorm on a commutative ring `R` and a nonzero `c : R`, we create a new
power-multiplicative seminorm for which `c` is multiplicative.

## Main Definitions

* `seminormFromConst'` : the real-valued function sending `x ∈ R` to the limit of
  `(f (x * c^n))/((f c)^n)`.
* `seminormFromConst` : the function `seminormFromConst'` as a `RingSeminorm` on `R`.


## Main Results
* `seminormFromConst_isNonarchimedean` : the function `seminormFromConst' c f`
  is nonarchimedean when f is nonarchimedean.
* `seminormFromConst_isPowMul` : the function `seminormFromConst' c f`
  is power-multiplicative.
* `seminormFromConst_const_mul` : for every `x : R`, `seminormFromConst' c f (c * x)`
  equals the product `seminormFromConst' c f c * seminormFromConst' c f x`.

## References
* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert]

## Tags

SeminormFromConst, Seminorm, Nonarchimedean
-/

@[expose] public section

noncomputable section

open Filter

open scoped Topology

section Ring

variable {R : Type*} [CommRing R] (c : R) (f : RingSeminorm R)

/--
Definition of `seminormFromConst_seq` / `seminormFromConst_seq` 的定义

English:
definition seminormFromConst_seq
  signature: (x : R)
  body: fun n => f (x * c ^ n) / f c ^ n

中文:
定义 seminormFromConst_seq
  签名: (x : R)
  定义体: fun n => f (x * c ^ n) / f c ^ n
-/
def seminormFromConst_seq (x : R) : Nat -> Real := fun n => f (x * c ^ n) / f c ^ n

/--
lemma `seminormFromConst_seq_def` / 引理 `seminormFromConst_seq_def`

English:
lemma seminormFromConst_seq_def
  given: (x : R)
  proof: rfl

中文:
引理 seminormFromConst_seq_def
  条件: (x : R)
  证明: rfl
-/
lemma seminormFromConst_seq_def (x : R) :
    seminormFromConst_seq c f x = fun n => f (x * c ^ n) / f c ^ n := rfl

/--
theorem `seminormFromConst_seq_nonneg` / 定理 `seminormFromConst_seq_nonneg`

English:
theorem seminormFromConst_seq_nonneg
  given: (x : R)
  statement: 0 <= seminormFromConst_seq c f x
  proof: fun n => div_nonneg (apply_nonneg f (x * c ^ n)) (pow_nonneg (apply_nonneg f c) n)

中文:
定理 seminormFromConst_seq_nonneg
  条件: (x : R)
  结论: 0 <= seminormFromConst_seq c f x
  证明: fun n => div_nonneg (apply_nonneg f (x * c ^ n)) (pow_nonneg (apply_nonneg f c) n)

Depends on / 依赖: apply_nonneg, div_nonneg, pow_nonneg
-/
theorem seminormFromConst_seq_nonneg (x : R) : 0 <= seminormFromConst_seq c f x :=
  fun n => div_nonneg (apply_nonneg f (x * c ^ n)) (pow_nonneg (apply_nonneg f c) n)

/--
theorem `seminormFromConst_bddBelow` / 定理 `seminormFromConst_bddBelow`

English:
theorem seminormFromConst_bddBelow
  given: (x : R)
  proof: by
  use 0
  rintro r ⟨n, rfl⟩
  exact seminormFromConst_seq_nonneg c f x n

中文:
定理 seminormFromConst_bddBelow
  条件: (x : R)
  证明: by
  use 0
  rintro r ⟨n, rfl⟩
  exact seminormFromConst_seq_nonneg c f x n

Depends on / 依赖: seminormFromConst_seq_nonneg
-/
theorem seminormFromConst_bddBelow (x : R) :
    BddBelow (Set.range (seminormFromConst_seq c f x)) := by
  use 0
  rintro r ⟨n, rfl⟩
  exact seminormFromConst_seq_nonneg c f x n

variable {f}

/--
theorem `seminormFromConst_seq_zero` / 定理 `seminormFromConst_seq_zero`

English:
theorem seminormFromConst_seq_zero
  given: (hf : f 0 = 0)
  statement: seminormFromConst_seq c f 0 = 0
  proof: by
  rw [seminormFromConst_seq_def]
  ext n
  rw [zero_mul]; rw [hf]; rw [zero_div]; rw [Pi.zero_apply]

中文:
定理 seminormFromConst_seq_zero
  条件: (hf : f 0 = 0)
  结论: seminormFromConst_seq c f 0 = 0
  证明: by
  rw [seminormFromConst_seq_def]
  ext n
  rw [zero_mul]; rw [hf]; rw [zero_div]; rw [Pi.zero_apply]

Depends on / 依赖: Pi.zero_apply, Quotient, Quotient.inductionOn, inductionOn, seminormFromConst_seq_def, zero_apply, zero_div, zero_mul
-/
theorem seminormFromConst_seq_zero (hf : f 0 = 0) : seminormFromConst_seq c f 0 = 0 := by
  rw [seminormFromConst_seq_def]
  ext n
  rw [zero_mul]; rw [hf]; rw [zero_div]; rw [Pi.zero_apply]

variable {c}
variable (hf1 : f 1 <= 1) (hc : f c != 0) (hpm : IsPowMul f)
include hpm hc

/--
theorem `seminormFromConst_seq_one` / 定理 `seminormFromConst_seq_one`

English:
theorem seminormFromConst_seq_one
  given: (n : Nat) (hn : 1 <= n)
  statement: seminormFromConst_seq c f 1 n = 1
  proof: by
  simp only [seminormFromConst_seq]
  rw [one_mul]; rw [hpm _ hn]; rw [div_self (pow_ne_zero n hc)]

include hf1

中文:
定理 seminormFromConst_seq_one
  条件: (n : 自然数) (hn : 1 <= n)
  结论: seminormFromConst_seq c f 1 n = 1
  证明: by
  simp only [seminormFromConst_seq]
  rw [one_mul]; rw [hpm _ hn]; rw [div_self (pow_ne_zero n hc)]

include hf1

Depends on / 依赖: Classical, Classical.inhabited_of_nonempty, div_self, inhabited_of_nonempty, one_mul, pow_ne_zero, seminormFromConst_seq
-/
theorem seminormFromConst_seq_one (n : Nat) (hn : 1 <= n) : seminormFromConst_seq c f 1 n = 1 := by
  simp only [seminormFromConst_seq]
  rw [one_mul]; rw [hpm _ hn]; rw [div_self (pow_ne_zero n hc)]

include hf1

/--
theorem `seminormFromConst_seq_antitone` / 定理 `seminormFromConst_seq_antitone`

English:
theorem seminormFromConst_seq_antitone
  given: (x : R)
  statement: Antitone (seminormFromConst_seq c f x)
  proof: by
  intro m n hmn
  simp only [seminormFromConst_seq]
  nth_rw 1 [← Nat.add_sub_of_le hmn]
  rw [pow_add]; rw [← mul_assoc]
  have hc_pos : 0 < f c := lt_of_le_of_ne (apply_nonneg f _) hc.symm
  apply le_trans ((div_le_div_iff_of_pos_right (pow_pos hc_pos _)).mpr (map_mul_le_mul f _ _))
  cases hmn.eq_or_lt with
  | inl heq =>
    have hnm : n - m = 0 := by rw [heq, Nat.sub_self n]
    rw [hnm]; rw [heq]; rw [div_le_div_iff_of_pos_right (pow_pos hc_pos _)]; rw [pow_zero]
    conv_rhs => rw [← mul_one (f (x * c ^ n))]
    gcongr
  | inr hlt =>
    have h1 : 1 <= n - m := by
      rw [Nat.one_le_iff_ne_zero]
      exact Nat.sub_ne_zero_of_lt hlt
    rw [hpm c h1]; rw [mul_div_assoc]; rw [div_eq_mul_inv]; rw [pow_sub₀ _ hc hmn]; rw [mul_assoc]; rw [mul_comm (f c ^ m)⁻¹]; rw [← mul_assoc (f c ^ n)]; rw [mul_inv_cancel₀ (pow_ne_zero n hc)]; rw [one_mul]; rw [div_eq_mul_inv]

中文:
定理 seminormFromConst_seq_antitone
  条件: (x : R)
  结论: 递减 (seminormFromConst_seq c f x)
  证明: by
  intro m n hmn
  simp only [seminormFromConst_seq]
  nth_rw 1 [← Nat.add_sub_of_le hmn]
  rw [pow_add]; rw [← mul_assoc]
  have hc_pos : 0 < f c := lt_of_le_of_ne (apply_nonneg f _) hc.symm
  apply le_trans ((div_le_div_iff_of_pos_right (pow_pos hc_pos _)).mpr (map_mul_le_mul f _ _))
  cases hmn.eq_or_lt with
  | inl heq =>
    have hnm : n - m = 0 := by rw [heq, Nat.sub_self n]
    rw [hnm]; rw [heq]; rw [div_le_div_iff_of_pos_right (pow_pos hc_pos _)]; rw [pow_zero]
    conv_rhs => rw [← mul_one (f (x * c ^ n))]
    gcongr
  | inr hlt =>
    have h1 : 1 <= n - m := by
      rw [Nat.one_le_iff_ne_zero]
      exact Nat.sub_ne_zero_of_lt hlt
    rw [hpm c h1]; rw [mul_div_assoc]; rw [div_eq_mul_inv]; rw [pow_sub₀ _ hc hmn]; rw [mul_assoc]; rw [mul_comm (f c ^ m)⁻¹]; rw [← mul_assoc (f c ^ n)]; rw [mul_inv_cancel₀ (pow_ne_zero n hc)]; rw [one_mul]; rw [div_eq_mul_inv]

Depends on / 依赖: Nat.add_sub_of_le, Nat.sub_self, add_sub_of_le, apply_nonneg, conv_rhs, div_le_div_iff_of_pos_right, eq_or_lt, hc.symm, hc_pos, hmn.eq_or_lt, le_trans, lt_of_le_of_ne, map_mul_le_mul, mul_assoc, mul_one, nth_rw, pow_add, pow_pos, pow_zero, seminormFromConst_seq
-/
theorem seminormFromConst_seq_antitone (x : R) : Antitone (seminormFromConst_seq c f x) := by
  intro m n hmn
  simp only [seminormFromConst_seq]
  nth_rw 1 [← Nat.add_sub_of_le hmn]
  rw [pow_add]; rw [← mul_assoc]
  have hc_pos : 0 < f c := lt_of_le_of_ne (apply_nonneg f _) hc.symm
  apply le_trans ((div_le_div_iff_of_pos_right (pow_pos hc_pos _)).mpr (map_mul_le_mul f _ _))
  cases hmn.eq_or_lt with
  | inl heq =>
    have hnm : n - m = 0 := by rw [heq, Nat.sub_self n]
    rw [hnm]; rw [heq]; rw [div_le_div_iff_of_pos_right (pow_pos hc_pos _)]; rw [pow_zero]
    conv_rhs => rw [← mul_one (f (x * c ^ n))]
    gcongr
  | inr hlt =>
    have h1 : 1 <= n - m := by
      rw [Nat.one_le_iff_ne_zero]
      exact Nat.sub_ne_zero_of_lt hlt
    rw [hpm c h1]; rw [mul_div_assoc]; rw [div_eq_mul_inv]; rw [pow_sub₀ _ hc hmn]; rw [mul_assoc]; rw [mul_comm (f c ^ m)⁻¹]; rw [← mul_assoc (f c ^ n)]; rw [mul_inv_cancel₀ (pow_ne_zero n hc)]; rw [one_mul]; rw [div_eq_mul_inv]

/--
Definition of `seminormFromConst'` / `seminormFromConst'` 的定义

English:
definition seminormFromConst'
  signature: (c : R) (f : RingSeminorm R) (x : R)
  body: iInf (seminormFromConst_seq c f x)

中文:
定义 seminormFromConst'
  签名: (c : R) (f : 环半范数 R) (x : R)
  定义体: iInf (seminormFromConst_seq c f x)

Depends on / 依赖: seminormFromConst_seq
-/
def seminormFromConst' (c : R) (f : RingSeminorm R) (x : R) : Real :=
  iInf (seminormFromConst_seq c f x)

/--
theorem `tendsto_seminormFromConst_seq_atTop` / 定理 `tendsto_seminormFromConst_seq_atTop`

English:
theorem tendsto_seminormFromConst_seq_atTop
  given: (x : R)
  proof: tendsto_atTop_ciInf (seminormFromConst_seq_antitone hf1 hc hpm x)
    (seminormFromConst_bddBelow c f x)

@[deprecated (since := "2026-01-14")]
alias seminormFromConst_isLimit := tendsto_seminormFromConst_seq_atTop

中文:
定理 tendsto_seminormFromConst_seq_atTop
  条件: (x : R)
  证明: tendsto_atTop_ciInf (seminormFromConst_seq_antitone hf1 hc hpm x)
    (seminormFromConst_bddBelow c f x)

@[deprecated (since := "2026-01-14")]
alias seminormFromConst_isLimit := tendsto_seminormFromConst_seq_atTop

Depends on / 依赖: seminormFromConst_bddBelow, seminormFromConst_seq_antitone, tendsto_atTop_ciInf
-/
theorem tendsto_seminormFromConst_seq_atTop (x : R) :
    Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (seminormFromConst' c f x)) :=
  tendsto_atTop_ciInf (seminormFromConst_seq_antitone hf1 hc hpm x)
    (seminormFromConst_bddBelow c f x)

@[deprecated (since := "2026-01-14")]
alias seminormFromConst_isLimit := tendsto_seminormFromConst_seq_atTop

/--
theorem `seminormFromConst_one` / 定理 `seminormFromConst_one`

English:
theorem seminormFromConst_one
  statement: seminormFromConst' c f 1 = 1
  proof: by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst_seq_atTop hf1 hc hpm 1)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  exact ⟨1, seminormFromConst_seq_one hc hpm⟩

中文:
定理 seminormFromConst_one
  结论: seminormFromConst' c f 1 = 1
  证明: by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst_seq_atTop hf1 hc hpm 1)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  exact ⟨1, seminormFromConst_seq_one hc hpm⟩

Depends on / 依赖: EventuallyEq, eventually_atTop, seminormFromConst_seq_one, tendsto_const_nhds, tendsto_nhds_unique_of_eventuallyEq, tendsto_seminormFromConst_seq_atTop
-/
theorem seminormFromConst_one : seminormFromConst' c f 1 = 1 := by
  apply tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst_seq_atTop hf1 hc hpm 1)
    tendsto_const_nhds
  simp only [EventuallyEq, eventually_atTop]
  exact ⟨1, seminormFromConst_seq_one hc hpm⟩

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
Definition of `seminormFromConst` / `seminormFromConst` 的定义

English:
definition seminormFromConst
  signature: : RingSeminorm R where
  body: seminormFromConst' c f
  map_zero' := tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm 0)
    (by simpa [seminormFromConst_seq_zero c (map_zero _)] using! tendsto_const_nhds)
  add_le' x y := by
apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x + y))
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).add
        (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)
    intro n
    have h_add : f ((x + y) * c ^ n) <= f (x * c ^ n) + f (y * c ^ n) := by
      simp only [add_mul, map_add_le_add f _ _]
    simp only [seminormFromConst_seq, ← add_div]
    gcongr
  neg' x := by
    apply tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (-x))
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x)
    simp only [EventuallyEq, eventually_atTop]
    use 0
    simp only [seminormFromConst_seq, neg_mul, map_neg_eq_map, zero_le, implies_true]
  mul_le' x y := by
    have hlim : Tendsto (fun n => seminormFromConst_seq c f (x * y) (2 * n)) atTop
        (𝓝 (seminormFromConst' c f (x * y))) := by
      apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x * y)).comp
        (tendsto_atTop_atTop_of_monotone (fun _ _ hnm => by
          simp only [mul_le_mul_iff_right₀, Nat.succ_pos', hnm]) _)
      · rintro n; use n; lia
    refine le_of_tendsto_of_tendsto' hlim ((tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).mul
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)) (fun n => ?_)
    simp only [seminormFromConst_seq]
    rw [div_mul_div_comm]; rw [← pow_add]; rw [two_mul]; rw [div_le_div_iff_of_pos_right (pow_pos (lt_of_le_of_ne (apply_nonneg f _) hc.symm) _)]; rw [pow_add]; rw [← mul_assoc]; rw [mul_comm (x * y)]; rw [← mul_assoc]; rw [mul_assoc]; rw [mul_comm (c ^ n)]
    exact map_mul_le_mul f (x * c ^ n) (y * c ^ n)

中文:
定义 seminormFromConst
  签名: : 环半范数 R where
  定义体: seminormFromConst' c f
  map_zero' := tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm 0)
    (by simpa [seminormFromConst_seq_zero c (map_zero _)] using! tendsto_const_nhds)
  add_le' x y := by
apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x + y))
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).add
        (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)
    intro n
    have h_add : f ((x + y) * c ^ n) <= f (x * c ^ n) + f (y * c ^ n) := by
      simp only [add_mul, map_add_le_add f _ _]
    simp only [seminormFromConst_seq, ← add_div]
    gcongr
  neg' x := by
    apply tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (-x))
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x)
    simp only [EventuallyEq, eventually_atTop]
    use 0
    simp only [seminormFromConst_seq, neg_mul, map_neg_eq_map, zero_le, implies_true]
  mul_le' x y := by
    have hlim : Tendsto (fun n => seminormFromConst_seq c f (x * y) (2 * n)) atTop
        (𝓝 (seminormFromConst' c f (x * y))) := by
      apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x * y)).comp
        (tendsto_atTop_atTop_of_monotone (fun _ _ hnm => by
          simp only [mul_le_mul_iff_right₀, Nat.succ_pos', hnm]) _)
      · rintro n; use n; lia
    refine le_of_tendsto_of_tendsto' hlim ((tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).mul
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)) (fun n => ?_)
    simp only [seminormFromConst_seq]
    rw [div_mul_div_comm]; rw [← pow_add]; rw [two_mul]; rw [div_le_div_iff_of_pos_right (pow_pos (lt_of_le_of_ne (apply_nonneg f _) hc.symm) _)]; rw [pow_add]; rw [← mul_assoc]; rw [mul_comm (x * y)]; rw [← mul_assoc]; rw [mul_assoc]; rw [mul_comm (c ^ n)]
    exact map_mul_le_mul f (x * c ^ n) (y * c ^ n)

Depends on / 依赖: seminormFromConst
-/
def seminormFromConst : RingSeminorm R where
  toFun := seminormFromConst' c f
  map_zero' := tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm 0)
    (by simpa [seminormFromConst_seq_zero c (map_zero _)] using! tendsto_const_nhds)
  add_le' x y := by
apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x + y))
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).add
        (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)
    intro n
    have h_add : f ((x + y) * c ^ n) <= f (x * c ^ n) + f (y * c ^ n) := by
      simp only [add_mul, map_add_le_add f _ _]
    simp only [seminormFromConst_seq, ← add_div]
    gcongr
  neg' x := by
    apply tendsto_nhds_unique_of_eventuallyEq (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (-x))
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x)
    simp only [EventuallyEq, eventually_atTop]
    use 0
    simp only [seminormFromConst_seq, neg_mul, map_neg_eq_map, zero_le, implies_true]
  mul_le' x y := by
    have hlim : Tendsto (fun n => seminormFromConst_seq c f (x * y) (2 * n)) atTop
        (𝓝 (seminormFromConst' c f (x * y))) := by
      apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x * y)).comp
        (tendsto_atTop_atTop_of_monotone (fun _ _ hnm => by
          simp only [mul_le_mul_iff_right₀, Nat.succ_pos', hnm]) _)
      · rintro n; use n; lia
    refine le_of_tendsto_of_tendsto' hlim ((tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).mul
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)) (fun n => ?_)
    simp only [seminormFromConst_seq]
    rw [div_mul_div_comm]; rw [← pow_add]; rw [two_mul]; rw [div_le_div_iff_of_pos_right (pow_pos (lt_of_le_of_ne (apply_nonneg f _) hc.symm) _)]; rw [pow_add]; rw [← mul_assoc]; rw [mul_comm (x * y)]; rw [← mul_assoc]; rw [mul_assoc]; rw [mul_comm (c ^ n)]
    exact map_mul_le_mul f (x * c ^ n) (y * c ^ n)

/--
theorem `seminormFromConst_def` / 定理 `seminormFromConst_def`

English:
theorem seminormFromConst_def
  given: (x : R)
  proof: rfl

中文:
定理 seminormFromConst_def
  条件: (x : R)
  证明: rfl
-/
theorem seminormFromConst_def (x : R) :
    seminormFromConst hf1 hc hpm x = seminormFromConst' c f x :=
  rfl

/--
theorem `seminormFromConst_one_le` / 定理 `seminormFromConst_one_le`

English:
theorem seminormFromConst_one_le
  statement: seminormFromConst' c f 1 <= 1
  proof: le_of_eq (seminormFromConst_one hf1 hc hpm)

中文:
定理 seminormFromConst_one_le
  结论: seminormFromConst' c f 1 <= 1
  证明: le_of_eq (seminormFromConst_one hf1 hc hpm)

Depends on / 依赖: le_of_eq, seminormFromConst_one
-/
theorem seminormFromConst_one_le : seminormFromConst' c f 1 <= 1 :=
  le_of_eq (seminormFromConst_one hf1 hc hpm)

/--
theorem `seminormFromConst_isNonarchimedean` / 定理 `seminormFromConst_isNonarchimedean`

English:
theorem seminormFromConst_isNonarchimedean
  given: (hna : IsNonarchimedean f)
  proof: fun x y => by
apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x + y))
    (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).max
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)
  intro n
  have hmax : f ((x + y) * c ^ n) <= max (f (x * c ^ n)) (f (y * c ^ n)) := by
    simp only [add_mul, hna _ _]
  rw [le_max_iff] at hmax ⊢
  unfold seminormFromConst_seq
  apply hmax.imp <;> intro <;> gcongr

中文:
定理 seminormFromConst_isNonarchimedean
  条件: (hna : IsNonarchimedean f)
  证明: fun x y => by
apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x + y))
    (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).max
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)
  intro n
  have hmax : f ((x + y) * c ^ n) <= max (f (x * c ^ n)) (f (y * c ^ n)) := by
    simp only [add_mul, hna _ _]
  rw [le_max_iff] at hmax ⊢
  unfold seminormFromConst_seq
  apply hmax.imp <;> intro <;> gcongr

Depends on / 依赖: add_mul, hmax.imp, le_max_iff, le_of_tendsto_of_tendsto, seminormFromConst_seq, tendsto_seminormFromConst_seq_atTop
-/
theorem seminormFromConst_isNonarchimedean (hna : IsNonarchimedean f) :
    IsNonarchimedean (seminormFromConst' c f) := fun x y => by
apply le_of_tendsto_of_tendsto' (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x + y))
    (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).max
      (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y)
  intro n
  have hmax : f ((x + y) * c ^ n) <= max (f (x * c ^ n)) (f (y * c ^ n)) := by
    simp only [add_mul, hna _ _]
  rw [le_max_iff] at hmax ⊢
  unfold seminormFromConst_seq
  apply hmax.imp <;> intro <;> gcongr

/--
theorem `seminormFromConst_isPowMul` / 定理 `seminormFromConst_isPowMul`

English:
theorem seminormFromConst_isPowMul
  statement: IsPowMul (seminormFromConst' c f)
  proof: fun x m hm => by
  simp only [seminormFromConst']
  have hlim : Tendsto (fun n => seminormFromConst_seq c f (x ^ m) (m * n)) atTop
      (𝓝 (seminormFromConst' c f (x ^ m))) := by
    apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x ^ m)).comp
      (tendsto_atTop_atTop_of_monotone (fun _ _ hnk => mul_le_mul_right hnk m) _)
    rintro n; use n; exact le_mul_of_one_le_left' hm
  apply tendsto_nhds_unique hlim
  convert! (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).pow m using 1
  ext n
  simp only [seminormFromConst_seq, div_pow, ← hpm _ hm, ← pow_mul, mul_pow, mul_comm m n]

中文:
定理 seminormFromConst_isPowMul
  结论: IsPowMul (seminormFromConst' c f)
  证明: fun x m hm => by
  simp only [seminormFromConst']
  have hlim : Tendsto (fun n => seminormFromConst_seq c f (x ^ m) (m * n)) atTop
      (𝓝 (seminormFromConst' c f (x ^ m))) := by
    apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x ^ m)).comp
      (tendsto_atTop_atTop_of_monotone (fun _ _ hnk => mul_le_mul_right hnk m) _)
    rintro n; use n; exact le_mul_of_one_le_left' hm
  apply tendsto_nhds_unique hlim
  convert! (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).pow m using 1
  ext n
  simp only [seminormFromConst_seq, div_pow, ← hpm _ hm, ← pow_mul, mul_pow, mul_comm m n]

Depends on / 依赖: Tendsto, convert, le_mul_of_one_le_left, mul_le_mul_right, seminormFromCon, seminormFromConst, seminormFromConst_seq, tendsto_atTop_atTop_of_monotone, tendsto_nhds_unique, tendsto_seminormFromConst_seq_atTop
-/
theorem seminormFromConst_isPowMul : IsPowMul (seminormFromConst' c f) := fun x m hm => by
  simp only [seminormFromConst']
  have hlim : Tendsto (fun n => seminormFromConst_seq c f (x ^ m) (m * n)) atTop
      (𝓝 (seminormFromConst' c f (x ^ m))) := by
    apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x ^ m)).comp
      (tendsto_atTop_atTop_of_monotone (fun _ _ hnk => mul_le_mul_right hnk m) _)
    rintro n; use n; exact le_mul_of_one_le_left' hm
  apply tendsto_nhds_unique hlim
  convert! (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).pow m using 1
  ext n
  simp only [seminormFromConst_seq, div_pow, ← hpm _ hm, ← pow_mul, mul_pow, mul_comm m n]

/--
theorem `seminormFromConst_le_seminorm` / 定理 `seminormFromConst_le_seminorm`

English:
theorem seminormFromConst_le_seminorm
  given: (x : R)
  statement: seminormFromConst' c f x <= f x
  proof: by
  apply le_of_tendsto (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x)
  simp only [eventually_atTop]
  use 1
  intro n hn
  rw [seminormFromConst_seq]; rw [div_le_iff₀ (by positivity)]; rw [← hpm c hn]
  exact map_mul_le_mul ..

中文:
定理 seminormFromConst_le_seminorm
  条件: (x : R)
  结论: seminormFromConst' c f x <= f x
  证明: by
  apply le_of_tendsto (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x)
  simp only [eventually_atTop]
  use 1
  intro n hn
  rw [seminormFromConst_seq]; rw [div_le_iff₀ (by positivity)]; rw [← hpm c hn]
  exact map_mul_le_mul ..

Depends on / 依赖: eventually_atTop, le_of_tendsto, map_mul_le_mul, seminormFromConst_seq, tendsto_seminormFromConst_seq_atTop
-/
theorem seminormFromConst_le_seminorm (x : R) : seminormFromConst' c f x <= f x := by
  apply le_of_tendsto (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x)
  simp only [eventually_atTop]
  use 1
  intro n hn
  rw [seminormFromConst_seq]; rw [div_le_iff₀ (by positivity)]; rw [← hpm c hn]
  exact map_mul_le_mul ..

/--
theorem `seminormFromConst_apply_of_isMul` / 定理 `seminormFromConst_apply_of_isMul`

English:
theorem seminormFromConst_apply_of_isMul
  given: {x : R} (hx : forall y : R, f (x * y) = f x * f y)
  proof: have hlim : Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (f x)) := by
    have hseq : seminormFromConst_seq c f x = fun _n => f x := by
      ext n
      by_cases hn : n = 0
      · simp only [seminormFromConst_seq, hn, pow_zero, mul_one, div_one]
      · simp only [seminormFromConst_seq, hx (c ^ n), hpm _ (Nat.one_le_iff_ne_zero.mpr hn),
          mul_div_assoc, div_self (pow_ne_zero n hc), mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x) hlim

中文:
定理 seminormFromConst_apply_of_isMul
  条件: {x : R} (hx : 对任意 y : R, f (x * y) = f x * f y)
  证明: have hlim : Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (f x)) := by
    have hseq : seminormFromConst_seq c f x = fun _n => f x := by
      ext n
      by_cases hn : n = 0
      · simp only [seminormFromConst_seq, hn, pow_zero, mul_one, div_one]
      · simp only [seminormFromConst_seq, hx (c ^ n), hpm _ (Nat.one_le_iff_ne_zero.mpr hn),
          mul_div_assoc, div_self (pow_ne_zero n hc), mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x) hlim

Depends on / 依赖: Nat.one_le_iff_ne_zero.mpr, Tendsto, div_one, div_self, mul_div_assoc, mul_one, one_le_iff_ne_zero, pow_ne_zero, pow_zero, seminormFromConst_seq, tendsto_const_nhds, tendsto_nhds_unique, tendsto_seminormFromConst_seq_atTop
-/
theorem seminormFromConst_apply_of_isMul {x : R} (hx : forall y : R, f (x * y) = f x * f y) :
    seminormFromConst' c f x = f x :=
  have hlim : Tendsto (seminormFromConst_seq c f x) atTop (𝓝 (f x)) := by
    have hseq : seminormFromConst_seq c f x = fun _n => f x := by
      ext n
      by_cases hn : n = 0
      · simp only [seminormFromConst_seq, hn, pow_zero, mul_one, div_one]
      · simp only [seminormFromConst_seq, hx (c ^ n), hpm _ (Nat.one_le_iff_ne_zero.mpr hn),
          mul_div_assoc, div_self (pow_ne_zero n hc), mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x) hlim

/--
theorem `seminormFromConst_isMul_of_isMul` / 定理 `seminormFromConst_isMul_of_isMul`

English:
theorem seminormFromConst_isMul_of_isMul
  given: {x : R} (hx : forall y : R, f (x * y) = f x * f y) (y : R)
  proof: have hlim : Tendsto (seminormFromConst_seq c f (x * y)) atTop
      (𝓝 (seminormFromConst' c f x * seminormFromConst' c f y)) := by
    rw [seminormFromConst_apply_of_isMul hf1 hc hpm hx]
    have hseq : seminormFromConst_seq c f (x * y) =
        fun n => f x * seminormFromConst_seq c f y n := by
      ext n
      simp only [seminormFromConst_seq, mul_assoc, hx, mul_div_assoc]
    simpa [hseq] using (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y).const_mul _
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x * y)) hlim

中文:
定理 seminormFromConst_isMul_of_isMul
  条件: {x : R} (hx : 对任意 y : R, f (x * y) = f x * f y) (y : R)
  证明: have hlim : Tendsto (seminormFromConst_seq c f (x * y)) atTop
      (𝓝 (seminormFromConst' c f x * seminormFromConst' c f y)) := by
    rw [seminormFromConst_apply_of_isMul hf1 hc hpm hx]
    have hseq : seminormFromConst_seq c f (x * y) =
        fun n => f x * seminormFromConst_seq c f y n := by
      ext n
      simp only [seminormFromConst_seq, mul_assoc, hx, mul_div_assoc]
    simpa [hseq] using (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y).const_mul _
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x * y)) hlim

Depends on / 依赖: Tendsto, const_mul, mul_assoc, mul_div_assoc, seminormFromConst, seminormFromConst_apply_of_isMul, seminormFromConst_seq, tendsto_nhds_unique, tendsto_seminormFromConst_seq_atTop
-/
theorem seminormFromConst_isMul_of_isMul {x : R} (hx : forall y : R, f (x * y) = f x * f y) (y : R) :
    seminormFromConst' c f (x * y) =
      seminormFromConst' c f x * seminormFromConst' c f y :=
  have hlim : Tendsto (seminormFromConst_seq c f (x * y)) atTop
      (𝓝 (seminormFromConst' c f x * seminormFromConst' c f y)) := by
    rw [seminormFromConst_apply_of_isMul hf1 hc hpm hx]
    have hseq : seminormFromConst_seq c f (x * y) =
        fun n => f x * seminormFromConst_seq c f y n := by
      ext n
      simp only [seminormFromConst_seq, mul_assoc, hx, mul_div_assoc]
    simpa [hseq] using (tendsto_seminormFromConst_seq_atTop hf1 hc hpm y).const_mul _
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (x * y)) hlim

/--
theorem `seminormFromConst_apply_c` / 定理 `seminormFromConst_apply_c`

English:
theorem seminormFromConst_apply_c
  statement: seminormFromConst' c f c = f c
  proof: have hlim : Tendsto (seminormFromConst_seq c f c) atTop (𝓝 (f c)) := by
    have hseq : seminormFromConst_seq c f c = fun _n => f c := by
      ext n
      simp only [seminormFromConst_seq]
      rw [mul_comm]; rw [← pow_succ]; rw [hpm _ le_add_self]; rw [pow_succ]; rw [mul_comm]; rw [mul_div_assoc]; rw [div_self (pow_ne_zero n hc)]; rw [mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm c) hlim

中文:
定理 seminormFromConst_apply_c
  结论: seminormFromConst' c f c = f c
  证明: have hlim : Tendsto (seminormFromConst_seq c f c) atTop (𝓝 (f c)) := by
    have hseq : seminormFromConst_seq c f c = fun _n => f c := by
      ext n
      simp only [seminormFromConst_seq]
      rw [mul_comm]; rw [← pow_succ]; rw [hpm _ le_add_self]; rw [pow_succ]; rw [mul_comm]; rw [mul_div_assoc]; rw [div_self (pow_ne_zero n hc)]; rw [mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm c) hlim

Depends on / 依赖: Tendsto, div_self, le_add_self, mul_comm, mul_div_assoc, mul_one, pow_ne_zero, pow_succ, seminormFromConst_seq, tendsto_const_nhds, tendsto_nhds_unique, tendsto_seminormFromConst_seq_atTop
-/
theorem seminormFromConst_apply_c : seminormFromConst' c f c = f c :=
  have hlim : Tendsto (seminormFromConst_seq c f c) atTop (𝓝 (f c)) := by
    have hseq : seminormFromConst_seq c f c = fun _n => f c := by
      ext n
      simp only [seminormFromConst_seq]
      rw [mul_comm]; rw [← pow_succ]; rw [hpm _ le_add_self]; rw [pow_succ]; rw [mul_comm]; rw [mul_div_assoc]; rw [div_self (pow_ne_zero n hc)]; rw [mul_one]
    rw [hseq]
    exact tendsto_const_nhds
  tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm c) hlim

/--
theorem `seminormFromConst_const_mul` / 定理 `seminormFromConst_const_mul`

English:
theorem seminormFromConst_const_mul
  given: (x : R)
  proof: by
  have hlim : Tendsto (fun n => seminormFromConst_seq c f x (n + 1)) atTop
      (𝓝 (seminormFromConst' c f x)) := by
    apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).comp
      (tendsto_atTop_atTop_of_monotone add_left_mono _)
    rintro n; use n; lia
  rw [seminormFromConst_apply_c hf1 hc hpm]
  apply tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (c * x))
  have hterm : seminormFromConst_seq c f (c * x) =
      fun n => f c * seminormFromConst_seq c f x (n + 1) := by
    simp only [seminormFromConst_seq_def]
    ext n
    ring_nf
    rw [mul_assoc _ (f c)]; rw [mul_inv_cancel₀ hc]; rw [mul_one]
  simpa [hterm] using tendsto_const_nhds.mul hlim

中文:
定理 seminormFromConst_const_mul
  条件: (x : R)
  证明: by
  have hlim : Tendsto (fun n => seminormFromConst_seq c f x (n + 1)) atTop
      (𝓝 (seminormFromConst' c f x)) := by
    apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).comp
      (tendsto_atTop_atTop_of_monotone add_left_mono _)
    rintro n; use n; lia
  rw [seminormFromConst_apply_c hf1 hc hpm]
  apply tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (c * x))
  have hterm : seminormFromConst_seq c f (c * x) =
      fun n => f c * seminormFromConst_seq c f x (n + 1) := by
    simp only [seminormFromConst_seq_def]
    ext n
    ring_nf
    rw [mul_assoc _ (f c)]; rw [mul_inv_cancel₀ hc]; rw [mul_one]
  simpa [hterm] using tendsto_const_nhds.mul hlim

Depends on / 依赖: Tendsto, add_left_mono, seminormFrom, seminormFromConst, seminormFromConst_apply_c, seminormFromConst_seq, tendsto_atTop_atTop_of_monotone, tendsto_nhds_unique, tendsto_seminormFromConst_seq_atTop
-/
theorem seminormFromConst_const_mul (x : R) :
    seminormFromConst' c f (c * x) =
      seminormFromConst' c f c * seminormFromConst' c f x := by
  have hlim : Tendsto (fun n => seminormFromConst_seq c f x (n + 1)) atTop
      (𝓝 (seminormFromConst' c f x)) := by
    apply (tendsto_seminormFromConst_seq_atTop hf1 hc hpm x).comp
      (tendsto_atTop_atTop_of_monotone add_left_mono _)
    rintro n; use n; lia
  rw [seminormFromConst_apply_c hf1 hc hpm]
  apply tendsto_nhds_unique (tendsto_seminormFromConst_seq_atTop hf1 hc hpm (c * x))
  have hterm : seminormFromConst_seq c f (c * x) =
      fun n => f c * seminormFromConst_seq c f x (n + 1) := by
    simp only [seminormFromConst_seq_def]
    ext n
    ring_nf
    rw [mul_assoc _ (f c)]; rw [mul_inv_cancel₀ hc]; rw [mul_one]
  simpa [hterm] using tendsto_const_nhds.mul hlim

end Ring

section Field

variable {K : Type*} [Field K]

/--
Definition of `normFromConst` / `normFromConst` 的定义

English:
definition normFromConst
  signature: {k : K} {g : RingSeminorm K} (hg1 : g 1 <= 1) (hg_k : g k != 0)
  body: (seminormFromConst hg1 hg_k hg_pm).toRingNorm (RingSeminorm.ne_zero_iff.mpr
    ⟨k, by rwa [seminormFromConst_def hg1 hg_k, seminormFromConst_apply_c hg1 hg_k hg_pm]⟩)

中文:
定义 normFromConst
  签名: {k : K} {g : 环半范数 K} (hg1 : g 1 <= 1) (hg_k : g k != 0)
  定义体: (seminormFromConst hg1 hg_k hg_pm).toRingNorm (RingSeminorm.ne_zero_iff.mpr
    ⟨k, by rwa [seminormFromConst_def hg1 hg_k, seminormFromConst_apply_c hg1 hg_k hg_pm]⟩)

Depends on / 依赖: RingSeminorm, RingSeminorm.ne_zero_iff.mpr, hg_k, hg_pm, ne_zero_iff, seminormFromConst, seminormFromConst_apply_c, seminormFromConst_def, toRingNorm
-/
def normFromConst {k : K} {g : RingSeminorm K} (hg1 : g 1 <= 1) (hg_k : g k != 0)
    (hg_pm : IsPowMul g) : RingNorm K :=
  (seminormFromConst hg1 hg_k hg_pm).toRingNorm (RingSeminorm.ne_zero_iff.mpr
    ⟨k, by rwa [seminormFromConst_def hg1 hg_k, seminormFromConst_apply_c hg1 hg_k hg_pm]⟩)

/--
theorem `seminormFromConstRingNormOfField_def` / 定理 `seminormFromConstRingNormOfField_def`

English:
theorem seminormFromConstRingNormOfField_def
  statement: {k : K} {g : RingSeminorm K} (hg1 : g 1 <= 1)
  proof: rfl

中文:
定理 seminormFromConstRingNormOfField_def
  结论: {k : K} {g : 环半范数 K} (hg1 : g 1 <= 1)
  证明: rfl
-/
theorem seminormFromConstRingNormOfField_def {k : K} {g : RingSeminorm K} (hg1 : g 1 <= 1)
    (hg_k : g k != 0) (hg_pm : IsPowMul g) (x : K) :
    normFromConst hg1 hg_k hg_pm x = seminormFromConst' k g x := rfl

end Field
