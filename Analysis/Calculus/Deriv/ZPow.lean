/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Derivatives of `x ^ m`, `m : ℤ`

In this file we prove theorems about (iterated) derivatives of `x ^ m`, `m : ℤ`.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`Mathlib/Analysis/Calculus/Deriv/Basic.lean`.

## Keywords

derivative, power
-/

public section

universe u v w

open Topology Filter Asymptotics Set
open scoped Nat

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {x : 𝕜}
variable {s : Set 𝕜}
variable {m : Int}


/--
theorem `hasStrictDerivAt_zpow` / 定理 `hasStrictDerivAt_zpow`

English:
theorem hasStrictDerivAt_zpow
  given: (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
  proof: by
  have : forall m : Int, 0 < m -> HasStrictDerivAt (· ^ m) ((m : 𝕜) * x ^ (m - 1)) x := fun m hm => by
    lift m to Nat using hm.le
    simp only [zpow_natCast, Int.cast_natCast]
    convert hasStrictDerivAt_pow m x
    rw [← Int.ofNat_one]; rw [← Int.ofNat_sub]; rw [zpow_natCast]
    norm_cast 

中文:
定理 hasStrictDerivAt_zpow
  条件: (m : 整数) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
  证明: by
  have : forall m : Int, 0 < m -> HasStrictDerivAt (· ^ m) ((m : 𝕜) * x ^ (m - 1)) x := fun m hm => by
    lift m to Nat using hm.le
    simp only [zpow_natCast, Int.cast_natCast]
    convert hasStrictDerivAt_pow m x
    rw [← Int.ofNat_one]; rw [← Int.ofNat_sub]; rw [zpow_natCast]
    norm_cast 

Depends on / 依赖: Functio, HasStrictDerivAt, Int.cast_natCast, Int.ofNat_one, Int.ofNat_sub, cast_natCast, convert, h.resolve_right, hasStrictDerivAt_inv, hasStrictDerivAt_pow, hm.le, hm.not_ge, lt_trichotomy, neg_pos, not_ge, ofNat_one, ofNat_sub, resolve_right, zpow_natCast, zpow_ne_zero
-/
theorem hasStrictDerivAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m) :
    HasStrictDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x := by
  have : forall m : Int, 0 < m -> HasStrictDerivAt (· ^ m) ((m : 𝕜) * x ^ (m - 1)) x := fun m hm => by
    lift m to Nat using hm.le
    simp only [zpow_natCast, Int.cast_natCast]
    convert hasStrictDerivAt_pow m x
    rw [← Int.ofNat_one]; rw [← Int.ofNat_sub]; rw [zpow_natCast]
    norm_cast at hm
  rcases lt_trichotomy m 0 with (hm | hm | hm)
  · have hx : x != 0 := h.resolve_right hm.not_ge
    have := (hasStrictDerivAt_inv ?_).scomp _ (this (-m) (neg_pos.2 hm)) <;>
      [skip; exact zpow_ne_zero _ hx]
    simp only [Function.comp_def, zpow_neg, inv_inv, smul_eq_mul] at this
    convert! this using 1
    rw [sq]; rw [mul_inv]; rw [inv_inv]; rw [Int.cast_neg]; rw [neg_mul]; rw [neg_mul_neg]; rw [← zpow_add₀ hx]; rw [mul_assoc]; rw [←
      zpow_add₀ hx]
    congr
    abel
  · simp only [hm, zpow_zero, Int.cast_zero, zero_mul, hasStrictDerivAt_const]
  · exact this m hm

/--
theorem `hasDerivAt_zpow` / 定理 `hasDerivAt_zpow`

English:
theorem hasDerivAt_zpow
  given: (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
  proof: (hasStrictDerivAt_zpow m x h).hasDerivAt

中文:
定理 hasDerivAt_zpow
  条件: (m : 整数) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
  证明: (hasStrictDerivAt_zpow m x h).hasDerivAt

Depends on / 依赖: hasDerivAt, hasStrictDerivAt_zpow
-/
theorem hasDerivAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m) :
    HasDerivAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) x :=
  (hasStrictDerivAt_zpow m x h).hasDerivAt

/--
theorem `hasDerivWithinAt_zpow` / 定理 `hasDerivWithinAt_zpow`

English:
theorem hasDerivWithinAt_zpow
  given: (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m) (s : Set 𝕜)
  proof: (hasDerivAt_zpow m x h).hasDerivWithinAt

中文:
定理 hasDerivWithinAt_zpow
  条件: (m : 整数) (x : 𝕜) (h : x != 0 ∨ 0 <= m) (s : Set 𝕜)
  证明: (hasDerivAt_zpow m x h).hasDerivWithinAt

Depends on / 依赖: hasDerivAt_zpow, hasDerivWithinAt
-/
theorem hasDerivWithinAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m) (s : Set 𝕜) :
    HasDerivWithinAt (fun x => x ^ m) ((m : 𝕜) * x ^ (m - 1)) s x :=
  (hasDerivAt_zpow m x h).hasDerivWithinAt

/--
theorem `differentiableAt_zpow` / 定理 `differentiableAt_zpow`

English:
theorem differentiableAt_zpow
  statement: DifferentiableAt 𝕜 (fun x => x ^ m) x ↔ x != 0 ∨ 0 <= m
  proof: ⟨fun H => NormedField.continuousAt_zpow.1 H.continuousAt, fun H =>
    (hasDerivAt_zpow m x H).differentiableAt⟩

中文:
定理 differentiableAt_zpow
  结论: DifferentiableAt 𝕜 (fun x => x ^ m) x ↔ x != 0 ∨ 0 <= m
  证明: ⟨fun H => NormedField.continuousAt_zpow.1 H.continuousAt, fun H =>
    (hasDerivAt_zpow m x H).differentiableAt⟩

Depends on / 依赖: H.continuousAt, NormedField, NormedField.continuousAt_zpow, continuousAt, continuousAt_zpow, differentiableAt, hasDerivAt_zpow
-/
theorem differentiableAt_zpow : DifferentiableAt 𝕜 (fun x => x ^ m) x ↔ x != 0 ∨ 0 <= m :=
  ⟨fun H => NormedField.continuousAt_zpow.1 H.continuousAt, fun H =>
    (hasDerivAt_zpow m x H).differentiableAt⟩

/--
theorem `differentiableWithinAt_zpow` / 定理 `differentiableWithinAt_zpow`

English:
theorem differentiableWithinAt_zpow
  given: (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
  proof: (differentiableAt_zpow.mpr h).differentiableWithinAt

中文:
定理 differentiableWithinAt_zpow
  条件: (m : 整数) (x : 𝕜) (h : x != 0 ∨ 0 <= m)
  证明: (differentiableAt_zpow.mpr h).differentiableWithinAt

Depends on / 依赖: differentiableAt_zpow, differentiableAt_zpow.mpr, differentiableWithinAt
-/
theorem differentiableWithinAt_zpow (m : Int) (x : 𝕜) (h : x != 0 ∨ 0 <= m) :
    DifferentiableWithinAt 𝕜 (fun x => x ^ m) s x :=
  (differentiableAt_zpow.mpr h).differentiableWithinAt

/--
theorem `differentiableOn_zpow` / 定理 `differentiableOn_zpow`

English:
theorem differentiableOn_zpow
  given: (m : Int) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 <= m)
  proof: fun x hxs =>
differentiableWithinAt_zpow m x h.imp_left ne_of_mem_of_not_mem hxs

中文:
定理 differentiableOn_zpow
  条件: (m : 整数) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 <= m)
  证明: fun x hxs =>
differentiableWithinAt_zpow m x h.imp_left ne_of_mem_of_not_mem hxs
-/
theorem differentiableOn_zpow (m : Int) (s : Set 𝕜) (h : (0 : 𝕜) ∉ s ∨ 0 <= m) :
    DifferentiableOn 𝕜 (fun x => x ^ m) s := fun x hxs =>
differentiableWithinAt_zpow m x h.imp_left ne_of_mem_of_not_mem hxs

/--
theorem `deriv_zpow` / 定理 `deriv_zpow`

English:
theorem deriv_zpow
  given: (m : Int) (x : 𝕜)
  statement: deriv (fun x => x ^ m) x = m * x ^ (m - 1)
  proof: by
  by_cases H : x != 0 ∨ 0 <= m
  · exact (hasDerivAt_zpow m x H).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_zpow.1 H)]
    push Not at H
    rcases H with ⟨rfl, hm⟩
    rw [zero_zpow _ ((sub_one_lt _).trans hm).ne]; rw [mul_zero]

@[simp]

中文:
定理 deriv_zpow
  条件: (m : 整数) (x : 𝕜)
  结论: deriv (fun x => x ^ m) x = m * x ^ (m - 1)
  证明: by
  by_cases H : x != 0 ∨ 0 <= m
  · exact (hasDerivAt_zpow m x H).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_zpow.1 H)]
    push Not at H
    rcases H with ⟨rfl, hm⟩
    rw [zero_zpow _ ((sub_one_lt _).trans hm).ne]; rw [mul_zero]

@[simp]

Depends on / 依赖: deriv_zero_of_not_differentiableAt, differentiableAt_zpow, hasDerivAt_zpow, mul_zero, sub_one_lt, zero_zpow
-/
theorem deriv_zpow (m : Int) (x : 𝕜) : deriv (fun x => x ^ m) x = m * x ^ (m - 1) := by
  by_cases H : x != 0 ∨ 0 <= m
  · exact (hasDerivAt_zpow m x H).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_zpow.1 H)]
    push Not at H
    rcases H with ⟨rfl, hm⟩
    rw [zero_zpow _ ((sub_one_lt _).trans hm).ne]; rw [mul_zero]

@[simp]
/--
theorem `deriv_zpow'` / 定理 `deriv_zpow'`

English:
theorem deriv_zpow'
  given: (m : Int)
  statement: (deriv fun x : 𝕜 => x ^ m) = fun x => (m : 𝕜) * x ^ (m - 1)
  proof: funext deriv_zpow m

中文:
定理 deriv_zpow'
  条件: (m : 整数)
  结论: (deriv fun x : 𝕜 => x ^ m) = fun x => (m : 𝕜) * x ^ (m - 1)
  证明: funext deriv_zpow m

Depends on / 依赖: deriv_zpow
-/
theorem deriv_zpow' (m : Int) : (deriv fun x : 𝕜 => x ^ m) = fun x => (m : 𝕜) * x ^ (m - 1) :=
funext deriv_zpow m

/--
theorem `derivWithin_zpow` / 定理 `derivWithin_zpow`

English:
theorem derivWithin_zpow
  given: (hxs : UniqueDiffWithinAt 𝕜 s x) (h : x != 0 ∨ 0 <= m)
  proof: (hasDerivWithinAt_zpow m x h s).derivWithin hxs

@[simp]

中文:
定理 derivWithin_zpow
  条件: (hxs : UniqueDiffWithinAt 𝕜 s x) (h : x != 0 ∨ 0 <= m)
  证明: (hasDerivWithinAt_zpow m x h s).derivWithin hxs

@[simp]

Depends on / 依赖: derivWithin, hasDerivWithinAt_zpow
-/
theorem derivWithin_zpow (hxs : UniqueDiffWithinAt 𝕜 s x) (h : x != 0 ∨ 0 <= m) :
    derivWithin (fun x => x ^ m) s x = (m : 𝕜) * x ^ (m - 1) :=
  (hasDerivWithinAt_zpow m x h s).derivWithin hxs

@[simp]
/--
theorem `iter_deriv_zpow'` / 定理 `iter_deriv_zpow'`

English:
theorem iter_deriv_zpow'
  given: (m : Int) (k : Nat)
  proof: by
  induction k with
  | zero =>
    simp only [one_mul, Int.ofNat_zero, id, sub_zero, Finset.prod_range_zero, Function.iterate_zero]
  | succ k ihk =>
    simp only [Function.iterate_succ_apply', ihk, deriv_const_mul_field', deriv_zpow',
      Finset.prod_range_succ, Int.natCast_succ, ← sub_sub, I

中文:
定理 iter_deriv_zpow'
  条件: (m : 整数) (k : 自然数)
  证明: by
  induction k with
  | zero =>
    simp only [one_mul, Int.ofNat_zero, id, sub_zero, Finset.prod_range_zero, Function.iterate_zero]
  | succ k ihk =>
    simp only [Function.iterate_succ_apply', ihk, deriv_const_mul_field', deriv_zpow',
      Finset.prod_range_succ, Int.natCast_succ, ← sub_sub, I

Depends on / 依赖: Finset, Finset.prod_range_succ, Finset.prod_range_zero, Function, Function.iterate_succ_apply, Function.iterate_zero, Int.cast_natCast, Int.cast_sub, Int.natCast_succ, Int.ofNat_zero, cast_natCast, cast_sub, deriv_const_mul_field, deriv_zpow, iterate_succ_apply, iterate_zero, mul_assoc, natCast_succ, ofNat_zero, one_mul
-/
theorem iter_deriv_zpow' (m : Int) (k : Nat) :
    (deriv^[k] fun x : 𝕜 => x ^ m) =
      fun x => (∏ i in Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k) := by
  induction k with
  | zero =>
    simp only [one_mul, Int.ofNat_zero, id, sub_zero, Finset.prod_range_zero, Function.iterate_zero]
  | succ k ihk =>
    simp only [Function.iterate_succ_apply', ihk, deriv_const_mul_field', deriv_zpow',
      Finset.prod_range_succ, Int.natCast_succ, ← sub_sub, Int.cast_sub, Int.cast_natCast,
      mul_assoc]

/--
theorem `iter_deriv_zpow` / 定理 `iter_deriv_zpow`

English:
theorem iter_deriv_zpow
  given: (m : Int) (x : 𝕜) (k : Nat)
  proof: congr_fun (iter_deriv_zpow' m k) x

中文:
定理 iter_deriv_zpow
  条件: (m : 整数) (x : 𝕜) (k : 自然数)
  证明: congr_fun (iter_deriv_zpow' m k) x

Depends on / 依赖: congr_fun, iter_deriv_zpow
-/
theorem iter_deriv_zpow (m : Int) (x : 𝕜) (k : Nat) :
    deriv^[k] (fun y => y ^ m) x = (∏ i in Finset.range k, ((m : 𝕜) - i)) * x ^ (m - k) :=
  congr_fun (iter_deriv_zpow' m k) x

/--
theorem `iter_deriv_pow` / 定理 `iter_deriv_pow`

English:
theorem iter_deriv_pow
  given: (n : Nat) (x : 𝕜) (k : Nat)
  proof: by
  simp only [← zpow_natCast, iter_deriv_zpow, Int.cast_natCast]
  rcases le_or_gt k n with hkn | hnk
  · rw [Int.ofNat_sub hkn]
  · have : (∏ i in Finset.range k, (n - i : 𝕜)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hnk) (sub_self _)
    simp only [this, zero_mul]

@[simp]

中文:
定理 iter_deriv_pow
  条件: (n : 自然数) (x : 𝕜) (k : 自然数)
  证明: by
  simp only [← zpow_natCast, iter_deriv_zpow, Int.cast_natCast]
  rcases le_or_gt k n with hkn | hnk
  · rw [Int.ofNat_sub hkn]
  · have : (∏ i in Finset.range k, (n - i : 𝕜)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hnk) (sub_self _)
    simp only [this, zero_mul]

@[simp]

Depends on / 依赖: Finset, Finset.mem_range, Finset.prod_eq_zero, Finset.range, Int.cast_natCast, Int.ofNat_sub, cast_natCast, iter_deriv_zpow, le_or_gt, mem_range, ofNat_sub, prod_eq_zero, sub_self, zero_mul, zpow_natCast
-/
theorem iter_deriv_pow (n : Nat) (x : 𝕜) (k : Nat) :
    deriv^[k] (fun x : 𝕜 => x ^ n) x = (∏ i in Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k) := by
  simp only [← zpow_natCast, iter_deriv_zpow, Int.cast_natCast]
  rcases le_or_gt k n with hkn | hnk
  · rw [Int.ofNat_sub hkn]
  · have : (∏ i in Finset.range k, (n - i : 𝕜)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hnk) (sub_self _)
    simp only [this, zero_mul]

@[simp]
/--
theorem `iter_deriv_pow'` / 定理 `iter_deriv_pow'`

English:
theorem iter_deriv_pow'
  given: (n k : Nat)
  proof: funext fun x => iter_deriv_pow n x k

中文:
定理 iter_deriv_pow'
  条件: (n k : 自然数)
  证明: funext fun x => iter_deriv_pow n x k

Depends on / 依赖: iter_deriv_pow
-/
theorem iter_deriv_pow' (n k : Nat) :
    (deriv^[k] fun x : 𝕜 => x ^ n) =
      fun x => (∏ i in Finset.range k, ((n : 𝕜) - i)) * x ^ (n - k) :=
  funext fun x => iter_deriv_pow n x k

/--
theorem `iter_deriv_inv` / 定理 `iter_deriv_inv`

English:
theorem iter_deriv_inv
  given: (k : Nat) (x : 𝕜)
  proof: calc
  deriv^[k] Inv.inv x = deriv^[k] (· ^ (-1 : Int)) x := by simp
  _ = (∏ i in Finset.range k, (-1 - i : 𝕜)) * x ^ (-1 - k : Int) := mod_cast iter_deriv_zpow (-1) x k
  _ = (-1) ^ k * k ! * x ^ (-1 - k : Int) := by
    simp only [← neg_add', Finset.prod_neg, ← Finset.prod_Ico_id_eq_factorial,
  

中文:
定理 iter_deriv_inv
  条件: (k : 自然数) (x : 𝕜)
  证明: calc
  deriv^[k] Inv.inv x = deriv^[k] (· ^ (-1 : Int)) x := by simp
  _ = (∏ i in Finset.range k, (-1 - i : 𝕜)) * x ^ (-1 - k : Int) := mod_cast iter_deriv_zpow (-1) x k
  _ = (-1) ^ k * k ! * x ^ (-1 - k : Int) := by
    simp only [← neg_add', Finset.prod_neg, ← Finset.prod_Ico_id_eq_factorial,
  
-/
theorem iter_deriv_inv (k : Nat) (x : 𝕜) :
    deriv^[k] Inv.inv x = (-1) ^ k * k ! * x ^ (-1 - k : Int) := calc
  deriv^[k] Inv.inv x = deriv^[k] (· ^ (-1 : Int)) x := by simp
  _ = (∏ i in Finset.range k, (-1 - i : 𝕜)) * x ^ (-1 - k : Int) := mod_cast iter_deriv_zpow (-1) x k
  _ = (-1) ^ k * k ! * x ^ (-1 - k : Int) := by
    simp only [← neg_add', Finset.prod_neg, ← Finset.prod_Ico_id_eq_factorial,
      Finset.prod_Ico_eq_prod_range]
    simp

@[simp]
/--
theorem `iter_deriv_inv'` / 定理 `iter_deriv_inv'`

English:
theorem iter_deriv_inv'
  given: (k : Nat)
  proof: funext (iter_deriv_inv k)

中文:
定理 iter_deriv_inv'
  条件: (k : 自然数)
  证明: funext (iter_deriv_inv k)

Depends on / 依赖: iter_deriv_inv
-/
theorem iter_deriv_inv' (k : Nat) :
    deriv^[k] Inv.inv = fun x : 𝕜 => (-1) ^ k * k ! * x ^ (-1 - k : Int) :=
  funext (iter_deriv_inv k)

open Nat Function in
/--
theorem `iter_deriv_inv_linear` / 定理 `iter_deriv_inv_linear`

English:
theorem iter_deriv_inv_linear
  given: (k : Nat) (c d : 𝕜)
  proof: by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [factorial_succ]; rw [add_comm k 1]; rw [iterate_add_apply]; rw [ihk]
    ext z
    simp only [Int.reduceNeg, iterate_one, deriv_const_mul_field', cast_add, cast_one]
    by_cases hd : c = 0
    · simp [hd]
    · have := deriv_comp_add_

中文:
定理 iter_deriv_inv_linear
  条件: (k : 自然数) (c d : 𝕜)
  证明: by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [factorial_succ]; rw [add_comm k 1]; rw [iterate_add_apply]; rw [ihk]
    ext z
    simp only [Int.reduceNeg, iterate_one, deriv_const_mul_field', cast_add, cast_one]
    by_cases hd : c = 0
    · simp [hd]
    · have := deriv_comp_add_

Depends on / 依赖: Int.reduceNeg, add_comm, cast_add, cast_one, deriv_comp_add_const, deriv_comp_mul_left, deriv_const_mul_field, factorial_succ, iterate_add_apply, iterate_one, reduceNeg
-/
theorem iter_deriv_inv_linear (k : Nat) (c d : 𝕜) :
    deriv^[k] (fun x => (c * x + d)⁻¹) =
    (fun x : 𝕜 => (-1) ^ k * k ! * c ^ k * (c * x + d) ^ (-1 - k : Int)) := by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [factorial_succ]; rw [add_comm k 1]; rw [iterate_add_apply]; rw [ihk]
    ext z
    simp only [Int.reduceNeg, iterate_one, deriv_const_mul_field', cast_add, cast_one]
    by_cases hd : c = 0
    · simp [hd]
    · have := deriv_comp_add_const (fun x => (c * x) ^ (-1 - k : Int)) (d / c) z
      have h0 : (fun x => (c * (x + d / c)) ^ (-1 - (k : Int))) =
        (fun x => (c * x + d) ^ (-1 - (k : Int))) := by
        ext y
        field_simp
      rw [h0]; rw [deriv_comp_mul_left c (fun x => (x) ^ (-1 - k : Int)) (z + d / c)] at this
      simp [this]
      field_simp
      ring_nf

/--
theorem `iter_deriv_inv_linear_sub` / 定理 `iter_deriv_inv_linear_sub`

English:
theorem iter_deriv_inv_linear_sub
  given: (k : Nat) (c d : 𝕜)
  proof: by
  simpa [sub_eq_add_neg] using iter_deriv_inv_linear k c (-d)

中文:
定理 iter_deriv_inv_linear_sub
  条件: (k : 自然数) (c d : 𝕜)
  证明: by
  simpa [sub_eq_add_neg] using iter_deriv_inv_linear k c (-d)

Depends on / 依赖: iter_deriv_inv_linear, sub_eq_add_neg
-/
theorem iter_deriv_inv_linear_sub (k : Nat) (c d : 𝕜) :
    deriv^[k] (fun x => (c * x - d)⁻¹) =
    (fun x : 𝕜 => (-1) ^ k * k ! * c ^ k * (c * x - d) ^ (-1 - k : Int)) := by
  simpa [sub_eq_add_neg] using iter_deriv_inv_linear k c (-d)

variable {f : E -> 𝕜} {t : Set E} {a : E}

@[fun_prop]
/--
theorem `DifferentiableWithinAt.zpow` / 定理 `DifferentiableWithinAt.zpow`

English:
theorem DifferentiableWithinAt.zpow
  given: (hf : DifferentiableWithinAt 𝕜 f t a) (h : f a != 0 ∨ 0 <= m)
  proof: (differentiableAt_zpow.2 h).comp_differentiableWithinAt a hf

@[fun_prop]

中文:
定理 DifferentiableWithinAt.zpow
  条件: (hf : DifferentiableWithinAt 𝕜 f t a) (h : f a != 0 ∨ 0 <= m)
  证明: (differentiableAt_zpow.2 h).comp_differentiableWithinAt a hf

@[fun_prop]

Depends on / 依赖: comp_differentiableWithinAt, differentiableAt_zpow
-/
theorem DifferentiableWithinAt.zpow (hf : DifferentiableWithinAt 𝕜 f t a) (h : f a != 0 ∨ 0 <= m) :
    DifferentiableWithinAt 𝕜 (fun x => f x ^ m) t a :=
  (differentiableAt_zpow.2 h).comp_differentiableWithinAt a hf

@[fun_prop]
/--
theorem `DifferentiableAt.zpow` / 定理 `DifferentiableAt.zpow`

English:
theorem DifferentiableAt.zpow
  given: (hf : DifferentiableAt 𝕜 f a) (h : f a != 0 ∨ 0 <= m)
  proof: (differentiableAt_zpow.2 h).comp a hf

@[fun_prop]

中文:
定理 DifferentiableAt.zpow
  条件: (hf : DifferentiableAt 𝕜 f a) (h : f a != 0 ∨ 0 <= m)
  证明: (differentiableAt_zpow.2 h).comp a hf

@[fun_prop]

Depends on / 依赖: differentiableAt_zpow
-/
theorem DifferentiableAt.zpow (hf : DifferentiableAt 𝕜 f a) (h : f a != 0 ∨ 0 <= m) :
    DifferentiableAt 𝕜 (fun x => f x ^ m) a :=
  (differentiableAt_zpow.2 h).comp a hf

@[fun_prop]
/--
theorem `DifferentiableOn.zpow` / 定理 `DifferentiableOn.zpow`

English:
theorem DifferentiableOn.zpow
  given: (hf : DifferentiableOn 𝕜 f t) (h : (forall x in t, f x != 0) ∨ 0 <= m)
  proof: fun x hx =>
(hf x hx).zpow h.imp_left fun h => h x hx

@[fun_prop]

中文:
定理 DifferentiableOn.zpow
  条件: (hf : DifferentiableOn 𝕜 f t) (h : (对任意 x in t, f x != 0) ∨ 0 <= m)
  证明: fun x hx =>
(hf x hx).zpow h.imp_left fun h => h x hx

@[fun_prop]
-/
theorem DifferentiableOn.zpow (hf : DifferentiableOn 𝕜 f t) (h : (forall x in t, f x != 0) ∨ 0 <= m) :
    DifferentiableOn 𝕜 (fun x => f x ^ m) t := fun x hx =>
(hf x hx).zpow h.imp_left fun h => h x hx

@[fun_prop]
/--
theorem `Differentiable.zpow` / 定理 `Differentiable.zpow`

English:
theorem Differentiable.zpow
  given: (hf : Differentiable 𝕜 f) (h : (forall x, f x != 0) ∨ 0 <= m)
  proof: fun x => (hf x).zpow h.imp_left fun h => h x

中文:
定理 Differentiable.zpow
  条件: (hf : Differentiable 𝕜 f) (h : (对任意 x, f x != 0) ∨ 0 <= m)
  证明: fun x => (hf x).zpow h.imp_left fun h => h x

Depends on / 依赖: h.imp_left, imp_left
-/
theorem Differentiable.zpow (hf : Differentiable 𝕜 f) (h : (forall x, f x != 0) ∨ 0 <= m) :
Differentiable 𝕜 fun x => f x ^ m := fun x => (hf x).zpow h.imp_left fun h => h x
