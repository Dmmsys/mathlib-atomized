/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Tactic.Positivity.Core

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.IsNonarchimedean
import Mathlib.Data.Fintype.Order
import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Basic theory of heights

This is an attempt at formalizing some basic properties of height functions.

We aim at a level of generality that allows to apply the theory to algebraic number fields
and to function fields (and possibly beyond).

The general set-up for heights is the following. Let `K` be a field.
* We have a `Multiset` of archimedean absolute values on `K` (with values in `ℝ`).
* We also have a `Set` of non-archimedean (i.e., `|x+y| ≤ max |x| |y|`) absolute values.
* For a given `x ≠ 0` in `K`, `|x|ᵥ = 1` for all but finitely many (non-archimedean) `v`.
* We have the *product formula* `∏ v : arch, |x|ᵥ * ∏ v : nonarch, |x|ᵥ = 1`
  for all `x ≠ 0` in `K`, where the first product is over the multiset of archimedean
  absolute values.

We realize this implementation via the class `Height.AdmissibleAbsValues K`.

## Main definitions

We define *multiplicative heights* and *logarithmic heights* (which are just defined to
be the (real) logarithm of the corresponding multiplicative height). This leads to some
duplication (in the definitions and statements; the proofs are reduced to those for the
multiplicative height), which is justified, as both versions are frequently used.

We define the following variants.
* `Height.mulHeight₁ x` and `Height.logHeight₁ x` for `x : K`.
  This is the height of an element of `K`.
* `Height.mulHeight x` and `Height.logHeight x` for `x : ι → K` with `ι` finite. This is the height
  of a tuple of elements of `K` representing a point in projective space. When `x = 0`, we
  define the multiplicative height to be `1` (so the logarithmic height is `0`).
  It is invariant under scaling by nonzero elements of `K`.
* `Finsupp.mulHeight x` and `Finsupp.logHeight x` for `x : α →₀ K`. This is the same
  as the height of `x` restricted to the support of `x`.

## TODO

* Add `Height.AdmissibleAbsValues` instances for
  * Fields of rational functions in `n` variables and
  * Finite extensions of fields with `Height.AdmissibleAbsValues`.

* Prove upper and lower bounds on the height of the image of a tuple under a tuple
  of homogeneous polynomial maps of the same degree.

## Tags

Height, absolute value

-/

@[expose] public noncomputable section

namespace Height

/-!
### Families of admissible absolute values

We define the class `AdmissibleAbsValues K` for a field `K`, which captures the notion of a
family of absolute values on `K` satisfying a product formula.
-/

/--
Definition of `AdmissibleAbsValues` / `AdmissibleAbsValues` 的定义

English:
class AdmissibleAbsValues
  parameters: (K : Type*) [Field K]
  axioms and operations (5):
    - archAbsVal : Multiset (AbsoluteValue K Real)
    - nonarchAbsVal : Set (AbsoluteValue K Real)
    - isNonarchimedean : forall v in nonarchAbsVal, IsNonarchimedean v
    - hasFiniteMulSupport({x : K} (_ : x != 0)) : (fun v : nonarchAbsVal => v.val x).HasFiniteMulSupport
    - product_formula({x : K} (_ : x != 0)) : (archAbsVal.map (· x)).prod * ∏ᶠ v : nonarchAbsVal, v.val x = 1

中文:
类 AdmissibleAbsValues
  参数: (K : 类型) [域 K]
  公理与运算 (5 个):
    - archAbsVal : Multiset (绝对值 K 实数)
    - nonarchAbsVal : 集合 (绝对值 K 实数)
    - isNonarchimedean : 对任意 v in nonarchAbsVal, IsNonarchimedean v
    - hasFiniteMulSupport({x : K} (_ : x != 0)) : (fun v : nonarchAbsVal => v.val x).HasFiniteMulSupport
    - product_formula({x : K} (_ : x != 0)) : (archAbsVal.map (· x)).乘积 * ∏ᶠ v : nonarchAbsVal, v.val x = 1
-/
class AdmissibleAbsValues (K : Type*) [Field K] where
  /-- The archimedean absolute values as a multiset of `ℝ`-valued absolute values on `K`. -/
  archAbsVal : Multiset (AbsoluteValue K Real)
  /-- The nonarchimedean absolute values as a set of `ℝ`-valued absolute values on `K`. -/
  nonarchAbsVal : Set (AbsoluteValue K Real)
  /-- The nonarchimedean absolute values are indeed nonarchimedean. -/
  isNonarchimedean : forall v in nonarchAbsVal, IsNonarchimedean v
  /-- Only finitely many (nonarchimedean) absolute values are `≠ 1` for any nonzero `x : K`. -/
  hasFiniteMulSupport {x : K} (_ : x != 0) : (fun v : nonarchAbsVal => v.val x).HasFiniteMulSupport
  /-- The product formula. The archimedean absolute values are taken with their multiplicity. -/
  product_formula {x : K} (_ : x != 0) :
      (archAbsVal.map (· x)).prod * ∏ᶠ v : nonarchAbsVal, v.val x = 1

open AdmissibleAbsValues Real Function

@[deprecated (since := "2026-03-03")] alias
  AdmissibleAbsValues.mulSupport_finite := AdmissibleAbsValues.hasFiniteMulSupport

attribute [fun_prop] hasFiniteMulSupport

variable (K : Type*) [Field K] [AdmissibleAbsValues K]

/-- The `totalWeight` of a field with `AdmissibleAbsValues` is the sum of the multiplicities of
the archimedean places. -/
.card def totalWeight : Nat := archAbsVal (K := K)

variable {K}

/-!
### Heights of field elements

We use the subscript `₁` to denote multiplicative and logarithmic heights of field elements
(this is because we are in the one-dimensional case of (affine) heights).
-/

/--
Definition of `mulHeight₁` / `mulHeight₁` 的定义

English:
definition mulHeight₁
  signature: (x : K)
  body: (archAbsVal.map fun v => max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1

中文:
定义 mulHeight₁
  签名: (x : K)
  定义体: (archAbsVal.map fun v => max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1

Depends on / 依赖: archAbsVal, archAbsVal.map, nonarchAbsVal, v.val
-/
def mulHeight₁ (x : K) : Real :=
  (archAbsVal.map fun v => max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1

/--
lemma `mulHeight₁_eq` / 引理 `mulHeight₁_eq`

English:
lemma mulHeight₁_eq
  given: (x : K)
  proof: rfl

@[simp]

中文:
引理 mulHeight₁_eq
  条件: (x : K)
  证明: rfl

@[simp]
-/
lemma mulHeight₁_eq (x : K) :
    mulHeight₁ x =
      (archAbsVal.map fun v => max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1 :=
  rfl

@[simp]
/--
lemma `mulHeight₁_zero` / 引理 `mulHeight₁_zero`

English:
lemma mulHeight₁_zero
  statement: mulHeight₁ (0 : K) = 1
  proof: by
  simp [mulHeight₁_eq]

@[simp]

中文:
引理 mulHeight₁_zero
  结论: mulHeight₁ (0 : K) = 1
  证明: by
  simp [mulHeight₁_eq]

@[simp]
-/
lemma mulHeight₁_zero : mulHeight₁ (0 : K) = 1 := by
  simp [mulHeight₁_eq]

@[simp]
/--
lemma `mulHeight₁_one` / 引理 `mulHeight₁_one`

English:
lemma mulHeight₁_one
  statement: mulHeight₁ (1 : K) = 1
  proof: by
  simp [mulHeight₁_eq]

中文:
引理 mulHeight₁_one
  结论: mulHeight₁ (1 : K) = 1
  证明: by
  simp [mulHeight₁_eq]
-/
lemma mulHeight₁_one : mulHeight₁ (1 : K) = 1 := by
  simp [mulHeight₁_eq]

/--
lemma `one_le_mulHeight₁` / 引理 `one_le_mulHeight₁`

English:
lemma one_le_mulHeight₁
  given: (x : K)
  statement: 1 <= mulHeight₁ x
  proof: one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod_map fun _ _ => le_max_right ..)
    one_le_finprod fun _ => le_max_right ..

中文:
引理 one_le_mulHeight₁
  条件: (x : K)
  结论: 1 <= mulHeight₁ x
  证明: one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod_map fun _ _ => le_max_right ..)
    one_le_finprod fun _ => le_max_right ..

Depends on / 依赖: Multiset, Multiset.one_le_prod_map, le_max_right, one_le_finprod, one_le_mul_of_one_le_of_one_le, one_le_prod_map
-/
lemma one_le_mulHeight₁ (x : K) : 1 <= mulHeight₁ x :=
one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod_map fun _ _ => le_max_right ..)
    one_le_finprod fun _ => le_max_right ..

-- This is needed as a side condition in proofs about logarithmic heights
/--
lemma `mulHeight₁_pos` / 引理 `mulHeight₁_pos`

English:
lemma mulHeight₁_pos
  given: (x : K)
  statement: 0 < mulHeight₁ x
  proof: zero_lt_one.trans_le one_le_mulHeight₁ x

中文:
引理 mulHeight₁_pos
  条件: (x : K)
  结论: 0 < mulHeight₁ x
  证明: zero_lt_one.trans_le one_le_mulHeight₁ x

Depends on / 依赖: trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma mulHeight₁_pos (x : K) : 0 < mulHeight₁ x :=
zero_lt_one.trans_le one_le_mulHeight₁ x

-- This is needed as a side condition in proofs about logarithmic heights
/--
lemma `mulHeight₁_ne_zero` / 引理 `mulHeight₁_ne_zero`

English:
lemma mulHeight₁_ne_zero
  given: (x : K)
  statement: mulHeight₁ x != 0
  proof: (mulHeight₁_pos x).ne'

中文:
引理 mulHeight₁_ne_zero
  条件: (x : K)
  结论: mulHeight₁ x != 0
  证明: (mulHeight₁_pos x).ne'
-/
lemma mulHeight₁_ne_zero (x : K) : mulHeight₁ x != 0 :=
  (mulHeight₁_pos x).ne'

/--
lemma `mulHeight₁_nonneg` / 引理 `mulHeight₁_nonneg`

English:
lemma mulHeight₁_nonneg
  given: (x : K)
  statement: 0 <= mulHeight₁ x
  proof: (mulHeight₁_pos x).le

中文:
引理 mulHeight₁_nonneg
  条件: (x : K)
  结论: 0 <= mulHeight₁ x
  证明: (mulHeight₁_pos x).le
-/
lemma mulHeight₁_nonneg (x : K) : 0 <= mulHeight₁ x :=
  (mulHeight₁_pos x).le

/--
Definition of `logHeight₁` / `logHeight₁` 的定义

English:
definition logHeight₁
  signature: (x : K)
  body: log (mulHeight₁ x)

中文:
定义 logHeight₁
  签名: (x : K)
  定义体: log (mulHeight₁ x)
-/
def logHeight₁ (x : K) : Real := log (mulHeight₁ x)

/--
lemma `logHeight₁_eq_log_mulHeight₁` / 引理 `logHeight₁_eq_log_mulHeight₁`

English:
lemma logHeight₁_eq_log_mulHeight₁
  given: (x : K)
  statement: logHeight₁ x = log (mulHeight₁ x)
  proof: rfl

@[simp]

中文:
引理 logHeight₁_eq_log_mulHeight₁
  条件: (x : K)
  结论: logHeight₁ x = log (mulHeight₁ x)
  证明: rfl

@[simp]
-/
lemma logHeight₁_eq_log_mulHeight₁ (x : K) : logHeight₁ x = log (mulHeight₁ x) := rfl

@[simp]
/--
lemma `logHeight₁_zero` / 引理 `logHeight₁_zero`

English:
lemma logHeight₁_zero
  statement: logHeight₁ (0 : K) = 0
  proof: by
  simp [logHeight₁_eq_log_mulHeight₁]

@[simp]

中文:
引理 logHeight₁_zero
  结论: logHeight₁ (0 : K) = 0
  证明: by
  simp [logHeight₁_eq_log_mulHeight₁]

@[simp]
-/
lemma logHeight₁_zero : logHeight₁ (0 : K) = 0 := by
  simp [logHeight₁_eq_log_mulHeight₁]

@[simp]
/--
lemma `logHeight₁_one` / 引理 `logHeight₁_one`

English:
lemma logHeight₁_one
  statement: logHeight₁ (1 : K) = 0
  proof: by
  simp [logHeight₁_eq_log_mulHeight₁]

中文:
引理 logHeight₁_one
  结论: logHeight₁ (1 : K) = 0
  证明: by
  simp [logHeight₁_eq_log_mulHeight₁]
-/
lemma logHeight₁_one : logHeight₁ (1 : K) = 0 := by
  simp [logHeight₁_eq_log_mulHeight₁]

/--
lemma `zero_le_logHeight₁` / 引理 `zero_le_logHeight₁`

English:
lemma zero_le_logHeight₁
  given: (x : K)
  statement: 0 <= logHeight₁ x
  proof: Real.log_nonneg one_le_mulHeight₁ x

中文:
引理 zero_le_logHeight₁
  条件: (x : K)
  结论: 0 <= logHeight₁ x
  证明: Real.log_nonneg one_le_mulHeight₁ x

Depends on / 依赖: Real.log_nonneg, log_nonneg
-/
lemma zero_le_logHeight₁ (x : K) : 0 <= logHeight₁ x :=
Real.log_nonneg one_le_mulHeight₁ x

/--
lemma `logHeight₁_eq` / 引理 `logHeight₁_eq`

English:
lemma logHeight₁_eq
  given: (x : K)
  proof: by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_eq]
  have H : mulHeight₁ x != 0 := mulHeight₁_ne_zero x
  rw [mulHeight₁_eq] at H
  have : forall a in archAbsVal.map (fun v => max (v x) 1), a != 0 := by
    intro a ha
    contrapose ha
    rw [ha]
exact Multiset.prod_eq_zero_iff.not.mp left_ne_zero_of_mul H
  rw [log_mul (left_ne_zero_of_mul H) (right_ne_zero_of_mul H)]; rw [log_multiset_prod this]; rw [Multiset.map_map]; rw [log_finprod (fun _ => by positivity)]
  congr 2 <;> simp [max_comm, posLog_eq_log_max_one]

中文:
引理 logHeight₁_eq
  条件: (x : K)
  证明: by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_eq]
  have H : mulHeight₁ x != 0 := mulHeight₁_ne_zero x
  rw [mulHeight₁_eq] at H
  have : forall a in archAbsVal.map (fun v => max (v x) 1), a != 0 := by
    intro a ha
    contrapose ha
    rw [ha]
exact Multiset.prod_eq_zero_iff.not.mp left_ne_zero_of_mul H
  rw [log_mul (left_ne_zero_of_mul H) (right_ne_zero_of_mul H)]; rw [log_multiset_prod this]; rw [Multiset.map_map]; rw [log_finprod (fun _ => by positivity)]
  congr 2 <;> simp [max_comm, posLog_eq_log_max_one]

Depends on / 依赖: Multiset, Multiset.map_map, Multiset.prod_eq_zero_iff.not.mp, archAbsVal, archAbsVal.map, contrapose, left_ne_zero_of_mul, log_finprod, log_mul, log_multiset_prod, map_map, max_comm, posLog_eq_log_ma, prod_eq_zero_iff, right_ne_zero_of_mul
-/
lemma logHeight₁_eq (x : K) :
    logHeight₁ x =
      (archAbsVal.map fun v => log⁺ (v x)).sum + ∑ᶠ v : nonarchAbsVal, log⁺ (v.val x) := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_eq]
  have H : mulHeight₁ x != 0 := mulHeight₁_ne_zero x
  rw [mulHeight₁_eq] at H
  have : forall a in archAbsVal.map (fun v => max (v x) 1), a != 0 := by
    intro a ha
    contrapose ha
    rw [ha]
exact Multiset.prod_eq_zero_iff.not.mp left_ne_zero_of_mul H
  rw [log_mul (left_ne_zero_of_mul H) (right_ne_zero_of_mul H)]; rw [log_multiset_prod this]; rw [Multiset.map_map]; rw [log_finprod (fun _ => by positivity)]
  congr 2 <;> simp [max_comm, posLog_eq_log_max_one]

end Height

/-!
### Positivity extension for mulHeight₁, logHeight₁
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Height

/-- Extension for the `positivity` tactic: `Height.mulHeight₁` is always positive. -/
@[positivity Height.mulHeight₁ _]
meta def evalMulHeight₁ : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@mulHeight₁ $K $KF $KA $a) =>
    assertInstancesCommute
    pure (.positive q(mulHeight₁_pos $a))
  | _, _, _ => throwError "not Height.mulHeight₁"

/-- Extension for the `positivity` tactic: `Height.logHeight₁` is always nonnegative. -/
@[positivity Height.logHeight₁ _]
meta def evalLogHeight₁ : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@logHeight₁ $K $KF $KA $a) =>
    assertInstancesCommute
    pure (.nonnegative q(zero_le_logHeight₁ $a))
  | _, _, _ => throwError "not Height.logHeight₁"

end Mathlib.Meta.Positivity

/-!
### Heights of tuples and finitely supported maps

We define the multiplicative height of a nonzero tuple `x : ι → K` as the product of the maxima
of `v` on `x`, as `v` runs through the relevant absolute values of `K`. As usual, the
logarithmic height is the logarithm of the multiplicative height.
When `x = 0`, we define the multiplicative height to be `1`; this is a convenient "junk value",
which allows to avoid the condition `x ≠ 0` in most of the results.

For a finitely supported function `x : ι →₀ K`, we define the height as the height of `x`
restricted to its support.
-/


namespace Height

open AdmissibleAbsValues Real Function

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι ι' : Type*}

/--
Definition of `mulHeight` / `mulHeight` 的定义

English:
definition mulHeight
  signature: (x : ι -> K)
  body: have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)

中文:
定义 mulHeight
  签名: (x : ι -> K)
  定义体: have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)

Depends on / 依赖: Classical, Classical.propDecidable, Decidable, archAbsVal, archAbsVal.map, nonarchAbsVal, propDecidable, v.val
-/
def mulHeight (x : ι -> K) : Real :=
  have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)

/--
lemma `mulHeight_eq` / 引理 `mulHeight_eq`

English:
lemma mulHeight_eq
  given: {x : ι -> K} (hx : x != 0)
  proof: by
  simp [mulHeight, hx]

@[to_fun (attr := simp)]

中文:
引理 mulHeight_eq
  条件: {x : ι -> K} (hx : x != 0)
  证明: by
  simp [mulHeight, hx]

@[to_fun (attr := simp)]

Depends on / 依赖: mulHeight
-/
lemma mulHeight_eq {x : ι -> K} (hx : x != 0) :
    mulHeight x =
      (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i) := by
  simp [mulHeight, hx]

@[to_fun (attr := simp)]
/--
lemma `mulHeight_zero` / 引理 `mulHeight_zero`

English:
lemma mulHeight_zero
  statement: mulHeight (0 : ι -> K) = 1
  proof: by
  simp [mulHeight]

@[to_fun (attr := simp)]

中文:
引理 mulHeight_zero
  结论: mulHeight (0 : ι -> K) = 1
  证明: by
  simp [mulHeight]

@[to_fun (attr := simp)]

Depends on / 依赖: mulHeight
-/
lemma mulHeight_zero : mulHeight (0 : ι -> K) = 1 := by
  simp [mulHeight]

@[to_fun (attr := simp)]
/--
lemma `mulHeight_one` / 引理 `mulHeight_one`

English:
lemma mulHeight_one
  statement: mulHeight (1 : ι -> K) = 1
  proof: by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [show (1 : ι -> K) = 0 from Subsingleton.elim ..]
    exact mulHeight_zero
  · have hx : (1 : ι -> K) != 0 := by simp
    simp [mulHeight_eq hx]

中文:
引理 mulHeight_one
  结论: mulHeight (1 : ι -> K) = 1
  证明: by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [show (1 : ι -> K) = 0 from Subsingleton.elim ..]
    exact mulHeight_zero
  · have hx : (1 : ι -> K) != 0 := by simp
    simp [mulHeight_eq hx]

Depends on / 依赖: Subsingleton, Subsingleton.elim, isEmpty_or_nonempty, mulHeight_eq, mulHeight_zero
-/
lemma mulHeight_one : mulHeight (1 : ι -> K) = 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [show (1 : ι -> K) = 0 from Subsingleton.elim ..]
    exact mulHeight_zero
  · have hx : (1 : ι -> K) != 0 := by simp
    simp [mulHeight_eq hx]

/--
lemma `mulHeight_comp_equiv` / 引理 `mulHeight_comp_equiv`

English:
lemma mulHeight_comp_equiv
  given: (e : ι ≃ ι') (x : ι' -> K)
  proof: by
  have H (v : AbsoluteValue K Real) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) := e.iSup_congr (congrFun rfl)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : x ∘ e != 0 := by
      obtain ⟨i, hi⟩ : exists i, x i != 0 := ne_iff.mp hx
      exact ne_iff.mpr ⟨e.symm i, by simp [hi]⟩
    simp [mulHeight_eq hx, mulHeight_eq hx', comp_apply, H]

中文:
引理 mulHeight_comp_equiv
  条件: (e : ι ≃ ι') (x : ι' -> K)
  证明: by
  have H (v : AbsoluteValue K Real) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) := e.iSup_congr (congrFun rfl)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : x ∘ e != 0 := by
      obtain ⟨i, hi⟩ : exists i, x i != 0 := ne_iff.mp hx
      exact ne_iff.mpr ⟨e.symm i, by simp [hi]⟩
    simp [mulHeight_eq hx, mulHeight_eq hx', comp_apply, H]

Depends on / 依赖: AbsoluteValue, comp_apply, e.iSup_congr, e.symm, eq_or_ne, iSup_congr, mulHeight_eq, ne_iff, ne_iff.mp, ne_iff.mpr
-/
lemma mulHeight_comp_equiv (e : ι ≃ ι') (x : ι' -> K) :
    mulHeight (x ∘ e) = mulHeight x := by
  have H (v : AbsoluteValue K Real) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) := e.iSup_congr (congrFun rfl)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : x ∘ e != 0 := by
      obtain ⟨i, hi⟩ : exists i, x i != 0 := ne_iff.mp hx
      exact ne_iff.mpr ⟨e.symm i, by simp [hi]⟩
    simp [mulHeight_eq hx, mulHeight_eq hx', comp_apply, H]

/--
lemma `mulHeight_swap` / 引理 `mulHeight_swap`

English:
lemma mulHeight_swap
  given: (x y : K)
  statement: mulHeight ![x, y] = mulHeight ![y, x]
  proof: by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  rw [show ![x]; rw [y] = ![y, x] ∘ e from List.ofFn_inj.mp rfl]
  exact mulHeight_comp_equiv e ![y, x]

中文:
引理 mulHeight_swap
  条件: (x y : K)
  结论: mulHeight ![x, y] = mulHeight ![y, x]
  证明: by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  rw [show ![x]; rw [y] = ![y, x] ∘ e from List.ofFn_inj.mp rfl]
  exact mulHeight_comp_equiv e ![y, x]

Depends on / 依赖: Equiv.swap, List.ofFn_inj.mp, mulHeight_comp_equiv, ofFn_inj
-/
lemma mulHeight_swap (x y : K) : mulHeight ![x, y] = mulHeight ![y, x] := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  rw [show ![x]; rw [y] = ![y, x] ∘ e from List.ofFn_inj.mp rfl]
  exact mulHeight_comp_equiv e ![y, x]

/--
Definition of `logHeight` / `logHeight` 的定义

English:
definition logHeight
  signature: (x : ι -> K)
  body: log (mulHeight x)

中文:
定义 logHeight
  签名: (x : ι -> K)
  定义体: log (mulHeight x)

Depends on / 依赖: mulHeight
-/
def logHeight (x : ι -> K) : Real := log (mulHeight x)

/--
lemma `logHeight_eq_log_mulHeight` / 引理 `logHeight_eq_log_mulHeight`

English:
lemma logHeight_eq_log_mulHeight
  given: (x : ι -> K)
  statement: logHeight x = log (mulHeight x)
  proof: rfl

@[to_fun (attr := simp)]

中文:
引理 logHeight_eq_log_mulHeight
  条件: (x : ι -> K)
  结论: logHeight x = log (mulHeight x)
  证明: rfl

@[to_fun (attr := simp)]
-/
lemma logHeight_eq_log_mulHeight (x : ι -> K) : logHeight x = log (mulHeight x) := rfl

@[to_fun (attr := simp)]
/--
lemma `logHeight_zero` / 引理 `logHeight_zero`

English:
lemma logHeight_zero
  statement: logHeight (0 : ι -> K) = 0
  proof: by
  simp [logHeight_eq_log_mulHeight]

@[to_fun (attr := simp)]

中文:
引理 logHeight_zero
  结论: logHeight (0 : ι -> K) = 0
  证明: by
  simp [logHeight_eq_log_mulHeight]

@[to_fun (attr := simp)]

Depends on / 依赖: logHeight_eq_log_mulHeight
-/
lemma logHeight_zero : logHeight (0 : ι -> K) = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[to_fun (attr := simp)]
/--
lemma `logHeight_one` / 引理 `logHeight_one`

English:
lemma logHeight_one
  statement: logHeight (1 : ι -> K) = 0
  proof: by
  simp [logHeight_eq_log_mulHeight]

中文:
引理 logHeight_one
  结论: logHeight (1 : ι -> K) = 0
  证明: by
  simp [logHeight_eq_log_mulHeight]

Depends on / 依赖: logHeight_eq_log_mulHeight
-/
lemma logHeight_one : logHeight (1 : ι -> K) = 0 := by
  simp [logHeight_eq_log_mulHeight]

/--
lemma `logHeight_comp_equiv` / 引理 `logHeight_comp_equiv`

English:
lemma logHeight_comp_equiv
  given: (e : ι ≃ ι') (x : ι' -> K)
  proof: by
  simp only [logHeight_eq_log_mulHeight, mulHeight_comp_equiv]

中文:
引理 logHeight_comp_equiv
  条件: (e : ι ≃ ι') (x : ι' -> K)
  证明: by
  simp only [logHeight_eq_log_mulHeight, mulHeight_comp_equiv]

Depends on / 依赖: logHeight_eq_log_mulHeight, mulHeight_comp_equiv
-/
lemma logHeight_comp_equiv (e : ι ≃ ι') (x : ι' -> K) :
    logHeight (x ∘ ⇑e) = logHeight x := by
  simp only [logHeight_eq_log_mulHeight, mulHeight_comp_equiv]

/--
lemma `logHeight_swap` / 引理 `logHeight_swap`

English:
lemma logHeight_swap
  given: (x y : K)
  statement: logHeight ![x, y] = logHeight ![y, x]
  proof: by
  simp only [logHeight_eq_log_mulHeight, mulHeight_swap]

中文:
引理 logHeight_swap
  条件: (x y : K)
  结论: logHeight ![x, y] = logHeight ![y, x]
  证明: by
  simp only [logHeight_eq_log_mulHeight, mulHeight_swap]

Depends on / 依赖: logHeight_eq_log_mulHeight, mulHeight_swap
-/
lemma logHeight_swap (x y : K) : logHeight ![x, y] = logHeight ![y, x] := by
  simp only [logHeight_eq_log_mulHeight, mulHeight_swap]

variable {α : Type*}

/--
Definition of `_root_.Finsupp.mulHeight` / `_root_.Finsupp.mulHeight` 的定义

English:
definition _root_.Finsupp.mulHeight
  signature: (x : α ->₀ K)
  body: Height.mulHeight fun i : x.support => x i

中文:
定义 _root_.有限支撑.mulHeight
  签名: (x : α ->₀ K)
  定义体: Height.mulHeight fun i : x.support => x i

Depends on / 依赖: Height, Height.mulHeight, mulHeight, support, x.support
-/
def _root_.Finsupp.mulHeight (x : α ->₀ K) : Real :=
  Height.mulHeight fun i : x.support => x i

/--
Definition of `_root_.Finsupp.logHeight` / `_root_.Finsupp.logHeight` 的定义

English:
definition _root_.Finsupp.logHeight
  signature: (x : α ->₀ K)
  body: log (mulHeight x)

中文:
定义 _root_.有限支撑.logHeight
  签名: (x : α ->₀ K)
  定义体: log (mulHeight x)

Depends on / 依赖: mulHeight
-/
def _root_.Finsupp.logHeight (x : α ->₀ K) : Real := log (mulHeight x)

/--
lemma `_root_.Finsupp.logHeight_eq_log_mulHeight` / 引理 `_root_.Finsupp.logHeight_eq_log_mulHeight`

English:
lemma _root_.Finsupp.logHeight_eq_log_mulHeight
  given: (x : α ->₀ K)
  proof: rfl

中文:
引理 _root_.有限支撑.logHeight_eq_log_mulHeight
  条件: (x : α ->₀ K)
  证明: rfl
-/
lemma _root_.Finsupp.logHeight_eq_log_mulHeight (x : α ->₀ K) :
    logHeight x = log (mulHeight x) := rfl


/--
lemma `max_eq_iSup` / 引理 `max_eq_iSup`

English:
lemma max_eq_iSup
  given: {α : Type*} [ConditionallyCompleteLattice α] (a b : α)
  proof: eq_of_forall_ge_iff by simp [ciSup_le_iff, Fin.forall_fin_two]

中文:
引理 max_eq_iSup
  条件: {α : 类型} [条件完备格 α] (a b : α)
  证明: eq_of_forall_ge_iff by simp [ciSup_le_iff, Fin.forall_fin_two]
-/
private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = iSup ![a, b] :=
eq_of_forall_ge_iff by simp [ciSup_le_iff, Fin.forall_fin_two]

variable [Finite ι] [Finite ι']

@[fun_prop]
/--
lemma `hasFiniteMulSupport_iSup_nonarchAbsVal` / 引理 `hasFiniteMulSupport_iSup_nonarchAbsVal`

English:
lemma hasFiniteMulSupport_iSup_nonarchAbsVal
  given: {x : ι -> K} (hx : x != 0)
  proof: by
have : Nonempty {j // x j != 0} := nonempty_subtype.mpr ne_iff.mp hx
  suffices (fun v : nonarchAbsVal => ⨆ i : {j // x j != 0}, v.val (x i)).HasFiniteMulSupport by
    convert! this with v
    obtain ⟨i, hi⟩ : exists j, x j != 0 := Function.ne_iff.mp hx
    have : Nonempty ι := .intro i
    refine le_antisymm (ciSup_le fun j => ?_) (ciSup_le fun ⟨j, hj⟩ => Finite.le_ciSup_of_le j le_rfl)
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, v.val.map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
    · exact Finite.le_ciSup_of_le ⟨j, h⟩ le_rfl
  fun_prop (disch := grind)

@[fun_prop]

中文:
引理 hasFiniteMulSupport_iSup_nonarchAbsVal
  条件: {x : ι -> K} (hx : x != 0)
  证明: by
have : Nonempty {j // x j != 0} := nonempty_subtype.mpr ne_iff.mp hx
  suffices (fun v : nonarchAbsVal => ⨆ i : {j // x j != 0}, v.val (x i)).HasFiniteMulSupport by
    convert! this with v
    obtain ⟨i, hi⟩ : exists j, x j != 0 := Function.ne_iff.mp hx
    have : Nonempty ι := .intro i
    refine le_antisymm (ciSup_le fun j => ?_) (ciSup_le fun ⟨j, hj⟩ => Finite.le_ciSup_of_le j le_rfl)
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, v.val.map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
    · exact Finite.le_ciSup_of_le ⟨j, h⟩ le_rfl
  fun_prop (disch := grind)

@[fun_prop]
-/
private lemma hasFiniteMulSupport_iSup_nonarchAbsVal {x : ι -> K} (hx : x != 0) :
    (fun v : nonarchAbsVal => ⨆ i, v.val (x i)).HasFiniteMulSupport := by
have : Nonempty {j // x j != 0} := nonempty_subtype.mpr ne_iff.mp hx
  suffices (fun v : nonarchAbsVal => ⨆ i : {j // x j != 0}, v.val (x i)).HasFiniteMulSupport by
    convert! this with v
    obtain ⟨i, hi⟩ : exists j, x j != 0 := Function.ne_iff.mp hx
    have : Nonempty ι := .intro i
    refine le_antisymm (ciSup_le fun j => ?_) (ciSup_le fun ⟨j, hj⟩ => Finite.le_ciSup_of_le j le_rfl)
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, v.val.map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
    · exact Finite.le_ciSup_of_le ⟨j, h⟩ le_rfl
  fun_prop (disch := grind)

@[fun_prop]
/--
lemma `hasFiniteMulSupport_max_nonarchAbsVal` / 引理 `hasFiniteMulSupport_max_nonarchAbsVal`

English:
lemma hasFiniteMulSupport_max_nonarchAbsVal
  given: (x : K)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [HasFiniteMulSupport]
  fun_prop

中文:
引理 hasFiniteMulSupport_max_nonarchAbsVal
  条件: (x : K)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [HasFiniteMulSupport]
  fun_prop
-/
private lemma hasFiniteMulSupport_max_nonarchAbsVal (x : K) :
    (fun v : nonarchAbsVal => v.val x ⊔ 1).HasFiniteMulSupport := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [HasFiniteMulSupport]
  fun_prop

/--
lemma `mulHeight_smul_eq_mulHeight` / 引理 `mulHeight_smul_eq_mulHeight`

English:
lemma mulHeight_smul_eq_mulHeight
  given: (x : ι -> K) {c : K} (hc : c != 0)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have : Nonempty ι := (ne_iff.mp hx).nonempty
  have hcx : c • x != 0 := by simp [hc, hx]
  simp only [mulHeight_eq hx, mulHeight_eq hcx, Pi.smul_apply, smul_eq_mul, map_mul,
← mul_iSup_of_nonneg AbsoluteValue.nonneg .., Multiset.prod_map_mul]
  rw [finprod_mul_distrib (by fun_prop) (by fun_prop)]; rw [mul_mul_mul_comm]; rw [product_formula hc]; rw [one_mul]

中文:
引理 mulHeight_smul_eq_mulHeight
  条件: (x : ι -> K) {c : K} (hc : c != 0)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have : Nonempty ι := (ne_iff.mp hx).nonempty
  have hcx : c • x != 0 := by simp [hc, hx]
  simp only [mulHeight_eq hx, mulHeight_eq hcx, Pi.smul_apply, smul_eq_mul, map_mul,
← mul_iSup_of_nonneg AbsoluteValue.nonneg .., Multiset.prod_map_mul]
  rw [finprod_mul_distrib (by fun_prop) (by fun_prop)]; rw [mul_mul_mul_comm]; rw [product_formula hc]; rw [one_mul]

Depends on / 依赖: AbsoluteValue, AbsoluteValue.nonneg, Multiset, Multiset.prod_map_mul, Nonempty, Pi.smul_apply, eq_or_ne, finprod_mul_distrib, fun_prop, map_mul, mulHeight_eq, mul_iSup_of_nonneg, mul_mul_mul_comm, ne_iff, ne_iff.mp, nonempty, nonneg, one_mul, prod_map_mul, product_formula
-/
lemma mulHeight_smul_eq_mulHeight (x : ι -> K) {c : K} (hc : c != 0) :
    mulHeight (c • x) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have : Nonempty ι := (ne_iff.mp hx).nonempty
  have hcx : c • x != 0 := by simp [hc, hx]
  simp only [mulHeight_eq hx, mulHeight_eq hcx, Pi.smul_apply, smul_eq_mul, map_mul,
← mul_iSup_of_nonneg AbsoluteValue.nonneg .., Multiset.prod_map_mul]
  rw [finprod_mul_distrib (by fun_prop) (by fun_prop)]; rw [mul_mul_mul_comm]; rw [product_formula hc]; rw [one_mul]

/--
lemma `one_le_mulHeight` / 引理 `one_le_mulHeight`

English:
lemma one_le_mulHeight
  given: (x : ι -> K)
  statement: 1 <= mulHeight x
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ : exists i, x i != 0 := ne_iff.mp hx
  have hx' : (x i)⁻¹ • x != 0 := by simp [hi, hx]
  rw [← mulHeight_smul_eq_mulHeight _ <| inv_ne_zero hi]; rw [mulHeight_eq hx']
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod_map fun v _ => ?_) ?_
· refine Finite.le_ciSup_of_le i le_of_eq ?_
    simpa using (inv_mul_cancel₀ <| v.ne_zero_iff.mpr hi).symm
  · refine one_le_finprod fun v => Finite.le_ciSup_of_le i ?_
    simp [inv_mul_cancel₀ <| v.val.ne_zero_iff.mpr hi]

中文:
引理 one_le_mulHeight
  条件: (x : ι -> K)
  结论: 1 <= mulHeight x
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ : exists i, x i != 0 := ne_iff.mp hx
  have hx' : (x i)⁻¹ • x != 0 := by simp [hi, hx]
  rw [← mulHeight_smul_eq_mulHeight _ <| inv_ne_zero hi]; rw [mulHeight_eq hx']
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod_map fun v _ => ?_) ?_
· refine Finite.le_ciSup_of_le i le_of_eq ?_
    simpa using (inv_mul_cancel₀ <| v.ne_zero_iff.mpr hi).symm
  · refine one_le_finprod fun v => Finite.le_ciSup_of_le i ?_
    simp [inv_mul_cancel₀ <| v.val.ne_zero_iff.mpr hi]

Depends on / 依赖: Finite, Finite.le_ciSup_of_le, Multiset, Multiset.one_le_prod_map, eq_or_ne, inv_ne_zero, le_ciSup_of_le, le_of_eq, mulHeight_eq, mulHeight_smul_eq_mulHeight, ne_iff, ne_iff.mp, ne_zero_iff, one_le_finprod, one_le_mul_of_one_le_of_one_le, one_le_prod_map, v.ne_zero_iff.mpr, v.val.n
-/
lemma one_le_mulHeight (x : ι -> K) : 1 <= mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ : exists i, x i != 0 := ne_iff.mp hx
  have hx' : (x i)⁻¹ • x != 0 := by simp [hi, hx]
  rw [← mulHeight_smul_eq_mulHeight _ <| inv_ne_zero hi]; rw [mulHeight_eq hx']
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod_map fun v _ => ?_) ?_
· refine Finite.le_ciSup_of_le i le_of_eq ?_
    simpa using (inv_mul_cancel₀ <| v.ne_zero_iff.mpr hi).symm
  · refine one_le_finprod fun v => Finite.le_ciSup_of_le i ?_
    simp [inv_mul_cancel₀ <| v.val.ne_zero_iff.mpr hi]

/--
lemma `mulHeight_pos` / 引理 `mulHeight_pos`

English:
lemma mulHeight_pos
  given: (x : ι -> K)
  statement: 0 < mulHeight x
  proof: zero_lt_one.trans_le one_le_mulHeight x

中文:
引理 mulHeight_pos
  条件: (x : ι -> K)
  结论: 0 < mulHeight x
  证明: zero_lt_one.trans_le one_le_mulHeight x

Depends on / 依赖: one_le_mulHeight, trans_le, zero_lt_one, zero_lt_one.trans_le
-/
lemma mulHeight_pos (x : ι -> K) : 0 < mulHeight x :=
zero_lt_one.trans_le one_le_mulHeight x

/--
lemma `mulHeight_ne_zero` / 引理 `mulHeight_ne_zero`

English:
lemma mulHeight_ne_zero
  given: (x : ι -> K)
  statement: mulHeight x != 0
  proof: (mulHeight_pos x).ne'

中文:
引理 mulHeight_ne_zero
  条件: (x : ι -> K)
  结论: mulHeight x != 0
  证明: (mulHeight_pos x).ne'

Depends on / 依赖: mulHeight_pos
-/
lemma mulHeight_ne_zero (x : ι -> K) : mulHeight x != 0 :=
  (mulHeight_pos x).ne'

/--
lemma `logHeight_nonneg` / 引理 `logHeight_nonneg`

English:
lemma logHeight_nonneg
  given: (x : ι -> K)
  statement: 0 <= logHeight x
  proof: log_nonneg one_le_mulHeight x

中文:
引理 logHeight_nonneg
  条件: (x : ι -> K)
  结论: 0 <= logHeight x
  证明: log_nonneg one_le_mulHeight x

Depends on / 依赖: log_nonneg, one_le_mulHeight
-/
lemma logHeight_nonneg (x : ι -> K) : 0 <= logHeight x :=
log_nonneg one_le_mulHeight x

open Function in
/--
lemma `mulHeight_comp_le` / 引理 `mulHeight_comp_le`

English:
lemma mulHeight_comp_le
  given: (f : ι -> ι') (x : ι' -> K)
  proof: by
  rcases eq_or_ne (x ∘ f) 0 with h₀ | h₀
  · simpa [h₀] using one_le_mulHeight _
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have : Nonempty ι := .intro (ne_iff.mp h₀).choose
  rw [mulHeight_eq h₀]; rw [mulHeight_eq hx]
  have H (v : AbsoluteValue K Real) : ⨆ i, v ((x ∘ f) i) <= ⨆ i, v (x i) :=
    ciSup_le fun i => Finite.le_ciSup_of_le (f i) le_rfl
  gcongr
  · exact finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _
  · exact Multiset.prod_map_nonneg fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _
  · exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _)
      fun v _ => H v
  · exact finprod_le_finprod (hasFiniteMulSupport_iSup_nonarchAbsVal h₀)
      (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
      (hasFiniteMulSupport_iSup_nonarchAbsVal hx) fun v => H v.val

中文:
引理 mulHeight_comp_le
  条件: (f : ι -> ι') (x : ι' -> K)
  证明: by
  rcases eq_or_ne (x ∘ f) 0 with h₀ | h₀
  · simpa [h₀] using one_le_mulHeight _
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have : Nonempty ι := .intro (ne_iff.mp h₀).choose
  rw [mulHeight_eq h₀]; rw [mulHeight_eq hx]
  have H (v : AbsoluteValue K Real) : ⨆ i, v ((x ∘ f) i) <= ⨆ i, v (x i) :=
    ciSup_le fun i => Finite.le_ciSup_of_le (f i) le_rfl
  gcongr
  · exact finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _
  · exact Multiset.prod_map_nonneg fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _
  · exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _)
      fun v _ => H v
  · exact finprod_le_finprod (hasFiniteMulSupport_iSup_nonarchAbsVal h₀)
      (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
      (hasFiniteMulSupport_iSup_nonarchAbsVal hx) fun v => H v.val

Depends on / 依赖: AbsoluteValue, Finite, Finite.le_ciSup_of_le, Multiset, Multiset.prod_map_nonneg, Nonempty, Real.iSup_nonneg_of_nonnegHomClas, Real.iSup_nonneg_of_nonnegHomClass, ciSup_le, eq_or_ne, finprod_nonneg, iSup_nonneg_of_nonnegHomClas, iSup_nonneg_of_nonnegHomClass, le_ciSup_of_le, le_rfl, mulHeight_eq, ne_iff, ne_iff.mp, one_le_mulHeight, prod_map_nonneg
-/
lemma mulHeight_comp_le (f : ι -> ι') (x : ι' -> K) :
    mulHeight (x ∘ f) <= mulHeight x := by
  rcases eq_or_ne (x ∘ f) 0 with h₀ | h₀
  · simpa [h₀] using one_le_mulHeight _
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have : Nonempty ι := .intro (ne_iff.mp h₀).choose
  rw [mulHeight_eq h₀]; rw [mulHeight_eq hx]
  have H (v : AbsoluteValue K Real) : ⨆ i, v ((x ∘ f) i) <= ⨆ i, v (x i) :=
    ciSup_le fun i => Finite.le_ciSup_of_le (f i) le_rfl
  gcongr
  · exact finprod_nonneg fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _
  · exact Multiset.prod_map_nonneg fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _
  · exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ => Real.iSup_nonneg_of_nonnegHomClass v _)
      fun v _ => H v
  · exact finprod_le_finprod (hasFiniteMulSupport_iSup_nonarchAbsVal h₀)
      (fun v => Real.iSup_nonneg_of_nonnegHomClass v.val _)
      (hasFiniteMulSupport_iSup_nonarchAbsVal hx) fun v => H v.val

open Real in
/--
lemma `logHeight_comp_le` / 引理 `logHeight_comp_le`

English:
lemma logHeight_comp_le
  given: (f : ι -> ι') (x : ι' -> K)
  proof: by
simpa [logHeight_eq_log_mulHeight] using log_le_log (mulHeight_pos _) mulHeight_comp_le ..

中文:
引理 logHeight_comp_le
  条件: (f : ι -> ι') (x : ι' -> K)
  证明: by
simpa [logHeight_eq_log_mulHeight] using log_le_log (mulHeight_pos _) mulHeight_comp_le ..

Depends on / 依赖: logHeight_eq_log_mulHeight, log_le_log, mulHeight_comp_le, mulHeight_pos
-/
lemma logHeight_comp_le (f : ι -> ι') (x : ι' -> K) :
    logHeight (x ∘ f) <= logHeight x := by
simpa [logHeight_eq_log_mulHeight] using log_le_log (mulHeight_pos _) mulHeight_comp_le ..

open Function in
/--
lemma `mulHeight_sumElim_zero_eq` / 引理 `mulHeight_sumElim_zero_eq`

English:
lemma mulHeight_sumElim_zero_eq
  given: (x : ι -> K)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ := ne_iff.mp hx
  have : Nonempty ι := .intro i
  have hx' : Sum.elim x (0 : ι' -> K) != 0 := ne_iff.mpr ⟨.inl i, by simpa using hi⟩
  rw [mulHeight_eq hx]; rw [mulHeight_eq hx']
  have H (v : AbsoluteValue K Real) : ⨆ j, v (Sum.elim x (0 : ι' -> K) j) = ⨆ i, v (x i) := by
refine le_antisymm ?_ ciSup_le fun i => Finite.le_ciSup_of_le (.inl i) le_rfl
    refine ciSup_le fun j => ?_
    cases j with
    | inl i => exact Finite.le_ciSup_of_le i le_rfl
    | inr _ => simpa using Real.iSup_nonneg_of_nonnegHomClass v _
  congr <;> ext1 v
  · exact H v
  · exact H v.val

中文:
引理 mulHeight_sumElim_zero_eq
  条件: (x : ι -> K)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ := ne_iff.mp hx
  have : Nonempty ι := .intro i
  have hx' : Sum.elim x (0 : ι' -> K) != 0 := ne_iff.mpr ⟨.inl i, by simpa using hi⟩
  rw [mulHeight_eq hx]; rw [mulHeight_eq hx']
  have H (v : AbsoluteValue K Real) : ⨆ j, v (Sum.elim x (0 : ι' -> K) j) = ⨆ i, v (x i) := by
refine le_antisymm ?_ ciSup_le fun i => Finite.le_ciSup_of_le (.inl i) le_rfl
    refine ciSup_le fun j => ?_
    cases j with
    | inl i => exact Finite.le_ciSup_of_le i le_rfl
    | inr _ => simpa using Real.iSup_nonneg_of_nonnegHomClass v _
  congr <;> ext1 v
  · exact H v
  · exact H v.val

Depends on / 依赖: AbsoluteValue, Finite, Finite.le_ciSup_of_le, Nonempty, Sum.elim, ciSup_le, eq_or_ne, le_antisymm, le_ciSup_of_le, le_rfl, mulHeight_eq, ne_iff, ne_iff.mp, ne_iff.mpr
-/
lemma mulHeight_sumElim_zero_eq (x : ι -> K) :
    mulHeight (Sum.elim x (0 : ι' -> K)) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ := ne_iff.mp hx
  have : Nonempty ι := .intro i
  have hx' : Sum.elim x (0 : ι' -> K) != 0 := ne_iff.mpr ⟨.inl i, by simpa using hi⟩
  rw [mulHeight_eq hx]; rw [mulHeight_eq hx']
  have H (v : AbsoluteValue K Real) : ⨆ j, v (Sum.elim x (0 : ι' -> K) j) = ⨆ i, v (x i) := by
refine le_antisymm ?_ ciSup_le fun i => Finite.le_ciSup_of_le (.inl i) le_rfl
    refine ciSup_le fun j => ?_
    cases j with
    | inl i => exact Finite.le_ciSup_of_le i le_rfl
    | inr _ => simpa using Real.iSup_nonneg_of_nonnegHomClass v _
  congr <;> ext1 v
  · exact H v
  · exact H v.val

/--
lemma `logHeight_sumElim_zero_eq` / 引理 `logHeight_sumElim_zero_eq`

English:
lemma logHeight_sumElim_zero_eq
  given: (x : ι -> K)
  proof: congrArg log mulHeight_sumElim_zero_eq ..

中文:
引理 logHeight_sumElim_zero_eq
  条件: (x : ι -> K)
  证明: congrArg log mulHeight_sumElim_zero_eq ..

Depends on / 依赖: mulHeight_sumElim_zero_eq
-/
lemma logHeight_sumElim_zero_eq (x : ι -> K) :
    logHeight (Sum.elim x (0 : ι' -> K)) = logHeight x :=
congrArg log mulHeight_sumElim_zero_eq ..

/--
lemma `mulHeight_eq_mulHeight_restrict_support` / 引理 `mulHeight_eq_mulHeight_restrict_support`

English:
lemma mulHeight_eq_mulHeight_restrict_support
  given: (x : ι -> K)
  proof: by
  classical
  let e := Equiv.Set.sumCompl x.support
  have hx : x ∘ e = Sum.elim (fun i : x.support => x i.val) 0 := by
    ext1 i
    simp only [comp_apply]
    cases i with
    | inl val => simp [e]
| inr val => exact notMem_support.mp (Set.mem_compl_iff _ _).mp val.prop
  rw [← mulHeight_comp_equiv e]; rw [hx]
  exact mulHeight_sumElim_zero_eq ..

中文:
引理 mulHeight_eq_mulHeight_restrict_support
  条件: (x : ι -> K)
  证明: by
  classical
  let e := Equiv.Set.sumCompl x.support
  have hx : x ∘ e = Sum.elim (fun i : x.support => x i.val) 0 := by
    ext1 i
    simp only [comp_apply]
    cases i with
    | inl val => simp [e]
| inr val => exact notMem_support.mp (Set.mem_compl_iff _ _).mp val.prop
  rw [← mulHeight_comp_equiv e]; rw [hx]
  exact mulHeight_sumElim_zero_eq ..

Depends on / 依赖: Equiv.Set.sumCompl, Set.mem_compl_iff, Sum.elim, classical, comp_apply, i.val, mem_compl_iff, mulHeight_comp_equiv, mulHeight_sumElim_zero_eq, notMem_support, notMem_support.mp, sumCompl, support, val.prop, x.support
-/
lemma mulHeight_eq_mulHeight_restrict_support (x : ι -> K) :
    mulHeight x = mulHeight fun i : x.support => x i.val := by
  classical
  let e := Equiv.Set.sumCompl x.support
  have hx : x ∘ e = Sum.elim (fun i : x.support => x i.val) 0 := by
    ext1 i
    simp only [comp_apply]
    cases i with
    | inl val => simp [e]
| inr val => exact notMem_support.mp (Set.mem_compl_iff _ _).mp val.prop
  rw [← mulHeight_comp_equiv e]; rw [hx]
  exact mulHeight_sumElim_zero_eq ..

/--
lemma `logHeight_eq_logHeight_restrict_support` / 引理 `logHeight_eq_logHeight_restrict_support`

English:
lemma logHeight_eq_logHeight_restrict_support
  given: (x : ι -> K)
  proof: congrArg log mulHeight_eq_mulHeight_restrict_support x

@[simp]

中文:
引理 logHeight_eq_logHeight_restrict_support
  条件: (x : ι -> K)
  证明: congrArg log mulHeight_eq_mulHeight_restrict_support x

@[simp]

Depends on / 依赖: mulHeight_eq_mulHeight_restrict_support
-/
lemma logHeight_eq_logHeight_restrict_support (x : ι -> K) :
    logHeight x = logHeight fun i : x.support => x i.val :=
congrArg log mulHeight_eq_mulHeight_restrict_support x

@[simp]
/--
lemma `mulHeight_eq_one_of_subsingleton` / 引理 `mulHeight_eq_one_of_subsingleton`

English:
lemma mulHeight_eq_one_of_subsingleton
  given: {ι : Type*} [Subsingleton ι] (x : ι -> K)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := .intro i
  rw [← mulHeight_smul_eq_mulHeight x (inv_ne_zero hi)]
  convert! mulHeight_one
  ext1 j
  simpa [Subsingleton.elim j i] using inv_mul_cancel₀ hi

@[simp]

中文:
引理 mulHeight_eq_one_of_subsingleton
  条件: {ι : 类型} [子单例 ι] (x : ι -> K)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := .intro i
  rw [← mulHeight_smul_eq_mulHeight x (inv_ne_zero hi)]
  convert! mulHeight_one
  ext1 j
  simpa [Subsingleton.elim j i] using inv_mul_cancel₀ hi

@[simp]

Depends on / 依赖: Function, Function.ne_iff.mp, Nonempty, Subsingleton, Subsingleton.elim, convert, eq_or_ne, inv_ne_zero, mulHeight_one, mulHeight_smul_eq_mulHeight, ne_iff
-/
lemma mulHeight_eq_one_of_subsingleton {ι : Type*} [Subsingleton ι] (x : ι -> K) :
    mulHeight x = 1 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have : Nonempty ι := .intro i
  rw [← mulHeight_smul_eq_mulHeight x (inv_ne_zero hi)]
  convert! mulHeight_one
  ext1 j
  simpa [Subsingleton.elim j i] using inv_mul_cancel₀ hi

@[simp]
/--
lemma `logHeight_eq_zero_of_subsingleton` / 引理 `logHeight_eq_zero_of_subsingleton`

English:
lemma logHeight_eq_zero_of_subsingleton
  given: {ι : Type*} [Subsingleton ι] (x : ι -> K)
  proof: by
  simp [logHeight_eq_log_mulHeight]

中文:
引理 logHeight_eq_zero_of_subsingleton
  条件: {ι : 类型} [子单例 ι] (x : ι -> K)
  证明: by
  simp [logHeight_eq_log_mulHeight]

Depends on / 依赖: logHeight_eq_log_mulHeight
-/
lemma logHeight_eq_zero_of_subsingleton {ι : Type*} [Subsingleton ι] (x : ι -> K) :
    logHeight x = 0 := by
  simp [logHeight_eq_log_mulHeight]

section tuple

/-
This section contains `simp` lemmas that remove a zero from one of the first three positions
in a tuple, when `mulHeight` or `logHeight` is applied to it.

TODO: Write a `simproc` that removes *all* (syntactic) zeros from a tuple in this situation.
-/

open Matrix

variable {n : Nat} (a b : K) (x : Fin n -> K)

@[simp]
/--
lemma `mulHeight_cons_zero` / 引理 `mulHeight_cons_zero`

English:
lemma mulHeight_cons_zero
  statement: mulHeight (vecCons 0 x) = mulHeight x
  proof: by
let e := (Equiv.sumComm ..).trans finSumFinEquiv.trans finCongr n.one_add
  have he : Matrix.vecCons 0 x ∘ ⇑e = Sum.elim x 0 := by
    ext j : 1
    match j with
    | .inl _ => simp [e]
    | .inr ⟨i, h⟩ =>
      simp [show i = 0 by lia, e, show Fin.castAdd n 0 = 0 from Fin.castAdd_mk _ _ zero_lt_one]
  rw [← mulHeight_comp_equiv e]; rw [he]; rw [mulHeight_sumElim_zero_eq]

@[simp]

中文:
引理 mulHeight_cons_zero
  结论: mulHeight (vecCons 0 x) = mulHeight x
  证明: by
let e := (Equiv.sumComm ..).trans finSumFinEquiv.trans finCongr n.one_add
  have he : Matrix.vecCons 0 x ∘ ⇑e = Sum.elim x 0 := by
    ext j : 1
    match j with
    | .inl _ => simp [e]
    | .inr ⟨i, h⟩ =>
      simp [show i = 0 by lia, e, show Fin.castAdd n 0 = 0 from Fin.castAdd_mk _ _ zero_lt_one]
  rw [← mulHeight_comp_equiv e]; rw [he]; rw [mulHeight_sumElim_zero_eq]

@[simp]

Depends on / 依赖: Equiv.sumComm, Fin.castAdd, Fin.castAdd_mk, Matrix, Matrix.vecCons, Sum.elim, castAdd, castAdd_mk, finCongr, finSumFinEquiv, finSumFinEquiv.trans, mulHeight_comp_equiv, mulHeight_sumElim_zero_eq, n.one_add, one_add, sumComm, vecCons, zero_lt_one
-/
lemma mulHeight_cons_zero : mulHeight (vecCons 0 x) = mulHeight x := by
let e := (Equiv.sumComm ..).trans finSumFinEquiv.trans finCongr n.one_add
  have he : Matrix.vecCons 0 x ∘ ⇑e = Sum.elim x 0 := by
    ext j : 1
    match j with
    | .inl _ => simp [e]
    | .inr ⟨i, h⟩ =>
      simp [show i = 0 by lia, e, show Fin.castAdd n 0 = 0 from Fin.castAdd_mk _ _ zero_lt_one]
  rw [← mulHeight_comp_equiv e]; rw [he]; rw [mulHeight_sumElim_zero_eq]

@[simp]
/--
lemma `logHeight_cons_zero` / 引理 `logHeight_cons_zero`

English:
lemma logHeight_cons_zero
  statement: logHeight (Matrix.vecCons 0 x) = logHeight x
  proof: by
  simp [logHeight_eq_log_mulHeight]

@[simp]

中文:
引理 logHeight_cons_zero
  结论: logHeight (矩阵.vecCons 0 x) = logHeight x
  证明: by
  simp [logHeight_eq_log_mulHeight]

@[simp]

Depends on / 依赖: logHeight_eq_log_mulHeight
-/
lemma logHeight_cons_zero : logHeight (Matrix.vecCons 0 x) = logHeight x := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
/--
lemma `mulHeight_cons_cons_zero` / 引理 `mulHeight_cons_cons_zero`

English:
lemma mulHeight_cons_cons_zero
  statement: mulHeight (vecCons a (vecCons 0 x)) = mulHeight (vecCons a x)
  proof: by
  rw [← mulHeight_comp_equiv (Equiv.swap 0 1)]
  simp

@[simp]

中文:
引理 mulHeight_cons_cons_zero
  结论: mulHeight (vecCons a (vecCons 0 x)) = mulHeight (vecCons a x)
  证明: by
  rw [← mulHeight_comp_equiv (Equiv.swap 0 1)]
  simp

@[simp]

Depends on / 依赖: Equiv.swap, mulHeight_comp_equiv
-/
lemma mulHeight_cons_cons_zero : mulHeight (vecCons a (vecCons 0 x)) = mulHeight (vecCons a x) := by
  rw [← mulHeight_comp_equiv (Equiv.swap 0 1)]
  simp

@[simp]
/--
lemma `logHeight_cons_cons_zero` / 引理 `logHeight_cons_cons_zero`

English:
lemma logHeight_cons_cons_zero
  statement: logHeight (vecCons a (vecCons 0 x)) = logHeight (vecCons a x)
  proof: by
  simp [logHeight_eq_log_mulHeight]

@[simp]

中文:
引理 logHeight_cons_cons_zero
  结论: logHeight (vecCons a (vecCons 0 x)) = logHeight (vecCons a x)
  证明: by
  simp [logHeight_eq_log_mulHeight]

@[simp]

Depends on / 依赖: logHeight_eq_log_mulHeight
-/
lemma logHeight_cons_cons_zero : logHeight (vecCons a (vecCons 0 x)) = logHeight (vecCons a x) := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
/--
lemma `mulHeight_cons_cons_cons_zero` / 引理 `mulHeight_cons_cons_cons_zero`

English:
lemma mulHeight_cons_cons_cons_zero
  proof: by
  rw [← mulHeight_comp_equiv (Equiv.swap (Fin.succ 0) (Fin.succ 1))]; rw [← cons_swap]
  simp

@[simp]

中文:
引理 mulHeight_cons_cons_cons_zero
  证明: by
  rw [← mulHeight_comp_equiv (Equiv.swap (Fin.succ 0) (Fin.succ 1))]; rw [← cons_swap]
  simp

@[simp]

Depends on / 依赖: Equiv.swap, Fin.succ, cons_swap, mulHeight_comp_equiv
-/
lemma mulHeight_cons_cons_cons_zero :
    mulHeight (vecCons a (vecCons b (vecCons 0 x))) = mulHeight (vecCons a (vecCons b x)) := by
  rw [← mulHeight_comp_equiv (Equiv.swap (Fin.succ 0) (Fin.succ 1))]; rw [← cons_swap]
  simp

@[simp]
/--
lemma `logHeight_cons_cons_cons_zero` / 引理 `logHeight_cons_cons_cons_zero`

English:
lemma logHeight_cons_cons_cons_zero
  proof: by
  simp [logHeight_eq_log_mulHeight]

中文:
引理 logHeight_cons_cons_cons_zero
  证明: by
  simp [logHeight_eq_log_mulHeight]

Depends on / 依赖: logHeight_eq_log_mulHeight
-/
lemma logHeight_cons_cons_cons_zero :
    logHeight (vecCons a (vecCons b (vecCons 0 x))) = logHeight (vecCons a (vecCons b x)) := by
  simp [logHeight_eq_log_mulHeight]

end tuple

end Height

/-!
### Positivity extension for mulHeight, logHeight
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq Height

/-- Extension for the `positivity` tactic: `Height.mulHeight` is always positive. -/
@[positivity Height.mulHeight _]
meta def evalMulHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@mulHeight $K $KF $KA $ι $a) =>
    -- Check whether there is a `Finite` instance for `$ι` around.
    match ← trySynthInstanceQ q(Finite $ι) with
    | .some _instFinite =>
      assertInstancesCommute
      return .positive q(mulHeight_pos $a)
    | _ => throwError "index type in Height.mulHeight not known to be finite"
  | _, _, _ => throwError "not Height.mulHeight"

/-- Extension for the `positivity` tactic: `Height.logHeight` is always nonnegative. -/
@[positivity Height.logHeight _]
meta def evalLogHeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(@logHeight $K $KF $KA $ι $a) =>
    -- Check whether there is a `Finite` instance for `$ι` around.
    match ← trySynthInstanceQ q(Finite $ι) with
    | .some _instFinite =>
      assertInstancesCommute
      return .nonnegative q(logHeight_nonneg $a)
    | _ => throwError "index type in Height.logHeight not known to be finite"
  | _, _, _ => throwError "not Height.logHeight"

end Mathlib.Meta.Positivity

/-!
### Further properties of heights
-/

namespace Height

open AdmissibleAbsValues Real Function

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*} {α : Type*} [Finite ι]

/--
lemma `logHeight_smul_eq_logHeight` / 引理 `logHeight_smul_eq_logHeight`

English:
lemma logHeight_smul_eq_logHeight
  given: (x : ι -> K) {c : K} (hc : c != 0)
  proof: by
  simp only [logHeight_eq_log_mulHeight, mulHeight_smul_eq_mulHeight x hc]

中文:
引理 logHeight_smul_eq_logHeight
  条件: (x : ι -> K) {c : K} (hc : c != 0)
  证明: by
  simp only [logHeight_eq_log_mulHeight, mulHeight_smul_eq_mulHeight x hc]

Depends on / 依赖: logHeight_eq_log_mulHeight, mulHeight_smul_eq_mulHeight
-/
lemma logHeight_smul_eq_logHeight (x : ι -> K) {c : K} (hc : c != 0) :
    logHeight (c • x) = logHeight x := by
  simp only [logHeight_eq_log_mulHeight, mulHeight_smul_eq_mulHeight x hc]

/--
lemma `mulHeight₁_eq_mulHeight` / 引理 `mulHeight₁_eq_mulHeight`

English:
lemma mulHeight₁_eq_mulHeight
  given: (x : K)
  statement: mulHeight₁ x = mulHeight ![x, 1]
  proof: by
  have H (v : AbsoluteValue K Real) (x : K) : v x ⊔ 1 = ⨆ i, v (![x, 1] i) := by
    have (i : Fin 2) : v (![x, 1] i) = ![v x, 1] i := by fin_cases i <;> simp
    simpa [this] using max_eq_iSup (v x) 1
  have hx : ![x, 1] != 0 := by simp
  simp only [mulHeight₁_eq, mulHeight_eq hx, H]

中文:
引理 mulHeight₁_eq_mulHeight
  条件: (x : K)
  结论: mulHeight₁ x = mulHeight ![x, 1]
  证明: by
  have H (v : AbsoluteValue K Real) (x : K) : v x ⊔ 1 = ⨆ i, v (![x, 1] i) := by
    have (i : Fin 2) : v (![x, 1] i) = ![v x, 1] i := by fin_cases i <;> simp
    simpa [this] using max_eq_iSup (v x) 1
  have hx : ![x, 1] != 0 := by simp
  simp only [mulHeight₁_eq, mulHeight_eq hx, H]

Depends on / 依赖: AbsoluteValue, fin_cases, max_eq_iSup, mulHeight_eq
-/
lemma mulHeight₁_eq_mulHeight (x : K) : mulHeight₁ x = mulHeight ![x, 1] := by
  have H (v : AbsoluteValue K Real) (x : K) : v x ⊔ 1 = ⨆ i, v (![x, 1] i) := by
    have (i : Fin 2) : v (![x, 1] i) = ![v x, 1] i := by fin_cases i <;> simp
    simpa [this] using max_eq_iSup (v x) 1
  have hx : ![x, 1] != 0 := by simp
  simp only [mulHeight₁_eq, mulHeight_eq hx, H]

/--
lemma `logHeight₁_eq_logHeight` / 引理 `logHeight₁_eq_logHeight`

English:
lemma logHeight₁_eq_logHeight
  given: (x : K)
  statement: logHeight₁ x = logHeight ![x, 1]
  proof: by
  simp only [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_eq_mulHeight x]

中文:
引理 logHeight₁_eq_logHeight
  条件: (x : K)
  结论: logHeight₁ x = logHeight ![x, 1]
  证明: by
  simp only [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_eq_mulHeight x]

Depends on / 依赖: logHeight_eq_log_mulHeight
-/
lemma logHeight₁_eq_logHeight (x : K) : logHeight₁ x = logHeight ![x, 1] := by
  simp only [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_eq_mulHeight x]

/--
lemma `mulHeight₁_div_eq_mulHeight` / 引理 `mulHeight₁_div_eq_mulHeight`

English:
lemma mulHeight₁_div_eq_mulHeight
  given: (x y : K)
  proof: by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [mulHeight₁_eq_mulHeight, ← mulHeight_smul_eq_mulHeight _ hy]
    simp [mul_div_cancel₀ x hy]

中文:
引理 mulHeight₁_div_eq_mulHeight
  条件: (x y : K)
  证明: by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [mulHeight₁_eq_mulHeight, ← mulHeight_smul_eq_mulHeight _ hy]
    simp [mul_div_cancel₀ x hy]

Depends on / 依赖: eq_or_ne, mulHeight_smul_eq_mulHeight
-/
lemma mulHeight₁_div_eq_mulHeight (x y : K) :
    mulHeight₁ (x / y) = mulHeight ![x, y] := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [mulHeight₁_eq_mulHeight, ← mulHeight_smul_eq_mulHeight _ hy]
    simp [mul_div_cancel₀ x hy]

/--
lemma `logHeight₁_div_eq_logHeight` / 引理 `logHeight₁_div_eq_logHeight`

English:
lemma logHeight₁_div_eq_logHeight
  given: (x y : K)
  proof: by
  rw [logHeight₁_eq_log_mulHeight₁]; rw [logHeight_eq_log_mulHeight]; rw [mulHeight₁_div_eq_mulHeight x y]

中文:
引理 logHeight₁_div_eq_logHeight
  条件: (x y : K)
  证明: by
  rw [logHeight₁_eq_log_mulHeight₁]; rw [logHeight_eq_log_mulHeight]; rw [mulHeight₁_div_eq_mulHeight x y]

Depends on / 依赖: logHeight_eq_log_mulHeight
-/
lemma logHeight₁_div_eq_logHeight (x y : K) :
    logHeight₁ (x / y) = logHeight ![x, y] := by
  rw [logHeight₁_eq_log_mulHeight₁]; rw [logHeight_eq_log_mulHeight]; rw [mulHeight₁_div_eq_mulHeight x y]

/--
lemma `mulHeight_pow` / 引理 `mulHeight_pow`

English:
lemma mulHeight_pow
  given: (x : ι -> K) (n : Nat)
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · cases n <;> simp
  have : Nonempty ι := (ne_iff.mp hx).nonempty
  have H (v : AbsoluteValue K Real) : ⨆ i : ι, v ((x ^ n) i) = (⨆ i, v (x i)) ^ n := by
    simp only [Pi.pow_apply, map_pow]
    simp +singlePass only [← coe_toNNReal _ (v.nonneg _)]
    norm_cast
    exact (pow_left_mono n).map_ciSup_of_continuousAt (continuous_pow n).continuousAt
.symm (Finite.bddAbove_range _)
  have hxn : x ^ n != 0 := by simp [hx]
  simp only [mulHeight_eq hx, mulHeight_eq hxn, H, mul_pow,
finprod_pow hasFiniteMulSupport_iSup_nonarchAbsVal hx, ← Multiset.prod_map_pow]

中文:
引理 mulHeight_pow
  条件: (x : ι -> K) (n : 自然数)
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · cases n <;> simp
  have : Nonempty ι := (ne_iff.mp hx).nonempty
  have H (v : AbsoluteValue K Real) : ⨆ i : ι, v ((x ^ n) i) = (⨆ i, v (x i)) ^ n := by
    simp only [Pi.pow_apply, map_pow]
    simp +singlePass only [← coe_toNNReal _ (v.nonneg _)]
    norm_cast
    exact (pow_left_mono n).map_ciSup_of_continuousAt (continuous_pow n).continuousAt
.symm (Finite.bddAbove_range _)
  have hxn : x ^ n != 0 := by simp [hx]
  simp only [mulHeight_eq hx, mulHeight_eq hxn, H, mul_pow,
finprod_pow hasFiniteMulSupport_iSup_nonarchAbsVal hx, ← Multiset.prod_map_pow]

Depends on / 依赖: AbsoluteValue, Finite, Finite.bddAbove_range, Nonempty, Pi.pow_apply, bddAbove_range, coe_toNNReal, continuousAt, continuous_pow, eq_or_ne, map_ciSup_of_continuousAt, map_pow, mulHeight_eq, mul_pow, ne_iff, ne_iff.mp, nonempty, nonneg, pow_apply, pow_left_mono
-/
lemma mulHeight_pow (x : ι -> K) (n : Nat) :
    mulHeight (x ^ n) = mulHeight x ^ n := by
  rcases eq_or_ne x 0 with rfl | hx
  · cases n <;> simp
  have : Nonempty ι := (ne_iff.mp hx).nonempty
  have H (v : AbsoluteValue K Real) : ⨆ i : ι, v ((x ^ n) i) = (⨆ i, v (x i)) ^ n := by
    simp only [Pi.pow_apply, map_pow]
    simp +singlePass only [← coe_toNNReal _ (v.nonneg _)]
    norm_cast
    exact (pow_left_mono n).map_ciSup_of_continuousAt (continuous_pow n).continuousAt
.symm (Finite.bddAbove_range _)
  have hxn : x ^ n != 0 := by simp [hx]
  simp only [mulHeight_eq hx, mulHeight_eq hxn, H, mul_pow,
finprod_pow hasFiniteMulSupport_iSup_nonarchAbsVal hx, ← Multiset.prod_map_pow]

/--
lemma `logHeight_pow` / 引理 `logHeight_pow`

English:
lemma logHeight_pow
  given: (x : ι -> K) (n : Nat)
  statement: logHeight (x ^ n) = n * logHeight x
  proof: by
  simp [logHeight_eq_log_mulHeight, mulHeight_pow x n]

中文:
引理 logHeight_pow
  条件: (x : ι -> K) (n : 自然数)
  结论: logHeight (x ^ n) = n * logHeight x
  证明: by
  simp [logHeight_eq_log_mulHeight, mulHeight_pow x n]

Depends on / 依赖: logHeight_eq_log_mulHeight, mulHeight_pow
-/
lemma logHeight_pow (x : ι -> K) (n : Nat) : logHeight (x ^ n) = n * logHeight x := by
  simp [logHeight_eq_log_mulHeight, mulHeight_pow x n]

/--
lemma `mulHeight₁_inv` / 引理 `mulHeight₁_inv`

English:
lemma mulHeight₁_inv
  given: (x : K)
  statement: mulHeight₁ (x⁻¹) = mulHeight₁ x
  proof: by
  simp_rw [mulHeight₁_eq_mulHeight]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero]
  · have H : x • ![x⁻¹, 1] = ![1, x] := by ext1 i; fin_cases i <;> simp [hx]
    rw [← mulHeight_smul_eq_mulHeight _ hx]; rw [H]; rw [mulHeight_swap]

中文:
引理 mulHeight₁_inv
  条件: (x : K)
  结论: mulHeight₁ (x⁻¹) = mulHeight₁ x
  证明: by
  simp_rw [mulHeight₁_eq_mulHeight]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero]
  · have H : x • ![x⁻¹, 1] = ![1, x] := by ext1 i; fin_cases i <;> simp [hx]
    rw [← mulHeight_smul_eq_mulHeight _ hx]; rw [H]; rw [mulHeight_swap]

Depends on / 依赖: eq_or_ne, fin_cases, inv_zero, mulHeight_smul_eq_mulHeight, mulHeight_swap, simp_rw
-/
lemma mulHeight₁_inv (x : K) : mulHeight₁ (x⁻¹) = mulHeight₁ x := by
  simp_rw [mulHeight₁_eq_mulHeight]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero]
  · have H : x • ![x⁻¹, 1] = ![1, x] := by ext1 i; fin_cases i <;> simp [hx]
    rw [← mulHeight_smul_eq_mulHeight _ hx]; rw [H]; rw [mulHeight_swap]

/--
lemma `logHeight₁_inv` / 引理 `logHeight₁_inv`

English:
lemma logHeight₁_inv
  given: (x : K)
  statement: logHeight₁ (x⁻¹) = logHeight₁ x
  proof: by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_inv]

中文:
引理 logHeight₁_inv
  条件: (x : K)
  结论: logHeight₁ (x⁻¹) = logHeight₁ x
  证明: by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_inv]
-/
lemma logHeight₁_inv (x : K) : logHeight₁ (x⁻¹) = logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_inv]

/--
lemma `mulHeight₁_pow` / 引理 `mulHeight₁_pow`

English:
lemma mulHeight₁_pow
  given: (x : K) (n : Nat)
  statement: mulHeight₁ (x ^ n) = mulHeight₁ x ^ n
  proof: by
  simp only [mulHeight₁_eq_mulHeight, ← mulHeight_pow _ n]
  congr 1
  ext1 i
  fin_cases i <;> simp

中文:
引理 mulHeight₁_pow
  条件: (x : K) (n : 自然数)
  结论: mulHeight₁ (x ^ n) = mulHeight₁ x ^ n
  证明: by
  simp only [mulHeight₁_eq_mulHeight, ← mulHeight_pow _ n]
  congr 1
  ext1 i
  fin_cases i <;> simp

Depends on / 依赖: fin_cases, mulHeight_pow
-/
lemma mulHeight₁_pow (x : K) (n : Nat) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n := by
  simp only [mulHeight₁_eq_mulHeight, ← mulHeight_pow _ n]
  congr 1
  ext1 i
  fin_cases i <;> simp

/--
lemma `logHeight₁_pow` / 引理 `logHeight₁_pow`

English:
lemma logHeight₁_pow
  given: (x : K) (n : Nat)
  statement: logHeight₁ (x ^ n) = n * logHeight₁ x
  proof: by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_pow, log_pow]

中文:
引理 logHeight₁_pow
  条件: (x : K) (n : 自然数)
  结论: logHeight₁ (x ^ n) = n * logHeight₁ x
  证明: by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_pow, log_pow]

Depends on / 依赖: log_pow
-/
lemma logHeight₁_pow (x : K) (n : Nat) : logHeight₁ (x ^ n) = n * logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_pow, log_pow]

/--
lemma `mulHeight₁_zpow` / 引理 `mulHeight₁_zpow`

English:
lemma mulHeight₁_zpow
  given: (x : K) (n : Int)
  statement: mulHeight₁ (x ^ n) = mulHeight₁ x ^ n.natAbs
  proof: by
  rcases le_or_gt 0 n with h | h
  · lift n to Nat using h
    rw [zpow_natCast]; rw [mulHeight₁_pow]; rw [Int.natAbs_natCast]
  · nth_rewrite 1 [show n = -n.natAbs by grind]
    rw [zpow_neg]; rw [mulHeight₁_inv]; rw [zpow_natCast]; rw [mulHeight₁_pow]

中文:
引理 mulHeight₁_zpow
  条件: (x : K) (n : 整数)
  结论: mulHeight₁ (x ^ n) = mulHeight₁ x ^ n.natAbs
  证明: by
  rcases le_or_gt 0 n with h | h
  · lift n to Nat using h
    rw [zpow_natCast]; rw [mulHeight₁_pow]; rw [Int.natAbs_natCast]
  · nth_rewrite 1 [show n = -n.natAbs by grind]
    rw [zpow_neg]; rw [mulHeight₁_inv]; rw [zpow_natCast]; rw [mulHeight₁_pow]

Depends on / 依赖: Int.natAbs_natCast, le_or_gt, n.natAbs, natAbs, natAbs_natCast, nth_rewrite, zpow_natCast, zpow_neg
-/
lemma mulHeight₁_zpow (x : K) (n : Int) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n.natAbs := by
  rcases le_or_gt 0 n with h | h
  · lift n to Nat using h
    rw [zpow_natCast]; rw [mulHeight₁_pow]; rw [Int.natAbs_natCast]
  · nth_rewrite 1 [show n = -n.natAbs by grind]
    rw [zpow_neg]; rw [mulHeight₁_inv]; rw [zpow_natCast]; rw [mulHeight₁_pow]

/--
lemma `logHeight₁_zpow` / 引理 `logHeight₁_zpow`

English:
lemma logHeight₁_zpow
  given: (x : K) (n : Int)
  statement: logHeight₁ (x ^ n) = n.natAbs * logHeight₁ x
  proof: by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_zpow, log_pow]

中文:
引理 logHeight₁_zpow
  条件: (x : K) (n : 整数)
  结论: logHeight₁ (x ^ n) = n.natAbs * logHeight₁ x
  证明: by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_zpow, log_pow]

Depends on / 依赖: log_pow
-/
lemma logHeight₁_zpow (x : K) (n : Int) : logHeight₁ (x ^ n) = n.natAbs * logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_zpow, log_pow]

end Height

/-!
### Heights and "Segre embedding"

We show that the multiplicative height of `fun (i, j) ↦ x i * y j` is the product of the
multiplicative heights of `x` and `y` (and the analogous statement for logarithmic heights).

We also show the corresponding statements for product with arbitrarily many factors.
-/

namespace Height

open Height.AdmissibleAbsValues Function

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

section many

universe u v

variable {α : Type u} [Fintype α] {ι : α -> Type v} [forall a, Finite (ι a)]

open Finset in
/--
lemma `mulHeight_fun_prod_eq` / 引理 `mulHeight_fun_prod_eq`

English:
lemma mulHeight_fun_prod_eq
  given: {x : (a : α) -> ι a -> K} (hx : forall a, x a != 0)
  proof: by
  rw [mulHeight_eq ?h₁]
  case h₁ =>
    simp_rw [ne_iff, Pi.zero_def] at hx ⊢
    choose f hf using hx
    exact ⟨f, prod_ne_zero_iff.mpr fun a _ => hf a⟩
  simp_rw [_root_.map_prod, Real.iSup_prod_eq_prod_iSup_of_nonnegHomClass]
  rw [Multiset.prod_map_prod]; rw [finprod_prod_comm _ _ fun b _ => hasFiniteMulSupport_iSup_nonarchAbsVal (hx b)]; rw [← prod_mul_distrib]
  exact prod_congr rfl fun a _ => by rw [mulHeight_eq (hx a)]

中文:
引理 mulHeight_fun_prod_eq
  条件: {x : (a : α) -> ι a -> K} (hx : 对任意 a, x a != 0)
  证明: by
  rw [mulHeight_eq ?h₁]
  case h₁ =>
    simp_rw [ne_iff, Pi.zero_def] at hx ⊢
    choose f hf using hx
    exact ⟨f, prod_ne_zero_iff.mpr fun a _ => hf a⟩
  simp_rw [_root_.map_prod, Real.iSup_prod_eq_prod_iSup_of_nonnegHomClass]
  rw [Multiset.prod_map_prod]; rw [finprod_prod_comm _ _ fun b _ => hasFiniteMulSupport_iSup_nonarchAbsVal (hx b)]; rw [← prod_mul_distrib]
  exact prod_congr rfl fun a _ => by rw [mulHeight_eq (hx a)]

Depends on / 依赖: Multiset, Multiset.prod_map_prod, Pi.zero_def, Real.iSup_prod_eq_prod_iSup_of_nonnegHomClass, _root_, _root_.map_prod, finprod_prod_comm, hasFiniteMulSupport_iSup_nonarchAbsVal, iSup_prod_eq_prod_iSup_of_nonnegHomClass, map_prod, mulHeight_eq, ne_iff, prod_congr, prod_map_prod, prod_mul_distrib, prod_ne_zero_iff, prod_ne_zero_iff.mpr, simp_rw, zero_def
-/
lemma mulHeight_fun_prod_eq {x : (a : α) -> ι a -> K} (hx : forall a, x a != 0) :
    mulHeight (fun I : (a : α) -> ι a => ∏ a, x a (I a)) = ∏ a, mulHeight (x a) := by
  rw [mulHeight_eq ?h₁]
  case h₁ =>
    simp_rw [ne_iff, Pi.zero_def] at hx ⊢
    choose f hf using hx
    exact ⟨f, prod_ne_zero_iff.mpr fun a _ => hf a⟩
  simp_rw [_root_.map_prod, Real.iSup_prod_eq_prod_iSup_of_nonnegHomClass]
  rw [Multiset.prod_map_prod]; rw [finprod_prod_comm _ _ fun b _ => hasFiniteMulSupport_iSup_nonarchAbsVal (hx b)]; rw [← prod_mul_distrib]
  exact prod_congr rfl fun a _ => by rw [mulHeight_eq (hx a)]

open Real in
/--
lemma `logHeight_fun_prod_eq` / 引理 `logHeight_fun_prod_eq`

English:
lemma logHeight_fun_prod_eq
  given: {x : (a : α) -> ι a -> K} (hx : forall a, x a != 0)
  proof: by
  simp only [logHeight_eq_log_mulHeight]
  rw [← log_prod fun a _ => mulHeight_ne_zero _]
exact congrArg log mulHeight_fun_prod_eq hx

中文:
引理 logHeight_fun_prod_eq
  条件: {x : (a : α) -> ι a -> K} (hx : 对任意 a, x a != 0)
  证明: by
  simp only [logHeight_eq_log_mulHeight]
  rw [← log_prod fun a _ => mulHeight_ne_zero _]
exact congrArg log mulHeight_fun_prod_eq hx

Depends on / 依赖: logHeight_eq_log_mulHeight, log_prod, mulHeight_fun_prod_eq, mulHeight_ne_zero
-/
lemma logHeight_fun_prod_eq {x : (a : α) -> ι a -> K} (hx : forall a, x a != 0) :
    logHeight (fun I : (a : α) -> ι a => ∏ a, x a (I a)) = ∑ a, logHeight (x a) := by
  simp only [logHeight_eq_log_mulHeight]
  rw [← log_prod fun a _ => mulHeight_ne_zero _]
exact congrArg log mulHeight_fun_prod_eq hx

end many

section two

/-
Note: One could try to deduce the binary case from the general case above,
but this leads into dependent type shenanigans (because `ι` and `ι'` can live in different
universes) that would likely obfuscate the proofs more than simplify them.
-/

variable {ι ι' : Type*} [Finite ι] [Finite ι']

/--
lemma `mulHeight_fun_mul_eq` / 引理 `mulHeight_fun_mul_eq`

English:
lemma mulHeight_fun_mul_eq
  given: {x : ι -> K} (hx : x != 0) {y : ι' -> K} (hy : y != 0)
  proof: by
  have hxy : (fun a : ι × ι' => x a.1 * y a.2) != 0 := by
    obtain ⟨i, hi⟩ := ne_iff.mp hx
    obtain ⟨j, hj⟩ := ne_iff.mp hy
    exact ne_iff.mpr ⟨⟨i, j⟩, mul_ne_zero hi hj⟩
  rw [mulHeight_eq hx]; rw [mulHeight_eq hy]; rw [mulHeight_eq hxy]; rw [mul_mul_mul_comm]; rw [← Multiset.prod_map_mul]; rw [← finprod_mul_distrib
        (hasFiniteMulSupport_iSup_nonarchAbsVal hx) (hasFiniteMulSupport_iSup_nonarchAbsVal hy)]
  congr <;> ext1 v
  · exact Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v x y
  · exact Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v.val x y

中文:
引理 mulHeight_fun_mul_eq
  条件: {x : ι -> K} (hx : x != 0) {y : ι' -> K} (hy : y != 0)
  证明: by
  have hxy : (fun a : ι × ι' => x a.1 * y a.2) != 0 := by
    obtain ⟨i, hi⟩ := ne_iff.mp hx
    obtain ⟨j, hj⟩ := ne_iff.mp hy
    exact ne_iff.mpr ⟨⟨i, j⟩, mul_ne_zero hi hj⟩
  rw [mulHeight_eq hx]; rw [mulHeight_eq hy]; rw [mulHeight_eq hxy]; rw [mul_mul_mul_comm]; rw [← Multiset.prod_map_mul]; rw [← finprod_mul_distrib
        (hasFiniteMulSupport_iSup_nonarchAbsVal hx) (hasFiniteMulSupport_iSup_nonarchAbsVal hy)]
  congr <;> ext1 v
  · exact Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v x y
  · exact Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v.val x y

Depends on / 依赖: Multiset, Multiset.prod_map_mul, Real.iSup_fun_m, Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg, finprod_mul_distrib, hasFiniteMulSupport_iSup_nonarchAbsVal, iSup_fun_m, iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg, mulHeight_eq, mul_mul_mul_comm, mul_ne_zero, ne_iff, ne_iff.mp, ne_iff.mpr, prod_map_mul
-/
lemma mulHeight_fun_mul_eq {x : ι -> K} (hx : x != 0) {y : ι' -> K} (hy : y != 0) :
    mulHeight (fun a : ι × ι' => x a.1 * y a.2) = mulHeight x * mulHeight y := by
  have hxy : (fun a : ι × ι' => x a.1 * y a.2) != 0 := by
    obtain ⟨i, hi⟩ := ne_iff.mp hx
    obtain ⟨j, hj⟩ := ne_iff.mp hy
    exact ne_iff.mpr ⟨⟨i, j⟩, mul_ne_zero hi hj⟩
  rw [mulHeight_eq hx]; rw [mulHeight_eq hy]; rw [mulHeight_eq hxy]; rw [mul_mul_mul_comm]; rw [← Multiset.prod_map_mul]; rw [← finprod_mul_distrib
        (hasFiniteMulSupport_iSup_nonarchAbsVal hx) (hasFiniteMulSupport_iSup_nonarchAbsVal hy)]
  congr <;> ext1 v
  · exact Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v x y
  · exact Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v.val x y

open Real in
/--
lemma `logHeight_fun_mul_eq` / 引理 `logHeight_fun_mul_eq`

English:
lemma logHeight_fun_mul_eq
  given: {x : ι -> K} (hx : x != 0) {y : ι' -> K} (hy : y != 0)
  proof: by
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  rw [mulHeight_fun_mul_eq hx hy]

中文:
引理 logHeight_fun_mul_eq
  条件: {x : ι -> K} (hx : x != 0) {y : ι' -> K} (hy : y != 0)
  证明: by
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  rw [mulHeight_fun_mul_eq hx hy]

Depends on / 依赖: logHeight_eq_log_mulHeight, mulHeight_fun_mul_eq
-/
lemma logHeight_fun_mul_eq {x : ι -> K} (hx : x != 0) {y : ι' -> K} (hy : y != 0) :
    logHeight (fun a : ι × ι' => x a.1 * y a.2) = logHeight x + logHeight y := by
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  rw [mulHeight_fun_mul_eq hx hy]

end two

/-!
### Height bound for products
-/

variable {ι : Type*}

/-- The multiplicative height of the pointwise negative of a tuple
equals its multiplicative height. -/
@[simp]
/--
lemma `mulHeight_neg` / 引理 `mulHeight_neg`

English:
lemma mulHeight_neg
  given: (x : ι -> K)
  statement: mulHeight (-x) = mulHeight x
  proof: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  simp [mulHeight_eq hx, mulHeight_eq <| neg_ne_zero.mpr hx]

中文:
引理 mulHeight_neg
  条件: (x : ι -> K)
  结论: mulHeight (-x) = mulHeight x
  证明: by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  simp [mulHeight_eq hx, mulHeight_eq <| neg_ne_zero.mpr hx]

Depends on / 依赖: eq_or_ne, mulHeight_eq, neg_ne_zero, neg_ne_zero.mpr
-/
lemma mulHeight_neg (x : ι -> K) : mulHeight (-x) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  simp [mulHeight_eq hx, mulHeight_eq <| neg_ne_zero.mpr hx]

/-- The logarithmic height of the pointwise negative of a tuple
equals its logarithmic height. -/
@[simp]
/--
lemma `logHeight_neg` / 引理 `logHeight_neg`

English:
lemma logHeight_neg
  given: (x : ι -> K)
  statement: logHeight (-x) = logHeight x
  proof: by
  simp [logHeight_eq_log_mulHeight]

中文:
引理 logHeight_neg
  条件: (x : ι -> K)
  结论: logHeight (-x) = logHeight x
  证明: by
  simp [logHeight_eq_log_mulHeight]

Depends on / 依赖: logHeight_eq_log_mulHeight
-/
lemma logHeight_neg (x : ι -> K) : logHeight (-x) = logHeight x := by
  simp [logHeight_eq_log_mulHeight]

section tuples

variable [Finite ι]

/--
lemma `mulHeight_mul_le` / 引理 `mulHeight_mul_le`

English:
lemma mulHeight_mul_le
  given: (x y : ι -> K)
  statement: mulHeight (x * y) <= mulHeight x * mulHeight y
  proof: by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using one_le_mulHeight y
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using one_le_mulHeight x
  rw [← mulHeight_fun_mul_eq hx hy]; rw [show x * y = (fun a => x a.1 * y a.2) ∘ Function.diag by ext1; simp]
  exact mulHeight_comp_le ..

中文:
引理 mulHeight_mul_le
  条件: (x y : ι -> K)
  结论: mulHeight (x * y) <= mulHeight x * mulHeight y
  证明: by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using one_le_mulHeight y
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using one_le_mulHeight x
  rw [← mulHeight_fun_mul_eq hx hy]; rw [show x * y = (fun a => x a.1 * y a.2) ∘ Function.diag by ext1; simp]
  exact mulHeight_comp_le ..

Depends on / 依赖: Function, Function.diag, eq_or_ne, isEmpty_or_nonempty, mulHeight_comp_le, mulHeight_fun_mul_eq, one_le_mulHeight
-/
lemma mulHeight_mul_le (x y : ι -> K) : mulHeight (x * y) <= mulHeight x * mulHeight y := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using one_le_mulHeight y
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using one_le_mulHeight x
  rw [← mulHeight_fun_mul_eq hx hy]; rw [show x * y = (fun a => x a.1 * y a.2) ∘ Function.diag by ext1; simp]
  exact mulHeight_comp_le ..

open Real in
/--
lemma `logHeight_mul_le` / 引理 `logHeight_mul_le`

English:
lemma logHeight_mul_le
  given: (x y : ι -> K)
  statement: logHeight (x * y) <= logHeight x + logHeight y
  proof: by
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
exact log_le_log (by positivity) mulHeight_mul_le ..

中文:
引理 logHeight_mul_le
  条件: (x y : ι -> K)
  结论: logHeight (x * y) <= logHeight x + logHeight y
  证明: by
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
exact log_le_log (by positivity) mulHeight_mul_le ..

Depends on / 依赖: logHeight_eq_log_mulHeight, log_le_log, mulHeight_mul_le
-/
lemma logHeight_mul_le (x y : ι -> K) : logHeight (x * y) <= logHeight x + logHeight y := by
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
exact log_le_log (by positivity) mulHeight_mul_le ..

end tuples

/--
lemma `mulHeight₁_mul_le` / 引理 `mulHeight₁_mul_le`

English:
lemma mulHeight₁_mul_le
  given: (x y : K)
  statement: mulHeight₁ (x * y) <= mulHeight₁ x * mulHeight₁ y
  proof: by
  simp only [mulHeight₁_eq_mulHeight]
  rw [show ![x * y]; rw [1] = ![x, 1] * ![y, 1] by ext i; fin_cases i <;> simp]
  exact mulHeight_mul_le ![x, 1] ![y, 1]

中文:
引理 mulHeight₁_mul_le
  条件: (x y : K)
  结论: mulHeight₁ (x * y) <= mulHeight₁ x * mulHeight₁ y
  证明: by
  simp only [mulHeight₁_eq_mulHeight]
  rw [show ![x * y]; rw [1] = ![x, 1] * ![y, 1] by ext i; fin_cases i <;> simp]
  exact mulHeight_mul_le ![x, 1] ![y, 1]

Depends on / 依赖: fin_cases, mulHeight_mul_le
-/
lemma mulHeight₁_mul_le (x y : K) : mulHeight₁ (x * y) <= mulHeight₁ x * mulHeight₁ y := by
  simp only [mulHeight₁_eq_mulHeight]
  rw [show ![x * y]; rw [1] = ![x, 1] * ![y, 1] by ext i; fin_cases i <;> simp]
  exact mulHeight_mul_le ![x, 1] ![y, 1]

open Real in
/--
lemma `logHeight₁_mul_le` / 引理 `logHeight₁_mul_le`

English:
lemma logHeight₁_mul_le
  given: (x y : K)
  statement: logHeight₁ (x * y) <= logHeight₁ x + logHeight₁ y
  proof: by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
exact log_le_log (by positivity) mulHeight₁_mul_le ..

中文:
引理 logHeight₁_mul_le
  条件: (x y : K)
  结论: logHeight₁ (x * y) <= logHeight₁ x + logHeight₁ y
  证明: by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
exact log_le_log (by positivity) mulHeight₁_mul_le ..

Depends on / 依赖: log_le_log
-/
lemma logHeight₁_mul_le (x y : K) : logHeight₁ (x * y) <= logHeight₁ x + logHeight₁ y := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
exact log_le_log (by positivity) mulHeight₁_mul_le ..

/--
lemma `mulHeight₁_prod_le` / 引理 `mulHeight₁_prod_le`

English:
lemma mulHeight₁_prod_le
  given: (s : Finset ι) (x : ι -> K)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    simp only [Finset.prod_insert hb]
    grw [← ih]
    exact mulHeight₁_mul_le ..

中文:
引理 mulHeight₁_prod_le
  条件: (s : 有限集 ι) (x : ι -> K)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    simp only [Finset.prod_insert hb]
    grw [← ih]
    exact mulHeight₁_mul_le ..

Depends on / 依赖: Finset, Finset.induction, Finset.prod_insert, classical, insert, prod_insert
-/
lemma mulHeight₁_prod_le (s : Finset ι) (x : ι -> K) :
    mulHeight₁ (∏ i in s, x i) <= ∏ i in s, mulHeight₁ (x i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    simp only [Finset.prod_insert hb]
    grw [← ih]
    exact mulHeight₁_mul_le ..

open Real in
/--
lemma `logHeight₁_prod_le` / 引理 `logHeight₁_prod_le`

English:
lemma logHeight₁_prod_le
  given: (s : Finset ι) (x : ι -> K)
  proof: by
  simp only [logHeight₁_eq_log_mulHeight₁]
  rw [← log_prod (fun _ _ => by positivity)]
exact log_le_log (by positivity) mulHeight₁_prod_le ..

中文:
引理 logHeight₁_prod_le
  条件: (s : 有限集 ι) (x : ι -> K)
  证明: by
  simp only [logHeight₁_eq_log_mulHeight₁]
  rw [← log_prod (fun _ _ => by positivity)]
exact log_le_log (by positivity) mulHeight₁_prod_le ..

Depends on / 依赖: log_le_log, log_prod
-/
lemma logHeight₁_prod_le (s : Finset ι) (x : ι -> K) :
    logHeight₁ (∏ i in s, x i) <= ∑ i in s, logHeight₁ (x i) := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  rw [← log_prod (fun _ _ => by positivity)]
exact log_le_log (by positivity) mulHeight₁_prod_le ..

end Height

/-!
### Bounds for the height of sums of field elements

We prove the general case (finite sums of arbitrary length) first and deduce the result
for sums of two elements from it.
-/

namespace Finset

variable {R S : Type*} [Semiring R] [CommSemiring S] [LinearOrder S] [IsOrderedRing S]

/--
lemma `max_abv_sum_one_le` / 引理 `max_abv_sum_one_le`

English:
lemma max_abv_sum_one_le
  statement: [CharZero S] (v : AbsoluteValue R S) {ι : Type*} {s : Finset ι}
  proof: by
  refine sup_le ?_ ?_
  · rw [← nsmul_eq_mul, ← sum_const]
    grw [v.sum_le s x]
    gcongr with i hi
    exact le_prod_max_one hi fun i => v (x i)
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · simp [hs]
    · exact s.one_le_prod fun _ _ => le_max_right ..

中文:
引理 max_abv_sum_one_le
  结论: [特征零 S] (v : 绝对值 R S) {ι : 类型} {s : 有限集 ι}
  证明: by
  refine sup_le ?_ ?_
  · rw [← nsmul_eq_mul, ← sum_const]
    grw [v.sum_le s x]
    gcongr with i hi
    exact le_prod_max_one hi fun i => v (x i)
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · simp [hs]
    · exact s.one_le_prod fun _ _ => le_max_right ..

Depends on / 依赖: le_max_right, le_prod_max_one, mul_one, nsmul_eq_mul, nth_rewrite, one_le_prod, s.one_le_prod, sum_const, sum_le, sup_le, v.sum_le
-/
lemma max_abv_sum_one_le [CharZero S] (v : AbsoluteValue R S) {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) (x : ι -> R) :
    max (v (∑ i in s, x i)) 1 <= #s * ∏ i in s, max (v (x i)) 1 := by
  refine sup_le ?_ ?_
  · rw [← nsmul_eq_mul, ← sum_const]
    grw [v.sum_le s x]
    gcongr with i hi
    exact le_prod_max_one hi fun i => v (x i)
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · simp [hs]
    · exact s.one_le_prod fun _ _ => le_max_right ..

/--
lemma `max_abv_sum_one_le_of_isNonarchimedean` / 引理 `max_abv_sum_one_le_of_isNonarchimedean`

English:
lemma max_abv_sum_one_le_of_isNonarchimedean
  statement: {v : AbsoluteValue R S} (hv : IsNonarchimedean v)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
refine sup_le ?_ s.one_le_prod fun _ _ => le_max_right ..
  grw [hv.apply_sum_le_sup hs]
  exact sup'_le hs (fun i => v (x i)) fun i hi => le_prod_max_one hi fun i => v (x i)

中文:
引理 max_abv_sum_one_le_of_isNonarchimedean
  结论: {v : 绝对值 R S} (hv : IsNonarchimedean v)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
refine sup_le ?_ s.one_le_prod fun _ _ => le_max_right ..
  grw [hv.apply_sum_le_sup hs]
  exact sup'_le hs (fun i => v (x i)) fun i hi => le_prod_max_one hi fun i => v (x i)

Depends on / 依赖: apply_sum_le_sup, eq_empty_or_nonempty, hv.apply_sum_le_sup, le_max_right, le_prod_max_one, one_le_prod, s.eq_empty_or_nonempty, s.one_le_prod, sup_le
-/
lemma max_abv_sum_one_le_of_isNonarchimedean {v : AbsoluteValue R S} (hv : IsNonarchimedean v)
    {ι : Type*} (s : Finset ι) (x : ι -> R) :
    max (v (∑ i in s, x i)) 1 <= ∏ i in s, max (v (x i)) 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
refine sup_le ?_ s.one_le_prod fun _ _ => le_max_right ..
  grw [hv.apply_sum_le_sup hs]
  exact sup'_le hs (fun i => v (x i)) fun i hi => le_prod_max_one hi fun i => v (x i)

end Finset

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

open AdmissibleAbsValues Real

open Finset Multiset in
/--
lemma `mulHeight₁_sum_le` / 引理 `mulHeight₁_sum_le`

English:
lemma mulHeight₁_sum_le
  given: {α : Type*} {s : Finset α} (hs : s.Nonempty) (x : α -> K)
  proof: by
  simp only [mulHeight₁_eq, totalWeight]
  rw [prod_mul_distrib]; rw [← prod_replicate]; rw [← map_const]; rw [← finprod_prod_comm _ _ (by fun_prop)]; rw [← prod_map_prod]; rw [← mul_assoc]; rw [← prod_map_mul]
  simp only [Function.const_apply]
  gcongr
  · exact finprod_nonneg fun _ => by positivity
  · exact prod_map_nonneg fun _ h => by positivity
  · exact prod_map_le_prod_map₀ _ _ (fun _ _ => by positivity) fun _ _ => max_abv_sum_one_le _ hs x
· exact finprod_le_finprod (by fun_prop) (fun _ => by grind) (by fun_prop)
      fun v => max_abv_sum_one_le_of_isNonarchimedean (isNonarchimedean _ v.prop) _ x

中文:
引理 mulHeight₁_sum_le
  条件: {α : 类型} {s : 有限集 α} (hs : s.非空) (x : α -> K)
  证明: by
  simp only [mulHeight₁_eq, totalWeight]
  rw [prod_mul_distrib]; rw [← prod_replicate]; rw [← map_const]; rw [← finprod_prod_comm _ _ (by fun_prop)]; rw [← prod_map_prod]; rw [← mul_assoc]; rw [← prod_map_mul]
  simp only [Function.const_apply]
  gcongr
  · exact finprod_nonneg fun _ => by positivity
  · exact prod_map_nonneg fun _ h => by positivity
  · exact prod_map_le_prod_map₀ _ _ (fun _ _ => by positivity) fun _ _ => max_abv_sum_one_le _ hs x
· exact finprod_le_finprod (by fun_prop) (fun _ => by grind) (by fun_prop)
      fun v => max_abv_sum_one_le_of_isNonarchimedean (isNonarchimedean _ v.prop) _ x

Depends on / 依赖: Function, Function.const_apply, const_apply, finprod_le_finprod, finprod_nonneg, finprod_prod_comm, fun_prop, map_const, max_abv_sum_one_le, mul_assoc, prod_map_mul, prod_map_nonneg, prod_map_prod, prod_mul_distrib, prod_replicate, totalWeight
-/
lemma mulHeight₁_sum_le {α : Type*} {s : Finset α} (hs : s.Nonempty) (x : α -> K) :
    mulHeight₁ (∑ a in s, x a) <= #s ^ (totalWeight K) * ∏ a in s, mulHeight₁ (x a) := by
  simp only [mulHeight₁_eq, totalWeight]
  rw [prod_mul_distrib]; rw [← prod_replicate]; rw [← map_const]; rw [← finprod_prod_comm _ _ (by fun_prop)]; rw [← prod_map_prod]; rw [← mul_assoc]; rw [← prod_map_mul]
  simp only [Function.const_apply]
  gcongr
  · exact finprod_nonneg fun _ => by positivity
  · exact prod_map_nonneg fun _ h => by positivity
  · exact prod_map_le_prod_map₀ _ _ (fun _ _ => by positivity) fun _ _ => max_abv_sum_one_le _ hs x
· exact finprod_le_finprod (by fun_prop) (fun _ => by grind) (by fun_prop)
      fun v => max_abv_sum_one_le_of_isNonarchimedean (isNonarchimedean _ v.prop) _ x

open Finset in
/--
lemma `logHeight₁_sum_le` / 引理 `logHeight₁_sum_le`

English:
lemma logHeight₁_sum_le
  given: {α : Type*} (s : Finset α) (x : α -> K)
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  simp only [logHeight₁_eq_log_mulHeight₁]
  have : forall a in s, mulHeight₁ (x a) != 0 := fun _ _ => by positivity
  have : (#s : Real) ^ totalWeight K != 0 := by simp [hs.ne_empty]
  pull (disch := first | assumption | positivity) log
exact (log_le_log <| by positivity) mulHeight₁_sum_le hs x

中文:
引理 logHeight₁_sum_le
  条件: {α : 类型} (s : 有限集 α) (x : α -> K)
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  simp only [logHeight₁_eq_log_mulHeight₁]
  have : forall a in s, mulHeight₁ (x a) != 0 := fun _ _ => by positivity
  have : (#s : Real) ^ totalWeight K != 0 := by simp [hs.ne_empty]
  pull (disch := first | assumption | positivity) log
exact (log_le_log <| by positivity) mulHeight₁_sum_le hs x

Depends on / 依赖: eq_empty_or_nonempty, hs.ne_empty, log_le_log, ne_empty, s.eq_empty_or_nonempty, totalWeight
-/
lemma logHeight₁_sum_le {α : Type*} (s : Finset α) (x : α -> K) :
    logHeight₁ (∑ a in s, x a) <= (totalWeight K) * log #s + ∑ a in s, logHeight₁ (x a) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  simp only [logHeight₁_eq_log_mulHeight₁]
  have : forall a in s, mulHeight₁ (x a) != 0 := fun _ _ => by positivity
  have : (#s : Real) ^ totalWeight K != 0 := by simp [hs.ne_empty]
  pull (disch := first | assumption | positivity) log
exact (log_le_log <| by positivity) mulHeight₁_sum_le hs x

/-- The multiplicative height of `-x` is the same as that of `x`. -/
@[simp]
/--
lemma `mulHeight₁_neg` / 引理 `mulHeight₁_neg`

English:
lemma mulHeight₁_neg
  given: (x : K)
  statement: mulHeight₁ (-x) = mulHeight₁ x
  proof: by
  simp [mulHeight₁_eq]

中文:
引理 mulHeight₁_neg
  条件: (x : K)
  结论: mulHeight₁ (-x) = mulHeight₁ x
  证明: by
  simp [mulHeight₁_eq]
-/
lemma mulHeight₁_neg (x : K) : mulHeight₁ (-x) = mulHeight₁ x := by
  simp [mulHeight₁_eq]

/-- The logarithmic height of `-x` is the same as that of `x`. -/
@[simp]
/--
lemma `logHeight₁_neg` / 引理 `logHeight₁_neg`

English:
lemma logHeight₁_neg
  given: (x : K)
  statement: logHeight₁ (-x) = logHeight₁ x
  proof: by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_neg]

中文:
引理 logHeight₁_neg
  条件: (x : K)
  结论: logHeight₁ (-x) = logHeight₁ x
  证明: by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_neg]
-/
lemma logHeight₁_neg (x : K) : logHeight₁ (-x) = logHeight₁ x := by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_neg]

/--
lemma `mulHeight₁_add_le` / 引理 `mulHeight₁_add_le`

English:
lemma mulHeight₁_add_le
  given: (x y : K)
  proof: by
  rw [show x + y = Finset.univ.sum ![x]; rw [y] by simp, mul_assoc]
  grw [mulHeight₁_sum_le Finset.univ_nonempty ![x, y]]
  simp

中文:
引理 mulHeight₁_add_le
  条件: (x y : K)
  证明: by
  rw [show x + y = Finset.univ.sum ![x]; rw [y] by simp, mul_assoc]
  grw [mulHeight₁_sum_le Finset.univ_nonempty ![x, y]]
  simp

Depends on / 依赖: Finset, Finset.univ.sum, Finset.univ_nonempty, mul_assoc, univ_nonempty
-/
lemma mulHeight₁_add_le (x y : K) :
    mulHeight₁ (x + y) <= 2 ^ totalWeight K * mulHeight₁ x * mulHeight₁ y := by
  rw [show x + y = Finset.univ.sum ![x]; rw [y] by simp, mul_assoc]
  grw [mulHeight₁_sum_le Finset.univ_nonempty ![x, y]]
  simp

/--
lemma `logHeight₁_add_le` / 引理 `logHeight₁_add_le`

English:
lemma logHeight₁_add_le
  given: (x y : K)
  proof: by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
exact (log_le_log <| by positivity) mulHeight₁_add_le ..

中文:
引理 logHeight₁_add_le
  条件: (x y : K)
  证明: by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
exact (log_le_log <| by positivity) mulHeight₁_add_le ..

Depends on / 依赖: log_le_log
-/
lemma logHeight₁_add_le (x y : K) :
    logHeight₁ (x + y) <= totalWeight K * log 2 + logHeight₁ x + logHeight₁ y := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
exact (log_le_log <| by positivity) mulHeight₁_add_le ..

/--
lemma `mulHeight₁_sub_le` / 引理 `mulHeight₁_sub_le`

English:
lemma mulHeight₁_sub_le
  given: (x y : K)
  proof: by
  rw [sub_eq_add_neg]; rw [← mulHeight₁_neg y]
  exact mulHeight₁_add_le x (-y)

中文:
引理 mulHeight₁_sub_le
  条件: (x y : K)
  证明: by
  rw [sub_eq_add_neg]; rw [← mulHeight₁_neg y]
  exact mulHeight₁_add_le x (-y)

Depends on / 依赖: sub_eq_add_neg
-/
lemma mulHeight₁_sub_le (x y : K) :
    mulHeight₁ (x - y) <= 2 ^ totalWeight K * mulHeight₁ x * mulHeight₁ y := by
  rw [sub_eq_add_neg]; rw [← mulHeight₁_neg y]
  exact mulHeight₁_add_le x (-y)

/--
lemma `logHeight₁_sub_le` / 引理 `logHeight₁_sub_le`

English:
lemma logHeight₁_sub_le
  given: (x y : K)
  proof: by
  rw [sub_eq_add_neg]; rw [← logHeight₁_neg y]
  exact logHeight₁_add_le x (-y)

中文:
引理 logHeight₁_sub_le
  条件: (x y : K)
  证明: by
  rw [sub_eq_add_neg]; rw [← logHeight₁_neg y]
  exact logHeight₁_add_le x (-y)

Depends on / 依赖: sub_eq_add_neg
-/
lemma logHeight₁_sub_le (x y : K) :
    logHeight₁ (x - y) <= totalWeight K * log 2 + logHeight₁ x + logHeight₁ y := by
  rw [sub_eq_add_neg]; rw [← logHeight₁_neg y]
  exact logHeight₁_add_le x (-y)

end Height
