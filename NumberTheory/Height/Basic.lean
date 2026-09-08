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

/-- A type class capturing an admissible family of absolute values. -/
/-
**Height.AdmissibleAbsValues** 是 Mathlib 中的一个归纳类型，位于命名空间 `Height`。
形式化陈述：(K : Type u_1) → [Field K] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type class capturing an admissible family of absolute values.
-/
class AdmissibleAbsValues (K : Type*) [Field K] where
  /-- The archimedean absolute values as a multiset of `ℝ`-valued absolute values on `K`. -/
  archAbsVal : Multiset (AbsoluteValue K ℝ)
  /-- The nonarchimedean absolute values as a set of `ℝ`-valued absolute values on `K`. -/
  nonarchAbsVal : Set (AbsoluteValue K ℝ)
  /-- The nonarchimedean absolute values are indeed nonarchimedean. -/
  isNonarchimedean : ∀ v ∈ nonarchAbsVal, IsNonarchimedean v
  /-- Only finitely many (nonarchimedean) absolute values are `≠ 1` for any nonzero `x : K`. -/
  hasFiniteMulSupport {x : K} (_ : x ≠ 0) : (fun v : nonarchAbsVal ↦ v.val x).HasFiniteMulSupport
  /-- The product formula. The archimedean absolute values are taken with their multiplicity. -/
  product_formula {x : K} (_ : x ≠ 0) :
      (archAbsVal.map (· x)).prod * ∏ᶠ v : nonarchAbsVal, v.val x = 1

open AdmissibleAbsValues Real Function

@[deprecated (since := "2026-03-03")] alias
  AdmissibleAbsValues.mulSupport_finite := AdmissibleAbsValues.hasFiniteMulSupport

attribute [fun_prop] hasFiniteMulSupport

variable (K : Type*) [Field K] [AdmissibleAbsValues K]

/-- The `totalWeight` of a field with `AdmissibleAbsValues` is the sum of the multiplicities of
the archimedean places. -/
/-
**Height.totalWeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：(K : Type u_1) → [inst : Field K] → [Height.AdmissibleAbsValues K] → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `totalWeight` of a field with `AdmissibleAbsValues` is the sum of the multip
licities of
the archimedean places.
-/
def totalWeight : ℕ := archAbsVal (K := K) |>.card

variable {K}

/-!
### Heights of field elements

We use the subscript `₁` to denote multiplicative and logarithmic heights of field elements
(this is because we are in the one-dimensional case of (affine) heights).
-/

/-- The multiplicative height of an element of `K`. -/
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of an element of `K`.
-/
def mulHeight₁ (x : K) : ℝ :=
  (archAbsVal.map fun v ↦ max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulHeight₁_eq (x : K) :
    mulHeight₁ x =
      (archAbsVal.map fun v ↦ max (v x) 1).prod * ∏ᶠ v : nonarchAbsVal, max (v.val x) 1 :=
  rfl

@[simp]
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulHeight₁_zero : mulHeight₁ (0 : K) = 1 := by
  simp [mulHeight₁_eq]

@[simp]
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulHeight₁_one : mulHeight₁ (1 : K) = 1 := by
  simp [mulHeight₁_eq]

/-- The multiplicative height of a field element is always at least `1`. -/
/-
**Height.one_le_mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：one_le_mulHeight (x : ι -> K) : 1 <= mulHeight x
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Height.mulHeight_smul_eq_mulHeight`：mulHeight_smul_eq_mulHeight (x : ι -
> K) {c : K} (hc : c != 0) : mulHeight (c • x) = mulHeight x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用引理 `one_le_mul_of_one_le_of_one_le`：one_le_mul_of_one_le_of_one_le [ZeroLEOn
eClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b) : (1 : M₀) <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Multiset.one_le_prod_map`：one_le_prod_map {s : Multiset α} {f : α -> R} 
(h : forall a in s, 1 <= f a) : 1 <= (s.map f).prod
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AbsoluteValue.map_mul`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (
x y : R), a…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AbsoluteValue.ne_zero_iff`：∀ {R : Type u_5} {S : Type u_6} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R 
S) {x : R}, abv…
· 使用引理 `one_le_finprod`：one_le_finprod {M : Type*} [CommMonoidWithZero M] [Preor
der M] [ZeroLEOneClass M] [PosMulMono M] {f : α -> M} (hf : forall i, 1 <= f i) 
: 1 …

--- 原说明 ---
The multiplicative height of a field element is always at least `1`.
-/
lemma one_le_mulHeight₁ (x : K) : 1 ≤ mulHeight₁ x :=
  one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod_map fun _ _ ↦ le_max_right ..) <|
    one_le_finprod fun _ ↦ le_max_right ..

-- This is needed as a side condition in proofs about logarithmic heights
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulHeight₁_pos (x : K) : 0 < mulHeight₁ x :=
  zero_lt_one.trans_le <| one_le_mulHeight₁ x

-- This is needed as a side condition in proofs about logarithmic heights
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulHeight₁_ne_zero (x : K) : mulHeight₁ x ≠ 0 :=
  (mulHeight₁_pos x).ne'
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulHeight₁_nonneg (x : K) : 0 ≤ mulHeight₁ x :=
  (mulHeight₁_pos x).le

/-- The logarithmic height of an element of `K`. -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of an element of `K`.
-/
def logHeight₁ (x : K) : ℝ := log (mulHeight₁ x)
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma logHeight₁_eq_log_mulHeight₁ (x : K) : logHeight₁ x = log (mulHeight₁ x) := rfl

@[simp]
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma logHeight₁_zero : logHeight₁ (0 : K) = 0 := by
  simp [logHeight₁_eq_log_mulHeight₁]

@[simp]
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma logHeight₁_one : logHeight₁ (1 : K) = 0 := by
  simp [logHeight₁_eq_log_mulHeight₁]
/-
**Height.zero_le_logHeight** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma zero_le_logHeight₁ (x : K) : 0 ≤ logHeight₁ x :=
  Real.log_nonneg <| one_le_mulHeight₁ x

/-- The logarithmic height of a field element can be expressed as a sum over the positive parts
of the logarithms of its various absolute values. -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of a field element can be expressed as a sum over the pos
itive parts
of the logarithms of its various absolute values.
-/
lemma logHeight₁_eq (x : K) :
    logHeight₁ x =
      (archAbsVal.map fun v ↦ log⁺ (v x)).sum + ∑ᶠ v : nonarchAbsVal, log⁺ (v.val x) := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_eq]
  have H : mulHeight₁ x ≠ 0 := mulHeight₁_ne_zero x
  rw [mulHeight₁_eq] at H
  have : ∀ a ∈ archAbsVal.map (fun v ↦ max (v x) 1), a ≠ 0 := by
    intro a ha
    contrapose ha
    rw [ha]
    exact Multiset.prod_eq_zero_iff.not.mp <| left_ne_zero_of_mul H
  rw [log_mul (left_ne_zero_of_mul H) (right_ne_zero_of_mul H), log_multiset_prod this,
    Multiset.map_map, log_finprod (fun _ ↦ by positivity)]
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
  | 0, ~q(ℝ), ~q(@mulHeight₁ $K $KF $KA $a) =>
    assertInstancesCommute
    pure (.positive q(mulHeight₁_pos $a))
  | _, _, _ => throwError "not Height.mulHeight₁"

/-- Extension for the `positivity` tactic: `Height.logHeight₁` is always nonnegative. -/
@[positivity Height.logHeight₁ _]
meta def evalLogHeight₁ : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(@logHeight₁ $K $KF $KA $a) =>
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

/-- The multiplicative height of a tuple of elements of `K`.
For the zero tuple we take the junk value `1`. -/
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of a tuple of elements of `K`.
For the zero tuple we take the junk value `1`.
-/
def mulHeight (x : ι → K) : ℝ :=
  have : Decidable (x = 0) := Classical.propDecidable _
  if x = 0 then 1 else
    (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)
/-
**Height.mulHeight_eq** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight x = (archAbsVal.map fu
n v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulHeight_eq {x : ι → K} (hx : x ≠ 0) :
    mulHeight x =
      (archAbsVal.map fun v ↦ ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.val (x i) := by
  simp [mulHeight, hx]

@[to_fun (attr := simp)]
/-
**Height.mulHeight_zero** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_zero : mulHeight (0 : ι -> K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulHeight_zero : mulHeight (0 : ι → K) = 1 := by
  simp [mulHeight]

@[to_fun (attr := simp)]
/-
**Height.mulHeight_one** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_one : mulHeight (1 : ι -> K) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AbsoluteValue.map_one`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `finprod_one`：finprod_one : (∏ᶠ _ : α, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulHeight_one : mulHeight (1 : ι → K) = 1 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [show (1 : ι → K) = 0 from Subsingleton.elim ..]
    exact mulHeight_zero
  · have hx : (1 : ι → K) ≠ 0 := by simp
    simp [mulHeight_eq hx]

/-- The multiplicative height does not change under re-indexing. -/
/-
**Height.mulHeight_comp_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_comp_equiv (e : ι ≃ ι') (x : ι' -> K) : mulHeight (x ∘ e) = mulH
eight x
参数：e : ι ≃ ι'；x : ι' -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.iSup_congr`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort u_5} [inst 
: SupSet α] {f : ι → α} {g : ι' → α} (e : ι ≃ ι'),   (∀ (x : ι), g (e x) = f x) 
→ ⨆ x,…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
The multiplicative height does not change under re-indexing.
-/
lemma mulHeight_comp_equiv (e : ι ≃ ι') (x : ι' → K) :
    mulHeight (x ∘ e) = mulHeight x := by
  have H (v : AbsoluteValue K ℝ) : ⨆ i, v (x (e i)) = ⨆ i, v (x i) := e.iSup_congr (congrFun rfl)
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : x ∘ e ≠ 0 := by
      obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
      exact ne_iff.mpr ⟨e.symm i, by simp [hi]⟩
    simp [mulHeight_eq hx, mulHeight_eq hx', comp_apply, H]
/-
**Height.mulHeight_swap** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_swap (x y : K) : mulHeight ![x, y] = mulHeight ![y, x]
参数：x y : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.ofFn_inj`：ofFn_inj {n : Nat} {f g : Fin n -> α} : ofFn f = ofFn g ↔
 f = g
· 使用引理 `Height.mulHeight_comp_equiv`：mulHeight_comp_equiv (e : ι ≃ ι') (x : ι' -
> K) : mulHeight (x ∘ e) = mulHeight x
-/
lemma mulHeight_swap (x y : K) : mulHeight ![x, y] = mulHeight ![y, x] := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  rw [show ![x, y] = ![y, x] ∘ e from List.ofFn_inj.mp rfl]
  exact mulHeight_comp_equiv e ![y, x]

/-- The logarithmic height of a tuple of elements of `K`. -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of a tuple of elements of `K`.
-/
def logHeight (x : ι → K) : ℝ := log (mulHeight x)
/-
**Height.logHeight_eq_log_mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_eq_log_mulHeight (x : ι -> K) : logHeight x = log (mulHeight x)
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma logHeight_eq_log_mulHeight (x : ι → K) : logHeight x = log (mulHeight x) := rfl

@[to_fun (attr := simp)]
/-
**Height.logHeight_zero** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_zero : logHeight (0 : ι -> K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logHeight_zero : logHeight (0 : ι → K) = 0 := by
  simp [logHeight_eq_log_mulHeight]

@[to_fun (attr := simp)]
/-
**Height.logHeight_one** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_one : logHeight (1 : ι -> K) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_one`：mulHeight_one : mulHeight (1 : ι -> K) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logHeight_one : logHeight (1 : ι → K) = 0 := by
  simp [logHeight_eq_log_mulHeight]
/-
**Height.logHeight_comp_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_comp_equiv (e : ι ≃ ι') (x : ι' -> K) : logHeight (x ∘ ⇑e) = log
Height x
参数：e : ι ≃ ι'；x : ι' -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_comp_equiv`：mulHeight_comp_equiv (e : ι ≃ ι') (x : ι' -
> K) : mulHeight (x ∘ e) = mulHeight x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logHeight_comp_equiv (e : ι ≃ ι') (x : ι' → K) :
    logHeight (x ∘ ⇑e) = logHeight x := by
  simp only [logHeight_eq_log_mulHeight, mulHeight_comp_equiv]
/-
**Height.logHeight_swap** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_swap (x y : K) : logHeight ![x, y] = logHeight ![y, x]
参数：x y : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_swap`：mulHeight_swap (x y : K) : mulHeight ![x, y] = mu
lHeight ![y, x]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logHeight_swap (x y : K) : logHeight ![x, y] = logHeight ![y, x] := by
  simp only [logHeight_eq_log_mulHeight, mulHeight_swap]

variable {α : Type*}

/-- The multiplicative height of a finitely supported function. -/
/-
**Height._root_.Finsupp.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of a finitely supported function.
-/
def _root_.Finsupp.mulHeight (x : α →₀ K) : ℝ :=
  Height.mulHeight fun i : x.support ↦ x i

/-- The logarithmic height of a finitely supported function. -/
/-
**Height._root_.Finsupp.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of a finitely supported function.
-/
def _root_.Finsupp.logHeight (x : α →₀ K) : ℝ := log (mulHeight x)
/-
**Height._root_.Finsupp.logHeight_eq_log_mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `He
ight`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Finsupp.logHeight_eq_log_mulHeight (x : α →₀ K) :
    logHeight x = log (mulHeight x) := rfl

/-!
### First properties of heights
-/

/-
**Height.max_eq_iSup** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### First properties of heights
-/
private lemma max_eq_iSup {α : Type*} [ConditionallyCompleteLattice α] (a b : α) :
    max a b = iSup ![a, b] :=
  eq_of_forall_ge_iff <| by simp [ciSup_le_iff, Fin.forall_fin_two]

variable [Finite ι] [Finite ι']

@[fun_prop]
/-
**Height.hasFiniteMulSupport_iSup_nonarchAbsVal** 是 Mathlib 中的一个引理，位于命名空间 `Heigh
t`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasFiniteMulSupport_iSup_nonarchAbsVal {x : ι → K} (hx : x ≠ 0) :
    (fun v : nonarchAbsVal ↦ ⨆ i, v.val (x i)).HasFiniteMulSupport := by
  have : Nonempty {j // x j ≠ 0} := nonempty_subtype.mpr <| ne_iff.mp hx
  suffices (fun v : nonarchAbsVal ↦ ⨆ i : {j // x j ≠ 0}, v.val (x i)).HasFiniteMulSupport by
    convert! this with v
    obtain ⟨i, hi⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.mp hx
    have : Nonempty ι := .intro i
    refine le_antisymm (ciSup_le fun j ↦ ?_) (ciSup_le fun ⟨j, hj⟩ ↦ Finite.le_ciSup_of_le j le_rfl)
    rcases eq_or_ne (x j) 0 with h | h
    · rw [h, v.val.map_zero]
      exact Real.iSup_nonneg' ⟨⟨i, hi⟩, v.val.nonneg ..⟩
    · exact Finite.le_ciSup_of_le ⟨j, h⟩ le_rfl
  fun_prop (disch := grind)

@[fun_prop]
/-
**Height.hasFiniteMulSupport_max_nonarchAbsVal** 是 Mathlib 中的一个引理，位于命名空间 `Height
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma hasFiniteMulSupport_max_nonarchAbsVal (x : K) :
    (fun v : nonarchAbsVal ↦ v.val x ⊔ 1).HasFiniteMulSupport := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [HasFiniteMulSupport]
  fun_prop

/-- The multiplicative height of a tuple does not change under scaling. -/
/-
**Height.mulHeight_smul_eq_mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_smul_eq_mulHeight (x : ι -> K) {c : K} (hc : c != 0) : mulHeight
 (c • x) = mulHeight x
参数：x : ι -> K；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Real.mul_iSup_of_nonneg`：Real.mul_iSup_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (r * ⨆ i, f i) = ⨆ i, r * f i
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `Multiset.prod_map_mul`：prod_map_mul : (m.map fun i => f i * g i).prod = 
(m.map f).prod * (m.map g).prod
· 使用定理 `finprod_mul_distrib`：finprod_mul_distrib (hf : HasFiniteMulSupport f) (h
g : HasFiniteMulSupport g) : ∏ᶠ i, f i * g i = (∏ᶠ i, f i) * ∏ᶠ i, g i
· 使用定理 `Height.AdmissibleAbsValues.hasFiniteMulSupport`：∀ {K : Type u_1} {inst :
 Field K} [self : Height.AdmissibleAbsValues K] {x : K},   x ≠ 0 → Function.HasF
initeMulSupport fun v => ↑v x
· 使用定理 `_private.Mathlib.NumberTheory.Height.Basic.0.Height.hasFiniteMulSupport_
iSup_nonarchAbsVal`：∀ {K : Type u_1} [inst : Field K] [inst_1 : Height.Admissibl
eAbsValues K] {ι : Type u_2} [Finite ι] {x : ι → K},   x ≠ 0 → Function.HasFinit
…
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Height.AdmissibleAbsValues.product_formula`：∀ {K : Type u_1} {inst : Fie
ld K} [self : Height.AdmissibleAbsValues K] {x : K},   x ≠ 0 →     (Multiset.map
 (fun x_2 => x_2 x) Height.Admis…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The multiplicative height of a tuple does not change under scaling.
-/
lemma mulHeight_smul_eq_mulHeight (x : ι → K) {c : K} (hc : c ≠ 0) :
    mulHeight (c • x) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [smul_zero]
  have : Nonempty ι := (ne_iff.mp hx).nonempty
  have hcx : c • x ≠ 0 := by simp [hc, hx]
  simp only [mulHeight_eq hx, mulHeight_eq hcx, Pi.smul_apply, smul_eq_mul, map_mul,
    ← mul_iSup_of_nonneg <| AbsoluteValue.nonneg .., Multiset.prod_map_mul]
  rw [finprod_mul_distrib (by fun_prop) (by fun_prop),
    mul_mul_mul_comm, product_formula hc, one_mul]
/-
**Height.one_le_mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：one_le_mulHeight (x : ι -> K) : 1 <= mulHeight x
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Height.mulHeight_smul_eq_mulHeight`：mulHeight_smul_eq_mulHeight (x : ι -
> K) {c : K} (hc : c != 0) : mulHeight (c • x) = mulHeight x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用引理 `one_le_mul_of_one_le_of_one_le`：one_le_mul_of_one_le_of_one_le [ZeroLEOn
eClass M₀] [PosMulMono M₀] (ha : 1 <= a) (hb : 1 <= b) : (1 : M₀) <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Multiset.one_le_prod_map`：one_le_prod_map {s : Multiset α} {f : α -> R} 
(h : forall a in s, 1 <= f a) : 1 <= (s.map f).prod
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AbsoluteValue.map_mul`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (
x y : R), a…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AbsoluteValue.ne_zero_iff`：∀ {R : Type u_5} {S : Type u_6} [inst : Semir
ing R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R 
S) {x : R}, abv…
· 使用引理 `one_le_finprod`：one_le_finprod {M : Type*} [CommMonoidWithZero M] [Preor
der M] [ZeroLEOneClass M] [PosMulMono M] {f : α -> M} (hf : forall i, 1 <= f i) 
: 1 …
-/
lemma one_le_mulHeight (x : ι → K) : 1 ≤ mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := ne_iff.mp hx
  have hx' : (x i)⁻¹ • x ≠ 0 := by simp [hi, hx]
  rw [← mulHeight_smul_eq_mulHeight _ <| inv_ne_zero hi, mulHeight_eq hx']
  refine one_le_mul_of_one_le_of_one_le (Multiset.one_le_prod_map fun v _ ↦ ?_) ?_
  · refine Finite.le_ciSup_of_le i <| le_of_eq ?_
    simpa using (inv_mul_cancel₀ <| v.ne_zero_iff.mpr hi).symm
  · refine one_le_finprod fun v ↦ Finite.le_ciSup_of_le i ?_
    simp [inv_mul_cancel₀ <| v.val.ne_zero_iff.mpr hi]
/-
**Height.mulHeight_pos** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_pos (x : ι -> K) : 0 < mulHeight x
参数：x : ι -> K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Height.one_le_mulHeight`：one_le_mulHeight (x : ι -> K) : 1 <= mulHeight 
x
-/
lemma mulHeight_pos (x : ι → K) : 0 < mulHeight x :=
  zero_lt_one.trans_le <| one_le_mulHeight x
/-
**Height.mulHeight_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_ne_zero (x : ι -> K) : mulHeight x != 0
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Height.mulHeight_pos`：mulHeight_pos (x : ι -> K) : 0 < mulHeight x
-/
lemma mulHeight_ne_zero (x : ι → K) : mulHeight x ≠ 0 :=
  (mulHeight_pos x).ne'
/-
**Height.logHeight_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_nonneg (x : ι -> K) : 0 <= logHeight x
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
· 使用引理 `Height.one_le_mulHeight`：one_le_mulHeight (x : ι -> K) : 1 <= mulHeight 
x
-/
lemma logHeight_nonneg (x : ι → K) : 0 ≤ logHeight x :=
  log_nonneg <| one_le_mulHeight x

open Function in
/-
**Height.mulHeight_comp_le** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_comp_le (f : ι -> ι') (x : ι' -> K) : mulHeight (x ∘ f) <= mulHe
ight x
参数：f : ι -> ι'；x : ι' -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用引理 `Height.one_le_mulHeight`：one_le_mulHeight (x : ι -> K) : 1 <= mulHeight 
x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Multiset.prod_map_le_prod_map₀`：prod_map_le_prod_map₀ {ι : Type*} {s : M
ultiset ι} (f : ι -> R) (g : ι -> R) (h0 : forall i in s, 0 <= f i) (h : forall 
i in s, f i <= g i) …
· 使用引理 `Real.iSup_nonneg_of_nonnegHomClass`：iSup_nonneg_of_nonnegHomClass {ι F α
 : Type*} [FunLike F α Real] [NonnegHomClass F α Real] (f : F) (g : ι -> α) : 0 
<= ⨆ i, f (g i)
· 使用引理 `finprod_le_finprod`：finprod_le_finprod {M : Type*} [CommMonoidWithZero M
] [PartialOrder M] [ZeroLEOneClass M] [PosMulMono M] {f g : α -> M} (hf : HasFin
iteMulSu…
· 使用定理 `_private.Mathlib.NumberTheory.Height.Basic.0.Height.hasFiniteMulSupport_
iSup_nonarchAbsVal`：∀ {K : Type u_1} [inst : Field K] [inst_1 : Height.Admissibl
eAbsValues K] {ι : Type u_2} [Finite ι] {x : ι → K},   x ≠ 0 → Function.HasFinit
…
· 使用定理 `finprod_nonneg`：finprod_nonneg {R : Type*} [CommMonoidWithZero R] [Preor
der R] [ZeroLEOneClass R] [PosMulMono R] {f : α -> R} (hf : forall x, 0 <= f x) 
: 0 …
· 使用引理 `Multiset.prod_map_nonneg`：prod_map_nonneg {s : Multiset α} {f : α -> R} 
(h : forall a in s, 0 <= f a) : 0 <= (s.map f).prod
-/
lemma mulHeight_comp_le (f : ι → ι') (x : ι' → K) :
    mulHeight (x ∘ f) ≤ mulHeight x := by
  rcases eq_or_ne (x ∘ f) 0 with h₀ | h₀
  · simpa [h₀] using one_le_mulHeight _
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have : Nonempty ι := .intro (ne_iff.mp h₀).choose
  rw [mulHeight_eq h₀, mulHeight_eq hx]
  have H (v : AbsoluteValue K ℝ) : ⨆ i, v ((x ∘ f) i) ≤ ⨆ i, v (x i) :=
    ciSup_le fun i ↦ Finite.le_ciSup_of_le (f i) le_rfl
  gcongr
  · exact finprod_nonneg fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _
  · exact Multiset.prod_map_nonneg fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _
  · exact Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ Real.iSup_nonneg_of_nonnegHomClass v _)
      fun v _ ↦ H v
  · exact finprod_le_finprod (hasFiniteMulSupport_iSup_nonarchAbsVal h₀)
      (fun v ↦ Real.iSup_nonneg_of_nonnegHomClass v.val _)
      (hasFiniteMulSupport_iSup_nonarchAbsVal hx) fun v ↦ H v.val

open Real in
/-
**Height.logHeight_comp_le** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_comp_le (f : ι -> ι') (x : ι' -> K) : logHeight (x ∘ f) <= logHe
ight x
参数：f : ι -> ι'；x : ι' -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.log_le_log`：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
· 使用引理 `Height.mulHeight_pos`：mulHeight_pos (x : ι -> K) : 0 < mulHeight x
· 使用引理 `Height.mulHeight_comp_le`：mulHeight_comp_le (f : ι -> ι') (x : ι' -> K) 
: mulHeight (x ∘ f) <= mulHeight x
-/
lemma logHeight_comp_le (f : ι → ι') (x : ι' → K) :
    logHeight (x ∘ f) ≤ logHeight x := by
  simpa [logHeight_eq_log_mulHeight] using log_le_log (mulHeight_pos _) <| mulHeight_comp_le ..

open Function in
/-
**Height.mulHeight_sumElim_zero_eq** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_sumElim_zero_eq (x : ι -> K) : mulHeight (Sum.elim x (0 : ι' -> 
K)) = mulHeight x
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sum.elim_zero_zero`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : Zero γ], Sum.elim 0 0 = 0
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `Sum.nonemptyLeft`：∀ {α : Type u} {β : Type v} [h : Nonempty α], Nonempty
 (α ⊕ β)
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用引理 `Real.iSup_nonneg_of_nonnegHomClass`：iSup_nonneg_of_nonnegHomClass {ι F α
 : Type*} [FunLike F α Real] [NonnegHomClass F α Real] (f : F) (g : ι -> α) : 0 
<= ⨆ i, f (g i)
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma mulHeight_sumElim_zero_eq (x : ι → K) :
    mulHeight (Sum.elim x (0 : ι' → K)) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨i, hi⟩ := ne_iff.mp hx
  have : Nonempty ι := .intro i
  have hx' : Sum.elim x (0 : ι' → K) ≠ 0 := ne_iff.mpr ⟨.inl i, by simpa using hi⟩
  rw [mulHeight_eq hx, mulHeight_eq hx']
  have H (v : AbsoluteValue K ℝ) : ⨆ j, v (Sum.elim x (0 : ι' → K) j) = ⨆ i, v (x i) := by
    refine le_antisymm ?_ <| ciSup_le fun i ↦ Finite.le_ciSup_of_le (.inl i) le_rfl
    refine ciSup_le fun j ↦ ?_
    cases j with
    | inl i => exact Finite.le_ciSup_of_le i le_rfl
    | inr _ => simpa using Real.iSup_nonneg_of_nonnegHomClass v _
  congr <;> ext1 v
  · exact H v
  · exact H v.val
/-
**Height.logHeight_sumElim_zero_eq** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_sumElim_zero_eq (x : ι -> K) : logHeight (Sum.elim x (0 : ι' -> 
K)) = logHeight x
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_sumElim_zero_eq`：mulHeight_sumElim_zero_eq (x : ι -> K)
 : mulHeight (Sum.elim x (0 : ι' -> K)) = mulHeight x
-/
lemma logHeight_sumElim_zero_eq (x : ι → K) :
    logHeight (Sum.elim x (0 : ι' → K)) = logHeight x :=
  congrArg log <| mulHeight_sumElim_zero_eq ..
/-
**Height.mulHeight_eq_mulHeight_restrict_support** 是 Mathlib 中的一个引理，位于命名空间 `Heig
ht`。
形式化陈述：mulHeight_eq_mulHeight_restrict_support (x : ι -> K) : mulHeight x = mulHe
ight fun i : x.support => x i.val
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
· 使用定理 `Set.mem_compl_iff`：mem_compl_iff (s : Set α) (x : α) : x in sᶜ ↔ x ∉ s
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_comp_equiv`：mulHeight_comp_equiv (e : ι ≃ ι') (x : ι' -
> K) : mulHeight (x ∘ e) = mulHeight x
· 使用引理 `Height.mulHeight_sumElim_zero_eq`：mulHeight_sumElim_zero_eq (x : ι -> K)
 : mulHeight (Sum.elim x (0 : ι' -> K)) = mulHeight x
-/
lemma mulHeight_eq_mulHeight_restrict_support (x : ι → K) :
    mulHeight x = mulHeight fun i : x.support ↦ x i.val := by
  classical
  let e := Equiv.Set.sumCompl x.support
  have hx : x ∘ e = Sum.elim (fun i : x.support ↦ x i.val) 0 := by
    ext1 i
    simp only [comp_apply]
    cases i with
    | inl val => simp [e]
    | inr val => exact notMem_support.mp <| (Set.mem_compl_iff _ _).mp val.prop
  rw [← mulHeight_comp_equiv e, hx]
  exact mulHeight_sumElim_zero_eq ..
/-
**Height.logHeight_eq_logHeight_restrict_support** 是 Mathlib 中的一个引理，位于命名空间 `Heig
ht`。
形式化陈述：logHeight_eq_logHeight_restrict_support (x : ι -> K) : logHeight x = logHe
ight fun i : x.support => x i.val
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_eq_mulHeight_restrict_support`：mulHeight_eq_mulHeight_r
estrict_support (x : ι -> K) : mulHeight x = mulHeight fun i : x.support => x i.
val
-/
lemma logHeight_eq_logHeight_restrict_support (x : ι → K) :
    logHeight x = logHeight fun i : x.support ↦ x i.val :=
  congrArg log <| mulHeight_eq_mulHeight_restrict_support x

@[simp]
/-
**Height.mulHeight_eq_one_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_eq_one_of_subsingleton {ι : Type*} [Subsingleton ι] (x : ι -> K)
 : mulHeight x = 1
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用引理 `Height.mulHeight_smul_eq_mulHeight`：mulHeight_smul_eq_mulHeight (x : ι -
> K) {c : K} (hc : c != 0) : mulHeight (c • x) = mulHeight x
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `Height.mulHeight_one`：mulHeight_one : mulHeight (1 : ι -> K) = 1
-/
lemma mulHeight_eq_one_of_subsingleton {ι : Type*} [Subsingleton ι] (x : ι → K) :
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
/-
**Height.logHeight_eq_zero_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_eq_zero_of_subsingleton {ι : Type*} [Subsingleton ι] (x : ι -> K
) : logHeight x = 0
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_eq_one_of_subsingleton`：mulHeight_eq_one_of_subsingleto
n {ι : Type*} [Subsingleton ι] (x : ι -> K) : mulHeight x = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logHeight_eq_zero_of_subsingleton {ι : Type*} [Subsingleton ι] (x : ι → K) :
    logHeight x = 0 := by
  simp [logHeight_eq_log_mulHeight]

section tuple

/-
This section contains `simp` lemmas that remove a zero from one of the first three positions
in a tuple, when `mulHeight` or `logHeight` is applied to it.

TODO: Write a `simproc` that removes *all* (syntactic) zeros from a tuple in this situation.
-/

open Matrix

variable {n : ℕ} (a b : K) (x : Fin n → K)

@[simp]
/-
**Height.mulHeight_cons_zero** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_cons_zero : mulHeight (vecCons 0 x) = mulHeight x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Nat.one_add`：∀ (n : ℕ), 1 + n = n.succ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `finCongr_apply`：∀ {n m : ℕ} (eq : n = m) (i : Fin n), (finCongr eq) i = 
Fin.cast eq i
· 使用定理 `Fin.cast_natAdd`：∀ (n : ℕ) {m : ℕ} (i : Fin m), Fin.cast ⋯ (Fin.natAdd n
 i) = i.addNat n
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `instNeZeroNatHAdd`：∀ {n m : ℕ} [h : NeZero n], NeZero (n + m)
· 使用定理 `Fin.castAdd_mk`：∀ {n : ℕ} (m i : ℕ) (h : i < n), Fin.castAdd m ⟨i, h⟩ = 
⟨i, ⋯⟩
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Height.mulHeight_comp_equiv`：mulHeight_comp_equiv (e : ι ≃ ι') (x : ι' -
> K) : mulHeight (x ∘ e) = mulHeight x
· 使用引理 `Height.mulHeight_sumElim_zero_eq`：mulHeight_sumElim_zero_eq (x : ι -> K)
 : mulHeight (Sum.elim x (0 : ι' -> K)) = mulHeight x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma mulHeight_cons_zero : mulHeight (vecCons 0 x) = mulHeight x := by
  let e := (Equiv.sumComm ..).trans <| finSumFinEquiv.trans <| finCongr n.one_add
  have he : Matrix.vecCons 0 x ∘ ⇑e = Sum.elim x 0 := by
    ext j : 1
    match j with
    | .inl _ => simp [e]
    | .inr ⟨i, h⟩ =>
      simp [show i = 0 by lia, e, show Fin.castAdd n 0 = 0 from Fin.castAdd_mk _ _ zero_lt_one]
  rw [← mulHeight_comp_equiv e, he, mulHeight_sumElim_zero_eq]

@[simp]
/-
**Height.logHeight_cons_zero** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_cons_zero : logHeight (Matrix.vecCons 0 x) = logHeight x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_cons_zero`：mulHeight_cons_zero : mulHeight (vecCons 0 x
) = mulHeight x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logHeight_cons_zero : logHeight (Matrix.vecCons 0 x) = logHeight x := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
/-
**Height.mulHeight_cons_cons_zero** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_cons_cons_zero : mulHeight (vecCons a (vecCons 0 x)) = mulHeight
 (vecCons a x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Height.mulHeight_comp_equiv`：mulHeight_comp_equiv (e : ι ≃ ι') (x : ι' -
> K) : mulHeight (x ∘ e) = mulHeight x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matrix.cons_cons_comp_swap_zero_one`：cons_cons_comp_swap_zero_one (a b :
 α) (x : Fin n -> α) : vecCons a (vecCons b x) ∘ (Equiv.swap 0 1) = vecCons b (v
ecCons a x)
· 使用引理 `Height.mulHeight_cons_zero`：mulHeight_cons_zero : mulHeight (vecCons 0 x
) = mulHeight x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulHeight_cons_cons_zero : mulHeight (vecCons a (vecCons 0 x)) = mulHeight (vecCons a x) := by
  rw [← mulHeight_comp_equiv (Equiv.swap 0 1)]
  simp

@[simp]
/-
**Height.logHeight_cons_cons_zero** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_cons_cons_zero : logHeight (vecCons a (vecCons 0 x)) = logHeight
 (vecCons a x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_cons_cons_zero`：mulHeight_cons_cons_zero : mulHeight (v
ecCons a (vecCons 0 x)) = mulHeight (vecCons a x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma logHeight_cons_cons_zero : logHeight (vecCons a (vecCons 0 x)) = logHeight (vecCons a x) := by
  simp [logHeight_eq_log_mulHeight]

@[simp]
/-
**Height.mulHeight_cons_cons_cons_zero** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_cons_cons_cons_zero : mulHeight (vecCons a (vecCons b (vecCons 0
 x))) = mulHeight (vecCons a (vecCons b x))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Height.mulHeight_comp_equiv`：mulHeight_comp_equiv (e : ι ≃ ι') (x : ι' -
> K) : mulHeight (x ∘ e) = mulHeight x
· 使用引理 `Matrix.cons_swap`：cons_swap (a : α) (x : Fin n -> α) (i j : Fin n) : vec
Cons a (x ∘ (Equiv.swap i j)) = vecCons a x ∘ (Equiv.swap i.succ j.succ)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Matrix.cons_cons_comp_swap_zero_one`：cons_cons_comp_swap_zero_one (a b :
 α) (x : Fin n -> α) : vecCons a (vecCons b x) ∘ (Equiv.swap 0 1) = vecCons b (v
ecCons a x)
· 使用引理 `Height.mulHeight_cons_cons_zero`：mulHeight_cons_cons_zero : mulHeight (v
ecCons a (vecCons 0 x)) = mulHeight (vecCons a x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulHeight_cons_cons_cons_zero :
    mulHeight (vecCons a (vecCons b (vecCons 0 x))) = mulHeight (vecCons a (vecCons b x)) := by
  rw [← mulHeight_comp_equiv (Equiv.swap (Fin.succ 0) (Fin.succ 1)), ← cons_swap]
  simp

@[simp]
/-
**Height.logHeight_cons_cons_cons_zero** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_cons_cons_cons_zero : logHeight (vecCons a (vecCons b (vecCons 0
 x))) = logHeight (vecCons a (vecCons b x))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_cons_cons_cons_zero`：mulHeight_cons_cons_cons_zero : mu
lHeight (vecCons a (vecCons b (vecCons 0 x))) = mulHeight (vecCons a (vecCons b 
x))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
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
  | 0, ~q(ℝ), ~q(@mulHeight $K $KF $KA $ι $a) =>
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
  | 0, ~q(ℝ), ~q(@logHeight $K $KF $KA $ι $a) =>
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

/-- The logarithmic height of a tuple does not change under scaling. -/
/-
**Height.logHeight_smul_eq_logHeight** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_smul_eq_logHeight (x : ι -> K) {c : K} (hc : c != 0) : logHeight
 (c • x) = logHeight x
参数：x : ι -> K；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_smul_eq_mulHeight`：mulHeight_smul_eq_mulHeight (x : ι -
> K) {c : K} (hc : c != 0) : mulHeight (c • x) = mulHeight x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The logarithmic height of a tuple does not change under scaling.
-/
lemma logHeight_smul_eq_logHeight (x : ι → K) {c : K} (hc : c ≠ 0) :
    logHeight (c • x) = logHeight x := by
  simp only [logHeight_eq_log_mulHeight, mulHeight_smul_eq_mulHeight x hc]
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulHeight₁_eq_mulHeight (x : K) : mulHeight₁ x = mulHeight ![x, 1] := by
  have H (v : AbsoluteValue K ℝ) (x : K) : v x ⊔ 1 = ⨆ i, v (![x, 1] i) := by
    have (i : Fin 2) : v (![x, 1] i) = ![v x, 1] i := by fin_cases i <;> simp
    simpa [this] using max_eq_iSup (v x) 1
  have hx : ![x, 1] ≠ 0 := by simp
  simp only [mulHeight₁_eq, mulHeight_eq hx, H]
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma logHeight₁_eq_logHeight (x : K) : logHeight₁ x = logHeight ![x, 1] := by
  simp only [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_eq_mulHeight x]
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulHeight₁_div_eq_mulHeight (x y : K) :
    mulHeight₁ (x / y) = mulHeight ![x, y] := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · rw [mulHeight₁_eq_mulHeight, ← mulHeight_smul_eq_mulHeight _ hy]
    simp [mul_div_cancel₀ x hy]
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma logHeight₁_div_eq_logHeight (x y : K) :
    logHeight₁ (x / y) = logHeight ![x, y] := by
  rw [logHeight₁_eq_log_mulHeight₁, logHeight_eq_log_mulHeight, mulHeight₁_div_eq_mulHeight x y]

/-- The multiplicative height of the coordinate-wise `n`th power of a tuple
is the `n`th power of its multiplicative height. -/
/-
**Height.mulHeight_pow** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_pow (x : ι -> K) (n : Nat) : mulHeight (x ^ n) = mulHeight x ^ n
参数：x : ι -> K；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `Height.mulHeight_one`：mulHeight_one : mulHeight (1 : ι -> K) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Real.coe_toNNReal`：∀ (r : ℝ), 0 ≤ r → ↑r.toNNReal = r
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `Monotone.map_ciSup_of_continuousAt`：Monotone.map_ciSup_of_continuousAt {
ι : Sort*} [Nonempty ι] {f : α -> β} {g : ι -> α} (Cf : ContinuousAt f (iSup g))
 (Mf : Monotone f) (bdd …
· 使用定理 `NNReal.instOrderTopology`：OrderTopology NNReal
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
The multiplicative height of the coordinate-wise `n`th power of a tuple
is the `n`th power of its multiplicative height.
-/
lemma mulHeight_pow (x : ι → K) (n : ℕ) :
    mulHeight (x ^ n) = mulHeight x ^ n := by
  rcases eq_or_ne x 0 with rfl | hx
  · cases n <;> simp
  have : Nonempty ι := (ne_iff.mp hx).nonempty
  have H (v : AbsoluteValue K ℝ) : ⨆ i : ι, v ((x ^ n) i) = (⨆ i, v (x i)) ^ n := by
    simp only [Pi.pow_apply, map_pow]
    simp +singlePass only [← coe_toNNReal _ (v.nonneg _)]
    norm_cast
    exact (pow_left_mono n).map_ciSup_of_continuousAt (continuous_pow n).continuousAt
      (Finite.bddAbove_range _) |>.symm
  have hxn : x ^ n ≠ 0 := by simp [hx]
  simp only [mulHeight_eq hx, mulHeight_eq hxn, H, mul_pow,
    finprod_pow <| hasFiniteMulSupport_iSup_nonarchAbsVal hx, ← Multiset.prod_map_pow]

/-- The logarithmic height of the coordinate-wise `n`th power of a tuple
is `n` times its logarithmic height. -/
/-
**Height.logHeight_pow** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_pow (x : ι -> K) (n : Nat) : logHeight (x ^ n) = n * logHeight x
参数：x : ι -> K；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_pow`：mulHeight_pow (x : ι -> K) (n : Nat) : mulHeight (
x ^ n) = mulHeight x ^ n
· 使用定理 `Real.log_pow`：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The logarithmic height of the coordinate-wise `n`th power of a tuple
is `n` times its logarithmic height.
-/
lemma logHeight_pow (x : ι → K) (n : ℕ) : logHeight (x ^ n) = n * logHeight x := by
  simp [logHeight_eq_log_mulHeight, mulHeight_pow x n]

/-- The multiplicative height of the inverse of a field element `x`
is the same as the multiplicative height of `x`. -/
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of the inverse of a field element `x`
is the same as the multiplicative height of `x`.
-/
lemma mulHeight₁_inv (x : K) : mulHeight₁ (x⁻¹) = mulHeight₁ x := by
  simp_rw [mulHeight₁_eq_mulHeight]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [inv_zero]
  · have H : x • ![x⁻¹, 1] = ![1, x] := by ext1 i; fin_cases i <;> simp [hx]
    rw [← mulHeight_smul_eq_mulHeight _ hx, H, mulHeight_swap]

/-- The logarithmic height of the inverse of a field element `x`
is the same as the logarithmic height of `x`. -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of the inverse of a field element `x`
is the same as the logarithmic height of `x`.
-/
lemma logHeight₁_inv (x : K) : logHeight₁ (x⁻¹) = logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_inv]

/-- The multiplicative height of the `n`th power of a field element `x` (with `n : ℕ`)
is the `n`th power of the multiplicative height of `x`. -/
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of the `n`th power of a field element `x` (with `n : ℕ
`)
is the `n`th power of the multiplicative height of `x`.
-/
lemma mulHeight₁_pow (x : K) (n : ℕ) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n := by
  simp only [mulHeight₁_eq_mulHeight, ← mulHeight_pow _ n]
  congr 1
  ext1 i
  fin_cases i <;> simp

/-- The logarithmic height of the `n`th power of a field element `x` (with `n : ℕ`)
is `n` times the logarithmic height of `x`. -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of the `n`th power of a field element `x` (with `n : ℕ`)
is `n` times the logarithmic height of `x`.
-/
lemma logHeight₁_pow (x : K) (n : ℕ) : logHeight₁ (x ^ n) = n * logHeight₁ x := by
  simp only [logHeight₁_eq_log_mulHeight₁, mulHeight₁_pow, log_pow]

/-- The multiplicative height of the `n`th power of a field element `x` (with `n : ℤ`)
is the `|n|`th power of the multiplicative height of `x`. -/
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of the `n`th power of a field element `x` (with `n : ℤ
`)
is the `|n|`th power of the multiplicative height of `x`.
-/
lemma mulHeight₁_zpow (x : K) (n : ℤ) : mulHeight₁ (x ^ n) = mulHeight₁ x ^ n.natAbs := by
  rcases le_or_gt 0 n with h | h
  · lift n to ℕ using h
    rw [zpow_natCast, mulHeight₁_pow, Int.natAbs_natCast]
  · nth_rewrite 1 [show n = -n.natAbs by grind]
    rw [zpow_neg, mulHeight₁_inv, zpow_natCast, mulHeight₁_pow]

/-- The logarithmic height of the `n`th power of a field element `x` (with `n : ℤ`)
is `|n|` times the logarithmic height of `x`. -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of the `n`th power of a field element `x` (with `n : ℤ`)
is `|n|` times the logarithmic height of `x`.
-/
lemma logHeight₁_zpow (x : K) (n : ℤ) : logHeight₁ (x ^ n) = n.natAbs * logHeight₁ x := by
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

variable {α : Type u} [Fintype α] {ι : α → Type v} [∀ a, Finite (ι a)]

open Finset in
/-- Consider a finite family `x : (a : α) → ι a → K` of tuples. Then the multiplicative height
of the "multiplication table" `fun (I : (a : α) → ι a ↦ ∏ a, x a (I a))` is the product
of the multiplicative heights of all the `x a`. -/
/-
**Height.mulHeight_fun_prod_eq** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_fun_prod_eq {x : (a : α) -> ι a -> K} (hx : forall a, x a != 0) 
: mulHeight (fun I : (a : α) -> ι a => ∏ a, x a (I a)) = ∏ a, mulHeight (x a)
参数：a : α；hx : forall a, x a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用引理 `Real.iSup_prod_eq_prod_iSup_of_nonnegHomClass`：iSup_prod_eq_prod_iSup_of
_nonnegHomClass {F : Type*} [FunLike F R Real] [NonnegHomClass F R Real] (v : F)
 {x : (a : α) -> ι a -> R} : ⨆ (i :…
· 使用引理 `Multiset.prod_map_prod`：prod_map_prod {α : Type*} [CommMonoid M] {m : Mu
ltiset ι} {s : Finset α} {f : ι -> α -> M} : (m.map fun i => ∏ a in s, f i a).pr
od = ∏ a in …
· 使用定理 `finprod_prod_comm`：finprod_prod_comm (s : Finset β) (f : α -> β -> M) (h
 : forall b in s, HasFiniteMulSupport fun a => f a b) : (∏ᶠ a : α, ∏ b in s, f a
 b) = ∏…
· 使用定理 `_private.Mathlib.NumberTheory.Height.Basic.0.Height.hasFiniteMulSupport_
iSup_nonarchAbsVal`：∀ {K : Type u_1} [inst : Field K] [inst_1 : Height.Admissibl
eAbsValues K] {ι : Type u_2} [Finite ι] {x : ι → K},   x ≠ 0 → Function.HasFinit
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g

--- 原说明 ---
Consider a finite family `x : (a : α) → ι a → K` of tuples. Then the multiplicat
ive height
of the "multiplication table" `fun (I : (a : α) → ι a ↦ ∏ a, x a (I a))` is the 
product
of the multiplicative heights of all the `x a`.
-/
lemma mulHeight_fun_prod_eq {x : (a : α) → ι a → K} (hx : ∀ a, x a ≠ 0) :
    mulHeight (fun I : (a : α) → ι a ↦ ∏ a, x a (I a)) = ∏ a, mulHeight (x a) := by
  rw [mulHeight_eq ?h₁]
  case h₁ =>
    simp_rw [ne_iff, Pi.zero_def] at hx ⊢
    choose f hf using hx
    exact ⟨f, prod_ne_zero_iff.mpr fun a _ ↦ hf a⟩
  simp_rw [_root_.map_prod, Real.iSup_prod_eq_prod_iSup_of_nonnegHomClass]
  rw [Multiset.prod_map_prod,
    finprod_prod_comm _ _ fun b _ ↦ hasFiniteMulSupport_iSup_nonarchAbsVal (hx b),
    ← prod_mul_distrib]
  exact prod_congr rfl fun a _ ↦ by rw [mulHeight_eq (hx a)]

open Real in
/-- Consider a finite family `x : (a : α) → ι a → K` of tuples. Then the logarithmic height
of the "multiplication table" `fun (I : (a : α) → ι a ↦ ∏ a, x a (I a))` is the sum
of the logarithmic heights of all the `x a`. -/
/-
**Height.logHeight_fun_prod_eq** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_fun_prod_eq {x : (a : α) -> ι a -> K} (hx : forall a, x a != 0) 
: logHeight (fun I : (a : α) -> ι a => ∏ a, x a (I a)) = ∑ a, logHeight (x a)
参数：a : α；hx : forall a, x a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_prod`：log_prod {α : Type*} {s : Finset α} {f : α -> Real} (hf :
 forall x in s, f x != 0) : log (∏ i in s, f i) = ∑ i in s, log (f i)
· 使用引理 `Height.mulHeight_ne_zero`：mulHeight_ne_zero (x : ι -> K) : mulHeight x !
= 0
· 使用引理 `Height.mulHeight_fun_prod_eq`：mulHeight_fun_prod_eq {x : (a : α) -> ι a 
-> K} (hx : forall a, x a != 0) : mulHeight (fun I : (a : α) -> ι a => ∏ a, x a 
(I a)) = ∏ a, mulH…

--- 原说明 ---
Consider a finite family `x : (a : α) → ι a → K` of tuples. Then the logarithmic
 height
of the "multiplication table" `fun (I : (a : α) → ι a ↦ ∏ a, x a (I a))` is the 
sum
of the logarithmic heights of all the `x a`.
-/
lemma logHeight_fun_prod_eq {x : (a : α) → ι a → K} (hx : ∀ a, x a ≠ 0) :
    logHeight (fun I : (a : α) → ι a ↦ ∏ a, x a (I a)) = ∑ a, logHeight (x a) := by
  simp only [logHeight_eq_log_mulHeight]
  rw [← log_prod fun a _ ↦ mulHeight_ne_zero _]
  exact congrArg log <| mulHeight_fun_prod_eq hx

end many

section two

/-
Note: One could try to deduce the binary case from the general case above,
but this leads into dependent type shenanigans (because `ι` and `ι'` can live in different
universes) that would likely obfuscate the proofs more than simplify them.
-/

variable {ι ι' : Type*} [Finite ι] [Finite ι']

/-- The multiplicative height of the "multiplication table" `fun (i, j) ↦ x i * y j`
is the product of the multiplicative heights of `x` and `y`. -/
/-
**Height.mulHeight_fun_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_fun_mul_eq {x : ι -> K} (hx : x != 0) {y : ι' -> K} (hy : y != 0
) : mulHeight (fun a : ι × ι' => x a.1 * y a.2) = mulHeight x * mulHeight y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_map_mul`：prod_map_mul : (m.map fun i => f i * g i).prod = 
(m.map f).prod * (m.map g).prod
· 使用定理 `finprod_mul_distrib`：finprod_mul_distrib (hf : HasFiniteMulSupport f) (h
g : HasFiniteMulSupport g) : ∏ᶠ i, f i * g i = (∏ᶠ i, f i) * ∏ᶠ i, g i
· 使用定理 `_private.Mathlib.NumberTheory.Height.Basic.0.Height.hasFiniteMulSupport_
iSup_nonarchAbsVal`：∀ {K : Type u_1} [inst : Field K] [inst_1 : Height.Admissibl
eAbsValues K] {ι : Type u_2} [Finite ι] {x : ι → K},   x ≠ 0 → Function.HasFinit
…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg`：iSup_fun_mul_eq_iSup_mul_i
Sup_of_nonneg {F : Type*} [FunLike F R Real] [NonnegHomClass F R Real] [MulHomCl
ass F R Real] (v : F) (x : ι -> R)…

--- 原说明 ---
The multiplicative height of the "multiplication table" `fun (i, j) ↦ x i * y j`
is the product of the multiplicative heights of `x` and `y`.
-/
lemma mulHeight_fun_mul_eq {x : ι → K} (hx : x ≠ 0) {y : ι' → K} (hy : y ≠ 0) :
    mulHeight (fun a : ι × ι' ↦ x a.1 * y a.2) = mulHeight x * mulHeight y := by
  have hxy : (fun a : ι × ι' ↦ x a.1 * y a.2) ≠ 0 := by
    obtain ⟨i, hi⟩ := ne_iff.mp hx
    obtain ⟨j, hj⟩ := ne_iff.mp hy
    exact ne_iff.mpr ⟨⟨i, j⟩, mul_ne_zero hi hj⟩
  rw [mulHeight_eq hx, mulHeight_eq hy, mulHeight_eq hxy, mul_mul_mul_comm, ← Multiset.prod_map_mul,
    ← finprod_mul_distrib
        (hasFiniteMulSupport_iSup_nonarchAbsVal hx) (hasFiniteMulSupport_iSup_nonarchAbsVal hy)]
  congr <;> ext1 v
  · exact Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v x y
  · exact Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg v.val x y

open Real in
/-- The logarithmic height of the "multiplication table" `fun (i, j) ↦ x i * y j`
is the sum of the logarithmic heights of `x` and `y`. -/
/-
**Height.logHeight_fun_mul_eq** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_fun_mul_eq {x : ι -> K} (hx : x != 0) {y : ι' -> K} (hy : y != 0
) : logHeight (fun a : ι × ι' => x a.1 * y a.2) = logHeight x + logHeight y
参数：hx : x != 0；hy : y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Height.mulHeight_pos`：mulHeight_pos (x : ι -> K) : 0 < mulHeight x
· 使用引理 `Height.mulHeight_fun_mul_eq`：mulHeight_fun_mul_eq {x : ι -> K} (hx : x !
= 0) {y : ι' -> K} (hy : y != 0) : mulHeight (fun a : ι × ι' => x a.1 * y a.2) =
 mulHeight x * mu…

--- 原说明 ---
The logarithmic height of the "multiplication table" `fun (i, j) ↦ x i * y j`
is the sum of the logarithmic heights of `x` and `y`.
-/
lemma logHeight_fun_mul_eq {x : ι → K} (hx : x ≠ 0) {y : ι' → K} (hy : y ≠ 0) :
    logHeight (fun a : ι × ι' ↦ x a.1 * y a.2) = logHeight x + logHeight y := by
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
/-
**Height.mulHeight_neg** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_neg (x : ι -> K) : mulHeight (-x) = mulHeight x
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddGroupSeminormClass.map_neg_eq_map`：∀ {F : Type u_7} {α : outParam (Ty
pe u_8)} {β : outParam (Type u_9)} {inst : AddGroup α} {inst_1 : AddCommMonoid β
}   {inst_2 : PartialOrder…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α

--- 原说明 ---
The multiplicative height of the pointwise negative of a tuple
equals its multiplicative height.
-/
lemma mulHeight_neg (x : ι → K) : mulHeight (-x) = mulHeight x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  simp [mulHeight_eq hx, mulHeight_eq <| neg_ne_zero.mpr hx]

/-- The logarithmic height of the pointwise negative of a tuple
equals its logarithmic height. -/
@[simp]
/-
**Height.logHeight_neg** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_neg (x : ι -> K) : logHeight (-x) = logHeight x
参数：x : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_neg`：mulHeight_neg (x : ι -> K) : mulHeight (-x) = mulH
eight x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The logarithmic height of the pointwise negative of a tuple
equals its logarithmic height.
-/
lemma logHeight_neg (x : ι → K) : logHeight (-x) = logHeight x := by
  simp [logHeight_eq_log_mulHeight]

section tuples

variable [Finite ι]

/-- The multiplicative height of a pointwise product of tuples is bounded by the product
of their multiplicative heights. -/
/-
**Height.mulHeight_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：mulHeight_mul_le (x y : ι -> K) : mulHeight (x * y) <= mulHeight x * mulHe
ight y
参数：x y : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_eq_one_of_subsingleton`：mulHeight_eq_one_of_subsingleto
n {ι : Type*} [Subsingleton ι] (x : ι -> K) : mulHeight x = 1
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `Height.mulHeight_zero`：mulHeight_zero : mulHeight (0 : ι -> K) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Height.one_le_mulHeight`：one_le_mulHeight (x : ι -> K) : 1 <= mulHeight 
x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Height.mulHeight_fun_mul_eq`：mulHeight_fun_mul_eq {x : ι -> K} (hx : x !
= 0) {y : ι' -> K} (hy : y != 0) : mulHeight (fun a : ι × ι' => x a.1 * y a.2) =
 mulHeight x * mu…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Height.mulHeight_comp_le`：mulHeight_comp_le (f : ι -> ι') (x : ι' -> K) 
: mulHeight (x ∘ f) <= mulHeight x
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)

--- 原说明 ---
The multiplicative height of a pointwise product of tuples is bounded by the pro
duct
of their multiplicative heights.
-/
lemma mulHeight_mul_le (x y : ι → K) : mulHeight (x * y) ≤ mulHeight x * mulHeight y := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  rcases eq_or_ne x 0 with rfl | hx
  · simpa using one_le_mulHeight y
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using one_le_mulHeight x
  rw [← mulHeight_fun_mul_eq hx hy,
    show x * y = (fun a ↦ x a.1 * y a.2) ∘ Function.diag by ext1; simp]
  exact mulHeight_comp_le ..

open Real in
/-- The logarithmic height of a pointwise product of tuples is bounded by the sum
of their logarithmic heights. -/
/-
**Height.logHeight_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `Height`。
形式化陈述：logHeight_mul_le (x y : ι -> K) : logHeight (x * y) <= logHeight x + logHe
ight y
参数：x y : ι -> K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Height.mulHeight_pos`：mulHeight_pos (x : ι -> K) : 0 < mulHeight x
· 使用引理 `Real.log_le_log`：log_le_log (hx : 0 < x) (hxy : x <= y) : log x <= log y
· 使用引理 `Height.mulHeight_mul_le`：mulHeight_mul_le (x y : ι -> K) : mulHeight (x 
* y) <= mulHeight x * mulHeight y

--- 原说明 ---
The logarithmic height of a pointwise product of tuples is bounded by the sum
of their logarithmic heights.
-/
lemma logHeight_mul_le (x y : ι → K) : logHeight (x * y) ≤ logHeight x + logHeight y := by
  simp only [logHeight_eq_log_mulHeight]
  pull (disch := positivity) log
  exact log_le_log (by positivity) <| mulHeight_mul_le ..

end tuples

/-- The multiplicative height of `x * y` is at most the product of the multiplicative heights
of `x` and `y`. -/
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of `x * y` is at most the product of the multiplicativ
e heights
of `x` and `y`.
-/
lemma mulHeight₁_mul_le (x y : K) : mulHeight₁ (x * y) ≤ mulHeight₁ x * mulHeight₁ y := by
  simp only [mulHeight₁_eq_mulHeight]
  rw [show ![x * y, 1] = ![x, 1] * ![y, 1] by ext i; fin_cases i <;> simp]
  exact mulHeight_mul_le ![x, 1] ![y, 1]

open Real in
/-- The logarithmic height of `x * y` is at most the sum of the logarithmic heights
of `x` and `y`. -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of `x * y` is at most the sum of the logarithmic heights
of `x` and `y`.
-/
lemma logHeight₁_mul_le (x y : K) : logHeight₁ (x * y) ≤ logHeight₁ x + logHeight₁ y := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
  exact log_le_log (by positivity) <| mulHeight₁_mul_le ..

/-- The multiplicative height of a product of field elements is bounded above by the product
of their multiplicative heights. -/
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of a product of field elements is bounded above by the
 product
of their multiplicative heights.
-/
lemma mulHeight₁_prod_le (s : Finset ι) (x : ι → K) :
    mulHeight₁ (∏ i ∈ s, x i) ≤ ∏ i ∈ s, mulHeight₁ (x i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    simp only [Finset.prod_insert hb]
    grw [← ih]
    exact mulHeight₁_mul_le ..

open Real in
/-- The logarithmic height of a product of field elements is bounded above by the sum
of their logarithmic heights. -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of a product of field elements is bounded above by the su
m
of their logarithmic heights.
-/
lemma logHeight₁_prod_le (s : Finset ι) (x : ι → K) :
    logHeight₁ (∏ i ∈ s, x i) ≤ ∑ i ∈ s, logHeight₁ (x i) := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  rw [← log_prod (fun _ _ ↦ by positivity)]
  exact log_le_log (by positivity) <| mulHeight₁_prod_le ..

end Height

/-!
### Bounds for the height of sums of field elements

We prove the general case (finite sums of arbitrary length) first and deduce the result
for sums of two elements from it.
-/

namespace Finset

variable {R S : Type*} [Semiring R] [CommSemiring S] [LinearOrder S] [IsOrderedRing S]

/-- The "local" version of the height bound for arbitrary sums for general (possibly archimedean)
absolute values. -/
/-
**Finset.max_abv_sum_one_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：max_abv_sum_one_le [CharZero S] (v : AbsoluteValue R S) {ι : Type*} {s : F
inset ι} (hs : s.Nonempty) (x : ι -> R) : max (v (∑ i in s, x i)) 1 <= #s * ∏ i 
in s, max (v (x i)) 1
参数：v : AbsoluteValue R S；hs : s.Nonempty；x : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `AbsoluteValue.sum_le`：AbsoluteValue.sum_le [Semiring R] [Semiring S] [Pa
rtialOrder S] [IsOrderedRing S] (abv : AbsoluteValue R S) (s : Finset ι) (f : ι 
-> R) : ab…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用引理 `Finset.le_prod_max_one`：le_prod_max_one {M : Type*} [CommMonoidWithZero 
M] [LinearOrder M] [ZeroLEOneClass M] [PosMulMono M] {i : ι} (hi : i in s) (f : 
ι -> M) : f …
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `Finset.one_le_prod`：one_le_prod (hf : forall i in s, 1 <= f i) : 1 <= ∏ 
i in s, f i
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)

--- 原说明 ---
The "local" version of the height bound for arbitrary sums for general (possibly
 archimedean)
absolute values.
-/
lemma max_abv_sum_one_le [CharZero S] (v : AbsoluteValue R S) {ι : Type*} {s : Finset ι}
    (hs : s.Nonempty) (x : ι → R) :
    max (v (∑ i ∈ s, x i)) 1 ≤ #s * ∏ i ∈ s, max (v (x i)) 1 := by
  refine sup_le ?_ ?_
  · rw [← nsmul_eq_mul, ← sum_const]
    grw [v.sum_le s x]
    gcongr with i hi
    exact le_prod_max_one hi fun i ↦ v (x i)
  · nth_rewrite 1 [← mul_one 1]
    gcongr
    · simp [hs]
    · exact s.one_le_prod fun _ _ ↦ le_max_right ..

/-- The "local" version of the height bound for arbitrary sums for nonarchimedean
absolute values. -/
/-
**Finset.max_abv_sum_one_le_of_isNonarchimedean** 是 Mathlib 中的一个引理，位于命名空间 `Finse
t`。
形式化陈述：max_abv_sum_one_le_of_isNonarchimedean {v : AbsoluteValue R S} (hv : IsNon
archimedean v) {ι : Type*} (s : Finset ι) (x : ι -> R) : max (v (∑ i in s, x i))
 1 <= ∏ i in s, max (v (x i)) 1
参数：hv : IsNonarchimedean v；s : Finset ι；x : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AbsoluteValue.map_zero`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring
 R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S),
 abv 0 = 0
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用引理 `IsNonarchimedean.apply_sum_le_sup`：apply_sum_le_sup {α β : Type*} [AddCo
mmMonoid α] {f : α -> R} (nonarch : IsNonarchimedean f) {s : Finset β} (hnonempt
y : s.Nonempty) {l : β …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用引理 `Finset.le_prod_max_one`：le_prod_max_one {M : Type*} [CommMonoidWithZero 
M] [LinearOrder M] [ZeroLEOneClass M] [PosMulMono M] {i : ι} (hi : i in s) (f : 
ι -> M) : f …
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Finset.one_le_prod`：one_le_prod (hf : forall i in s, 1 <= f i) : 1 <= ∏ 
i in s, f i
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b

--- 原说明 ---
The "local" version of the height bound for arbitrary sums for nonarchimedean
absolute values.
-/
lemma max_abv_sum_one_le_of_isNonarchimedean {v : AbsoluteValue R S} (hv : IsNonarchimedean v)
    {ι : Type*} (s : Finset ι) (x : ι → R) :
    max (v (∑ i ∈ s, x i)) 1 ≤ ∏ i ∈ s, max (v (x i)) 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  refine sup_le ?_ <| s.one_le_prod fun _ _ ↦ le_max_right ..
  grw [hv.apply_sum_le_sup hs]
  exact sup'_le hs (fun i ↦ v (x i)) fun i hi ↦ le_prod_max_one hi fun i ↦ v (x i)

end Finset

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

open AdmissibleAbsValues Real

open Finset Multiset in
/-- The multiplicative height of a nonempty finite sum of field elements is at most
`n ^ (totalWeight K)` times the product of the individual multiplicative
heights, where `n` is the number of terms. -/
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of a nonempty finite sum of field elements is at most
`n ^ (totalWeight K)` times the product of the individual multiplicative
heights, where `n` is the number of terms.
-/
lemma mulHeight₁_sum_le {α : Type*} {s : Finset α} (hs : s.Nonempty) (x : α → K) :
    mulHeight₁ (∑ a ∈ s, x a) ≤ #s ^ (totalWeight K) * ∏ a ∈ s, mulHeight₁ (x a) := by
  simp only [mulHeight₁_eq, totalWeight]
  rw [prod_mul_distrib, ← prod_replicate, ← map_const, ← finprod_prod_comm _ _ (by fun_prop),
    ← prod_map_prod, ← mul_assoc, ← prod_map_mul]
  simp only [Function.const_apply]
  gcongr
  · exact finprod_nonneg fun _ ↦ by positivity
  · exact prod_map_nonneg fun _ h ↦ by positivity
  · exact prod_map_le_prod_map₀ _ _ (fun _ _ ↦ by positivity) fun _ _ ↦ max_abv_sum_one_le _ hs x
  · exact finprod_le_finprod (by fun_prop) (fun _ ↦ by grind) (by fun_prop) <|
      fun v ↦ max_abv_sum_one_le_of_isNonarchimedean (isNonarchimedean _ v.prop) _ x

open Finset in
/-- The logarithmic height of a finite sum of field elements is at most
`totalWeight K * log n` plus the sum of the individual logarithmic heights,
where `n` is the number of terms.

(Note that here we do not need to assume that `s` is nonempty, due to the convenient
junk value `log 0 = 0`.) -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of a finite sum of field elements is at most
`totalWeight K * log n` plus the sum of the individual logarithmic heights,
where `n` is the number of terms.

(Note that here we do not need to assume that `s` is nonempty, due to the conven
ient
junk value `log 0 = 0`.)
-/
lemma logHeight₁_sum_le {α : Type*} (s : Finset α) (x : α → K) :
    logHeight₁ (∑ a ∈ s, x a) ≤ (totalWeight K) * log #s + ∑ a ∈ s, logHeight₁ (x a) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  simp only [logHeight₁_eq_log_mulHeight₁]
  have : ∀ a ∈ s, mulHeight₁ (x a) ≠ 0 := fun _ _ ↦ by positivity
  have : (#s : ℝ) ^ totalWeight K ≠ 0 := by simp [hs.ne_empty]
  pull (disch := first | assumption | positivity) log
  exact (log_le_log <| by positivity) <| mulHeight₁_sum_le hs x

/-- The multiplicative height of `-x` is the same as that of `x`. -/
@[simp]
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of `-x` is the same as that of `x`.
-/
lemma mulHeight₁_neg (x : K) : mulHeight₁ (-x) = mulHeight₁ x := by
  simp [mulHeight₁_eq]

/-- The logarithmic height of `-x` is the same as that of `x`. -/
@[simp]
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of `-x` is the same as that of `x`.
-/
lemma logHeight₁_neg (x : K) : logHeight₁ (-x) = logHeight₁ x := by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_neg]

/-- The multiplicative height of `x + y` is at most `2 ^ totalWeight K`
times the product of the multiplicative heights of `x` and `y`. -/
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of `x + y` is at most `2 ^ totalWeight K`
times the product of the multiplicative heights of `x` and `y`.
-/
lemma mulHeight₁_add_le (x y : K) :
    mulHeight₁ (x + y) ≤ 2 ^ totalWeight K * mulHeight₁ x * mulHeight₁ y := by
  rw [show x + y = Finset.univ.sum ![x, y] by simp, mul_assoc]
  grw [mulHeight₁_sum_le Finset.univ_nonempty ![x, y]]
  simp

/-- The logarithmic height of `x + y` is at most `totalWeight K * log 2`
plus the sum of the logarithmic heights of `x` and `y`. -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of `x + y` is at most `totalWeight K * log 2`
plus the sum of the logarithmic heights of `x` and `y`.
-/
lemma logHeight₁_add_le (x y : K) :
    logHeight₁ (x + y) ≤ totalWeight K * log 2 + logHeight₁ x + logHeight₁ y := by
  simp only [logHeight₁_eq_log_mulHeight₁]
  pull (disch := positivity) log
  exact (log_le_log <| by positivity) <| mulHeight₁_add_le ..

/-- The multiplicative height of `x - y` is at most `2 ^ totalWeight K`
times the product of the multiplicative heights of `x` and `y`. -/
/-
**Height.mulHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：mulHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of `x - y` is at most `2 ^ totalWeight K`
times the product of the multiplicative heights of `x` and `y`.
-/
lemma mulHeight₁_sub_le (x y : K) :
    mulHeight₁ (x - y) ≤ 2 ^ totalWeight K * mulHeight₁ x * mulHeight₁ y := by
  rw [sub_eq_add_neg, ← mulHeight₁_neg y]
  exact mulHeight₁_add_le x (-y)

/-- The logarithmic height of `x - y` is at most `totalWeight K * log 2`
plus the sum of the logarithmic heights of `x` and `y`. -/
/-
**Height.logHeight** 是 Mathlib 中的一个定义，位于命名空间 `Height`。
形式化陈述：logHeight (x : ι -> K) : Real
参数：x : ι -> K。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of `x - y` is at most `totalWeight K * log 2`
plus the sum of the logarithmic heights of `x` and `y`.
-/
lemma logHeight₁_sub_le (x y : K) :
    logHeight₁ (x - y) ≤ totalWeight K * log 2 + logHeight₁ x + logHeight₁ y := by
  rw [sub_eq_add_neg, ← logHeight₁_neg y]
  exact logHeight₁_add_le x (-y)

end Height

