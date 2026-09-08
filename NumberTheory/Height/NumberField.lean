/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Ralf Stephan
-/
module

public import Mathlib.NumberTheory.Height.Basic
public import Mathlib.NumberTheory.Height.Northcott
public import Mathlib.NumberTheory.NumberField.ProductFormula

import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Hom.Lattice
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Heights over number fields

We provide an instance of `Height.AdmissibleAbsValues` for algebraic number fields
and set up some API.

## Main results

* Heights on number fields satisfy the **Northcott property**: If `K` is a number field,
  then the set of elements of `K` of bounded (multiplicative or logarithmic) height is finite;
  see `NumberField.finite_setOfPred_mulHeight₁_le` and `NumberField.finite_setOfPred_logHeight₁_le`.
  We also provide instances for `Northcott (mulHeight₁ (K := K))` (which automatically leads
  also to `Northcott (logHeight₁ (K := K))`).

## TODO

When this file gets long, split the material on heights over `ℚ` off into a file `Rat.lean`.
-/

@[expose] public section

/-!
### Instance for number fields
-/

namespace NumberField

open Height

variable {K : Type*} [Field K] [NumberField K]

variable (K) in
/-- The infinite places of a number field `K` as a `Multiset` of absolute values on `K`,
with multiplicity given by `InfinitePlace.mult`. -/
/-
**NumberField.multisetInfinitePlace** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：multisetInfinitePlace : Multiset (AbsoluteValue K Real)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The infinite places of a number field `K` as a `Multiset` of absolute values on 
`K`,
with multiplicity given by `InfinitePlace.mult`.
-/
noncomputable def multisetInfinitePlace : Multiset (AbsoluteValue K ℝ) :=
  .bind (.univ : Finset (InfinitePlace K)).val fun v ↦ .replicate v.mult v.val

@[simp]
/-
**NumberField.mem_multisetInfinitePlace** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：mem_multisetInfinitePlace {v : AbsoluteValue K Real} : v in multisetInfini
tePlace K ↔ IsInfinitePlace v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_multisetInfinitePlace {v : AbsoluteValue K ℝ} :
    v ∈ multisetInfinitePlace K ↔ IsInfinitePlace v := by
  simp [multisetInfinitePlace, Multiset.mem_replicate, isInfinitePlace_iff, eq_comm (a := v)]

set_option backward.isDefEq.respectTransparency false in
/-
**NumberField.count_multisetInfinitePlace_eq_mult** 是 Mathlib 中的一个引理，位于命名空间 `Num
berField`。
形式化陈述：count_multisetInfinitePlace_eq_mult [DecidableEq (AbsoluteValue K Real)] (
v : InfinitePlace K) : (multisetInfinitePlace K).count v.val = v.mult
参数：AbsoluteValue K Real；v : InfinitePlace K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.count_bind`：count_bind [DecidableEq α] {m : Multiset β} {f : β 
-> Multiset α} {a : α} : count a (bind m f) = sum (m.map fun b => count a <| f b
)
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.count_replicate`：count_replicate (a b : α) (n : Nat) : count a 
(replicate n b) = if b = a then n else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Fintype.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMono
id M] [inst_1 : Fintype ι] [inst_2 : DecidableEq ι] (i : ι)   (f : ι → M), (∑ j,
 if j = i…
-/
lemma count_multisetInfinitePlace_eq_mult [DecidableEq (AbsoluteValue K ℝ)] (v : InfinitePlace K) :
    (multisetInfinitePlace K).count v.val = v.mult := by
  have : DecidableEq (InfinitePlace K) := Subtype.instDecidableEq
  simpa only [multisetInfinitePlace, Multiset.count_bind, Finset.sum_map_val,
    Multiset.count_replicate, ← Subtype.ext_iff] using Fintype.sum_ite_eq' v ..

set_option backward.isDefEq.respectTransparency.types false in
-- For the user-facing version, see `prod_archAbsVal_eq` below.
/-
**NumberField.prod_multisetInfinitePlace_eq** 是 Mathlib 中的一个引理，位于命名空间 `NumberFie
ld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma prod_multisetInfinitePlace_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    ((multisetInfinitePlace K).map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult := by
  classical
  rw [Finset.prod_multiset_map_count]
  exact Finset.prod_bij' (fun w hw ↦ ⟨w, mem_multisetInfinitePlace.mp <| Multiset.mem_dedup.mp hw⟩)
    (fun v _ ↦ v.val) (fun _ _ ↦ Finset.mem_univ _) (fun v _ ↦ by simp [v.isInfinitePlace])
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) fun w hw ↦ by rw [count_multisetInfinitePlace_eq_mult ⟨w, _⟩]

noncomputable
/-
**NumberField.instAdmissibleAbsValues** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
形式化陈述：instAdmissibleAbsValues : AdmissibleAbsValues K where archAbsVal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.FinitePlace.hasFiniteMulSupport`：hasFiniteMulSupport {x : K}
 (h_x_nezero : x != 0) : (fun w : FinitePlace K => w x).HasFiniteMulSupport
-/
instance instAdmissibleAbsValues : AdmissibleAbsValues K where
  archAbsVal := multisetInfinitePlace K
  nonarchAbsVal := {v | IsFinitePlace v}
  isNonarchimedean v hv := FinitePlace.add_le ⟨v, by simpa using! hv⟩
  hasFiniteMulSupport := FinitePlace.hasFiniteMulSupport
  product_formula {x} hx := private prod_multisetInfinitePlace_eq (· x) ▸ prod_abs_eq_one hx

open AdmissibleAbsValues
/-
**NumberField.prod_archAbsVal_eq** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：prod_archAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K Real ->
 M) : (archAbsVal.map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult
参数：f : AbsoluteValue K Real -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.Height.NumberField.0.NumberField.prod_mult
isetInfinitePlace_eq`：∀ {K : Type u_1} [inst : Field K] [inst_1 : NumberField K]
 {M : Type u_2} [inst_2 : CommMonoid M]   (f : AbsoluteValue K ℝ → M), (Multiset
.m…
-/
lemma prod_archAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (archAbsVal.map f).prod = ∏ v : InfinitePlace K, f v.val ^ v.mult :=
  prod_multisetInfinitePlace_eq f
/-
**NumberField.prod_nonarchAbsVal_eq** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：prod_nonarchAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K Real
 -> M) : (∏ᶠ v : nonarchAbsVal, f v.val) = ∏ᶠ v : FinitePlace K, f v.val
参数：f : AbsoluteValue K Real -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_nonarchAbsVal_eq {M : Type*} [CommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (∏ᶠ v : nonarchAbsVal, f v.val) = ∏ᶠ v : FinitePlace K, f v.val :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
open Finset Multiset in
/-
**NumberField.sum_archAbsVal_eq** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：sum_archAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K Real 
-> M) : (archAbsVal.map f).sum = ∑ v : InfinitePlace K, v.mult • f v.val
参数：f : AbsoluteValue K Real -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_multiset_map_count`：∀ {ι : Type u_1} [inst : DecidableEq ι] (
s : Multiset ι) {M : Type u_5} [inst_1 : AddCommMonoid M] (f : ι → M),   (Multis
et.map f s).sum = ∑…
· 使用定理 `Finset.sum_bij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a
 : ι)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `NumberField.mem_multisetInfinitePlace`：mem_multisetInfinitePlace {v : Ab
soluteValue K Real} : v in multisetInfinitePlace K ↔ IsInfinitePlace v
· 使用定理 `Multiset.mem_dedup`：mem_dedup {a : α} {s : Multiset α} : a in dedup s ↔ 
a in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `NumberField.count_multisetInfinitePlace_eq_mult`：count_multisetInfiniteP
lace_eq_mult [DecidableEq (AbsoluteValue K Real)] (v : InfinitePlace K) : (multi
setInfinitePlace K).count v.val = v.m…
-/
lemma sum_archAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (archAbsVal.map f).sum = ∑ v : InfinitePlace K, v.mult • f v.val := by
  classical
  rw [sum_multiset_map_count]
  exact sum_bij' (⟨·, mem_multisetInfinitePlace.mp <| mem_dedup.mp ·⟩)
    _ (by simp) (by simp [InfinitePlace.isInfinitePlace, archAbsVal]) (by simp) (fun _ _ ↦ rfl)
    fun w hw ↦ by
      simp only [archAbsVal, mem_toFinset, mem_multisetInfinitePlace] at hw ⊢
      simp [count_multisetInfinitePlace_eq_mult ⟨w, hw⟩]
/-
**NumberField.sum_nonarchAbsVal_eq** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：sum_nonarchAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K Re
al -> M) : (∑ᶠ v : nonarchAbsVal, f v.val) = ∑ᶠ v : FinitePlace K, f v.val
参数：f : AbsoluteValue K Real -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sum_nonarchAbsVal_eq {M : Type*} [AddCommMonoid M] (f : AbsoluteValue K ℝ → M) :
    (∑ᶠ v : nonarchAbsVal, f v.val) = ∑ᶠ v : FinitePlace K, f v.val :=
  rfl

/-- This is the familiar definition of the multiplicative height on a number field. -/
/-
**NumberField.mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the familiar definition of the multiplicative height on a number field.
-/
lemma mulHeight₁_eq (x : K) :
    mulHeight₁ x =
      (∏ v : InfinitePlace K, max (v x) 1 ^ v.mult) * ∏ᶠ v : FinitePlace K, max (v x) 1 := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight₁_eq,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v ↦ max (v x) 1]

open Real in
/-- This is the familiar definition of the logarithmic height on a number field. -/
/-
**NumberField.logHeight** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the familiar definition of the logarithmic height on a number field.
-/
lemma logHeight₁_eq (x : K) :
    logHeight₁ x =
      (∑ v : InfinitePlace K, v.mult * log⁺ (v x)) + ∑ᶠ v : FinitePlace K, log⁺ (v x) := by
  simp only [← nsmul_eq_mul, FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.logHeight₁_eq,
    sum_archAbsVal_eq, sum_nonarchAbsVal_eq fun v ↦ log⁺ (v x)]

/-- This is the familiar definition of the multiplicative height on (nonzero) tuples
of number field elements. -/
/-
**NumberField.mulHeight_eq** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：mulHeight_eq {ι : Type*} {x : ι -> K} (hx : x != 0) : mulHeight x = (∏ v :
 InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.mulHeight_eq`：mulHeight_eq {x : ι -> K} (hx : x != 0) : mulHeight
 x = (archAbsVal.map fun v => ⨆ i, v (x i)).prod * ∏ᶠ v : nonarchAbsVal, ⨆ i, v.
val (x i)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `NumberField.prod_archAbsVal_eq`：prod_archAbsVal_eq {M : Type*} [CommMono
id M] (f : AbsoluteValue K Real -> M) : (archAbsVal.map f).prod = ∏ v : Infinite
Place K, f v.val ^ v…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
This is the familiar definition of the multiplicative height on (nonzero) tuples
of number field elements.
-/
lemma mulHeight_eq {ι : Type*} {x : ι → K} (hx : x ≠ 0) :
    mulHeight x =
      (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) := by
  simp only [FinitePlace.coe_apply, InfinitePlace.coe_apply, Height.mulHeight_eq hx,
    prod_archAbsVal_eq, prod_nonarchAbsVal_eq fun v ↦ ⨆ i, v (x i)]

open Classical IntermediateField in
/-- The absolute multiplicative height of an algebraic number. This is defined for elements of any
field of characteristic zero, with a junk value of `0` if the element is not algebraic. -/
/-
**NumberField.absMulHeight** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute multiplicative height of an algebraic number. This is defined for e
lements of any
field of characteristic zero, with a junk value of `0` if the element is not alg
ebraic.
-/
noncomputable def absMulHeight₁ {K : Type*} [Field K] [CharZero K] (x : K) : ℝ :=
  if hx : IsIntegral ℚ x then
    haveI : FiniteDimensional ℚ ℚ⟮x⟯ := adjoin.finiteDimensional hx
    haveI : NumberField ℚ⟮x⟯ := {}
    (Height.mulHeight₁ (AdjoinSimple.gen ℚ x)) ^ (Module.finrank ℚ ℚ⟮x⟯ : ℝ)⁻¹
  else 1

/-- The absolute logarithmic height of an algebraic number. This is defined for elements of any
field of characteristic zero, with a junk value of `0` if the element is not algebraic. -/
/-
**NumberField.absLogHeight** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The absolute logarithmic height of an algebraic number. This is defined for elem
ents of any
field of characteristic zero, with a junk value of `0` if the element is not alg
ebraic.
-/
noncomputable def absLogHeight₁ {K : Type*} [Field K] [CharZero K] (x : K) : ℝ :=
  (absMulHeight₁ x).log

variable (K) in
/-
**NumberField.totalWeight_eq_sum_mult** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：totalWeight_eq_sum_mult : totalWeight K = ∑ v : InfinitePlace K, v.mult
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sum_map_toList`：∀ {ι : Type u_2} {M : Type u_3} [inst : AddComm
Monoid M] (s : Multiset ι) (f : ι → M),   (List.map f s.toList).sum = (Multiset.
map f s).sum
· 使用定理 `Fin.sum_univ_fun_getElem`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddCom
mMonoid M] (l : List ι) (f : ι → M), ∑ i, f l[↑i] = (List.map f l).sum
· 使用定理 `Multiset.length_toList`：length_toList (s : Multiset α) : s.toList.length
 = card s
· 使用定理 `Fin.sum_const`：∀ {M : Type u_2} [inst : AddCommMonoid M] (n : ℕ) (x : M)
, ∑ _i, x = n • x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `NumberField.sum_archAbsVal_eq`：sum_archAbsVal_eq {M : Type*} [AddCommMon
oid M] (f : AbsoluteValue K Real -> M) : (archAbsVal.map f).sum = ∑ v : Infinite
Place K, v.mult • f…
-/
lemma totalWeight_eq_sum_mult : totalWeight K = ∑ v : InfinitePlace K, v.mult := by
  simp only [totalWeight]
  convert! sum_archAbsVal_eq (fun _ ↦ (1 : ℕ))
  · rw [← Multiset.sum_map_toList, ← Fin.sum_univ_fun_getElem, ← Multiset.length_toList,
      Fin.sum_const, Multiset.length_toList, smul_eq_mul, mul_one]
  · simp

variable (K) in
/-
**NumberField.totalWeight_eq_finrank** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：totalWeight_eq_finrank : totalWeight K = Module.finrank Rat K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NumberField.totalWeight_eq_sum_mult`：totalWeight_eq_sum_mult : totalWeig
ht K = ∑ v : InfinitePlace K, v.mult
· 使用定理 `NumberField.InfinitePlace.sum_mult_eq`：sum_mult_eq [NumberField K] : ∑ w
 : InfinitePlace K, mult w = Module.finrank Rat K
-/
lemma totalWeight_eq_finrank : totalWeight K = Module.finrank ℚ K := by
  rw [totalWeight_eq_sum_mult, InfinitePlace.sum_mult_eq]

variable (K) in
@[grind! .]
/-
**NumberField.totalWeight_pos** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：totalWeight_pos : 0 < totalWeight K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.instNonemptyInfinitePlaceOfRingHomComplex`：∀ (K : Type u_1) 
[inst : Field K] [Nonempty (K →+* ℂ)], Nonempty (NumberField.InfinitePlace K)
· 使用定理 `NumberField.Embeddings.instNonemptyRingHom`：∀ (K : Type u_1) [inst : Fie
ld K] (A : Type u_2) [inst_1 : Field A] [CharZero A] [NumberField K] [IsAlgClose
d A],   Nonempty (K →+* A)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_bind`：card_bind : card (s.bind f) = (s.map (card ∘ f)).sum
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.card_replicate`：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.rep
licate n a).card = n
· 使用定理 `Fintype.sum_pos`：∀ {ι : Type u_1} {M : Type u_4} [inst : Fintype ι] [ins
t_1 : AddCommMonoid M] [inst_2 : PartialOrder M]   [IsOrderedCancelAddMonoid M] 
{f : …
· 使用定理 `Ne.pos`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α], a ≠ 0 → 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Pi.instCanonicallyOrderedAddForall`：∀ {ι : Type u_6} {Z : ι → Type u_7} 
[inst : (i : ι) → AddMonoid (Z i)] [inst_1 : (i : ι) → PartialOrder (Z i)]   [∀ 
(i : ι), CanonicallyOrde…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `NumberField.InfinitePlace.mult_ne_zero`：mult_ne_zero {w : InfinitePlace 
K} : mult w != 0
-/
lemma totalWeight_pos : 0 < totalWeight K := by
  have : Inhabited (InfinitePlace K) := Classical.inhabited_of_nonempty'
  simpa [totalWeight, archAbsVal, multisetInfinitePlace]
    using Fintype.sum_pos
      (Function.ne_iff.mpr ⟨default, (default : InfinitePlace K).mult_ne_zero⟩).pos

variable {ι : Type*} [Finite ι] {x : ι → 𝓞 K}

open IsDedekindDomain.HeightOneSpectrum Ideal FinitePlace Finite in
-- This statement is a step in the proof of the next one, which is strictly stronger.
/-
**NumberField.absNorm_mul_finprod_finitePlace_eq_one_aux** 是 Mathlib 中的一个引理，位于命名
空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma absNorm_mul_finprod_finitePlace_eq_one_aux [Nonempty ι] (hx : ∀ i, x i ≠ 0) :
    (span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = 1 := by
  have H j : span {x j} ≠ ⊥ := mt span_singleton_eq_bot.mp (hx j)
  have hx' : ⨆ i, span {x i} ≠ ⊥ :=
    iSup_eq_bot.not.mpr <| not_forall.mpr ⟨Classical.ofNonempty, H _⟩
  rw [span_range_eq_iSup, ← finprod_finitePlace_pow_multiplicity hx',
    map_finprod _ <| hasFiniteMulSupport_fun_pow_multiplicity hx' (·), Nat.cast_finprod',
    ← finprod_mul_distrib ?hf <| .iSup (FinitePlace.hasFiniteMulSupport <| mod_cast hx ·)]
  case hf =>
    simp only [map_pow, Nat.cast_pow]
    exact hasFiniteMulSupport_fun_pow_multiplicity hx' fun v ↦ (v.absNorm : ℝ)
  refine finprod_eq_one_of_forall_eq_one fun v ↦ ?_
  have hn := absNorm_eq_zero_iff.not.mpr v.maximalIdeal.ne_bot
  have h {m : ℕ} : (0 : ℝ) < ↑(absNorm v.maximalIdeal.asIdeal ^ m) := by positivity
  rw [multiplicity_iSup _ H, map_pow, mul_eq_one_iff_inv_eq₀ h.ne',
    map_iInf_of_monotone (fun _ ↦ multiplicity ..) (pow_right_monotone <| by lia),
    map_iInf_of_monotone _ Nat.mono_cast,
    map_iInf_of_antitoneOn antitoneOn_inv_pos fun _ ↦ Set.mem_ofPred.mpr h]
  refine iSup_congr fun i ↦ ?_
  rw [← mul_eq_one_iff_inv_eq₀ h.ne', mul_comm, Nat.cast_pow]
  exact apply_mul_absNorm_pow_eq_one v (hx i)

-- TODO: Generalize the following to integral closures of `ℤ` in `K` in place of `𝓞 K`.
open Ideal in
/-- This statement is equivalent to the fact that the "finite part" of the multiplicative
height of a (non-zero) tuple `x` is the inverse of the absolute norm of the ideal generated
by the values of `x`. We state it in a way that avoids taking an inverse. -/
/-
**NumberField.absNorm_mul_finprod_finitePlace_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `
NumberField`。
形式化陈述：absNorm_mul_finprod_finitePlace_eq_one (hx : x != 0) : (span <| Set.range 
x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `algebraMap.coe_zero`：coe_zero : (↑(0 : R) : A) = 0
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NumberField.RingOfIntegers.instIsTorsionFree_2`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   Module.IsT
orsionFree (NumberField.RingOfIntege…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `Function.hfunext`：hfunext {α α' : Sort u} {β : α -> Sort v} {β' : α' -> 
Sort v} {f : forall a, β a} {f' : forall a, β' a} (hα : α = α') (h : forall a a'
, a ≍ …
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `Ideal.span_range_eq_span_range_support`：span_range_eq_span_range_support
 (x : ι -> α) : span (range x) = span (range fun i : x.support => x i.val)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Finite.iSup_eq_iSup_subtype`：∀ {ι : Type u_1} {K : Type u_2} {M : Type u
_3} {F : Type u_4} [Finite ι] [inst : Zero K] [inst_1 : Zero M]   [inst_2 : Cond
itionallyComplete…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `NumberField.FinitePlace.instMonoidWithZeroHomClassReal`：∀ {K : Type u_1}
 [inst : Field K] [inst_1 : NumberField K], MonoidWithZeroHomClass (NumberField.
FinitePlace K) K ℝ
· 使用定理 `NumberField.FinitePlace.instNonnegHomClassReal`：∀ {K : Type u_1} [inst :
 Field K] [inst_1 : NumberField K], NonnegHomClass (NumberField.FinitePlace K) K
 ℝ
· 使用定理 `_private.Mathlib.NumberTheory.Height.NumberField.0.NumberField.absNorm_m
ul_finprod_finitePlace_eq_one_aux`：∀ {K : Type u_1} [inst : Field K] [inst_1 : N
umberField K] {ι : Type u_2} [Finite ι]   {x : ι → NumberField.RingOfIntegers K}
 [Nonempty ι], …

--- 原说明 ---
This statement is equivalent to the fact that the "finite part" of the multiplic
ative
height of a (non-zero) tuple `x` is the inverse of the absolute norm of the idea
l generated
by the values of `x`. We state it in a way that avoids taking an inverse.
-/
lemma absNorm_mul_finprod_finitePlace_eq_one (hx : x ≠ 0) :
    (span <| Set.range x).absNorm * ∏ᶠ v : FinitePlace K, ⨆ i, v (x i) = 1 := by
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hx
  let i' : { j // (x j : K) ≠ 0 } := ⟨i₀, mod_cast hi₀⟩
  have : Nonempty _ := .intro i'
  have hI : span (Set.range x) = span (Set.range fun i : { j // (x j : K) ≠ 0 } ↦ x i.val) := by
    convert span_range_eq_span_range_support x <;> norm_cast
  have hx₀ : (fun i ↦ (x i : K)) ≠ 0 := Function.ne_iff.mpr ⟨_, i'.prop⟩
  simp_rw [Finite.iSup_eq_iSup_subtype hx₀, hI]
  exact absNorm_mul_finprod_finitePlace_eq_one_aux fun j ↦ mod_cast j.prop

end NumberField

/-!
### The Northcott property for heights on number fields

We show that a number field `K` has the **Northcott property** with respect to the multiplicative
and with respect to the logarithmic height, i.e., for any `B : ℝ` the set of elements `x : K`
such that `mulHeight₁ x ≤ B` (resp., `logHeight₁ x ≤ B`) is finite.
See `NumberField.finite_setOfPred_mulHeight₁_le` and `NumberField.finite_setOfPred_logHeight₁_le`.

The main idea of the proof is as follows. We show that for every `x : K` there is `n : ℕ` such that
`n * x` is an algebraic integer and `n ≤ mulHeight₁ x`; see `NumberField.exists_nat_le_mulHeight₁`.
We also show that the set of `a : 𝓞 K` such that `mulHeight₁ (a / n)` is bounded is finite;
see `NumberField.finite_setOfPred_prod_infinitePlace_iSup_le`. The result for the multiplicative
height follows by combining these two ingredients, and the result for the logarithmic height follows
from that for any field with a family of admissible absolute values
(see `Mathlib.NumberTheory.Height.Northcott`).
-/

section Northcott

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

section withIdeal

open Ideal

/-
**NumberField.relIndex_span_span_nat_mul** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma relIndex_span_span_nat_mul (m : ℕ) {n : ℕ} (hn : n ≠ 0) (a : 𝓞 K) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n * m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑(n * m), n * a}).toAddSubgroup := by
  let f : 𝓞 K →ₗ[𝓞 K] 𝓞 K := .mulLeft _ n
  have hf : Function.Injective (f : 𝓞 K →+ 𝓞 K) :=
    (injective_iff_map_eq_zero f).mpr fun _ _ ↦ by simp_all [f]
  have H₁ : span {(n * m : 𝓞 K)} = Submodule.map f (span {↑m}) := by
    simp [LinearMap.map_span, f]
  have H₂ : span {↑(n * m), n * a} = Submodule.map f (span {↑m, a}) := by
    simp [LinearMap.map_span, f, Set.image_pair]
  rw [H₁, H₂]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hf |>.symm
/-
**NumberField.relIndex_span_span_eq_relIndex_span_span** 是 Mathlib 中的一个引理，位于命名空间
 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma relIndex_span_span_eq_relIndex_span_span {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    {a b : 𝓞 K} (h : n * a = m * b) :
    (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {↑m, a}).toAddSubgroup =
      (span {(n : 𝓞 K)}).toAddSubgroup.relIndex (span {↑n, b}).toAddSubgroup := by
  refine (relIndex_span_span_nat_mul m hn a).trans ?_
  rw [mul_comm, mul_comm n, h]
  exact (relIndex_span_span_nat_mul n hm b).symm

open Module AddSubgroup LinearMap in
/-
**NumberField.exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow**
 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
形式化陈述：exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow (x : K) :
 exists n : Nat, n != 0 ∧ exists a : 𝓞 K, n * x = a ∧ (span {(n : 𝓞 K), a}).absN
orm = n ^ (Module.finrank Rat K - 1)
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsFractionRing.isAlgebraic_iff`：isAlgebraic_iff [Algebra A C] [Algebra K
 C] [IsScalarTower A K C] {x : C} : IsAlgebraic A x ↔ IsAlgebraic K x
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsAlgebraic.of_finite`：IsAlgebraic.of_finite (e : A) [Module.Finite R A]
 : IsAlgebraic R e
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用引理 `IsAlgebraic.exists_nsmul_eq`：exists_nsmul_eq [IsIntegralClosure S Int K]
 {x : K} (hx : IsAlgebraic Int x) : exists (m : Nat) (s : S), m != 0 ∧ m • x = a
lgebraMap S K s
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureInt`：∀ {K : Type u_1} [i
nst : Field K], IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K
· 使用定理 `AddSubgroup.IsFiniteRelIndex.relIndex_ne_zero`：∀ {G : Type u_3} {inst : 
AddGroup G} {H K : AddSubgroup G} [self : H.IsFiniteRelIndex K], H.relIndex K ≠ 
0
· 使用引理 `Ideal.isFiniteRelIndex`：isFiniteRelIndex {I : Ideal S} (hI : I != ⊥) (J 
: Ideal S) : I.toAddSubgroup.IsFiniteRelIndex J.toAddSubgroup
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `NumberField.RingOfIntegers.instCharZero_1`：∀ (K : Type u_1) [inst : Fiel
d K] [CharZero K], CharZero (NumberField.RingOfIntegers K)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddSubgroup.nsmul_relIndex_mem`：∀ {G : Type u_6} [inst : AddGroup G] (H 
: AddSubgroup G) [H.Normal] {K : AddSubgroup G} {g : G},   g ∈ K → H.relIndex K 
• g ∈ H
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `Submodule.mem_span_of_mem`：mem_span_of_mem {s : Set M} {x : M} (hx : x i
n s) : x in span R s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
（共 63 条，此处仅展示前 30 条）
-/
lemma exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, n * x = a ∧
      (span {(n : 𝓞 K), a}).absNorm = n ^ (Module.finrank ℚ K - 1) := by
  have hx : IsAlgebraic ℤ x := IsFractionRing.isAlgebraic_iff ℤ _ _ |>.mpr (.of_finite ℚ x)
  obtain ⟨m, r, hm, hmr⟩ := hx.exists_nsmul_eq (𝓞 K)
  rw [← RingOfIntegers.coe_eq_algebraMap r] at hmr
  set n := (span {(m : 𝓞 K)}).toAddSubgroup.relIndex (span {(m : 𝓞 K), r}).toAddSubgroup with hndef
  have hn : n ≠ 0 := isFiniteRelIndex (by simp [hm]) _ |>.relIndex_ne_zero
  obtain ⟨a, ha'⟩ : ∃ a, m * a = n * r := by
    have : n • r ∈ span {(m : 𝓞 K)} :=
      (span {(m : 𝓞 K)}).toAddSubgroup.nsmul_relIndex_mem <| Submodule.mem_span_of_mem <| by grind
    simpa [mem_span_singleton', mul_comm] using this
  have ha : n * x = a := by
    refine mul_left_cancel₀ (mod_cast hm : (m : K) ≠ 0) ?_
    rw [mul_left_comm, ← nsmul_eq_mul m, hmr]
    exact_mod_cast ha'.symm
  refine ⟨n, hn, a, ha, mul_left_cancel₀ hn ?_⟩
  nth_rewrite 1 [hndef]
  rw [absNorm_eq_index, mul_pow_sub_one finrank_pos.ne', ← RingOfIntegers.rank,
    ← absNorm_span_natCast, absNorm_eq_index, ← relIndex_span_span_eq_relIndex_span_span hn hm ha']
  exact relIndex_mul_index <| Submodule.toAddSubgroup_mono <| span_mono <| by grind

open Height in
/-
**NumberField.one_le_pow_totalWeight_mul_finprod** 是 Mathlib 中的一个引理，位于命名空间 `Numb
erField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma one_le_pow_totalWeight_mul_finprod {n : ℕ} (hn : n ≠ 0) (a : 𝓞 K) :
    1 ≤ (n ^ totalWeight K : ℝ) * ∏ᶠ (v : FinitePlace K), ⨆ i, v (![↑a, ↑n] i) := by
  have Hw : (0 : ℝ) < n ^ totalWeight K := by positivity
  rw_mod_cast [totalWeight_eq_finrank, ← RingOfIntegers.rank, ← absNorm_span_natCast] at Hw ⊢
  rw [← absNorm_mul_finprod_finitePlace_eq_one (show ![a, n] ≠ 0 by simp [hn])]
  gcongr
  · exact finprod_nonneg fun _ ↦ Real.iSup_nonneg_of_nonnegHomClass ..
  · exact Nat.le_of_dvd Hw <| absNorm_dvd_absNorm_of_le <| span_mono <| by simp
  · apply le_of_eq; congr; ext; congr; ext i; fin_cases i <;> simp

end withIdeal

open Height

section withFinset

open Finset

/-- If `x : K` (for a number field `K`), then we can find a nonzero `n : ℕ` such that
`n ≤ mulHeight₁ x` and `n * x` is integral. I.e., the denominator of `x` can be bounded by
its multplicative height. -/
-- TODO: Use this to show `natDenominator x ≤ mulHeight₁ x` once #39872 is merged.
/-
**NumberField.exists_nat_le_mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exists_nat_le_mulHeight₁ (x : K) :
    ∃ n : ℕ, n ≠ 0 ∧ n ≤ mulHeight₁ x ∧ IsIntegral ℤ (n * x) := by
  obtain ⟨n, hn, a, ha₁, ha₂⟩ := exists_nat_ne_zero_exists_integer_mul_eq_and_absNorm_span_eq_pow x
  refine ⟨n, hn, ?_, ha₁ ▸ a.isIntegral_coe⟩
  rw [← totalWeight_eq_finrank] at ha₂
  have hv (i : Fin 2) : (![a, n] i : K) = ![(a : K), n] i := by fin_cases i <;> rfl
  rw [← mul_div_cancel_left₀ x (mod_cast hn : (n : K) ≠ 0), ha₁, mulHeight₁_div_eq_mulHeight,
    mulHeight_eq (by simp [hn])]
  refine le_of_mul_le_mul_left ?_ (show (0 : ℝ) < n ^ (totalWeight K - 1) by positivity)
  have : n ^ (totalWeight K - 1) * ∏ᶠ (v : FinitePlace K), ⨆ i, v (![(a : K), n] i) = 1 := by
    simpa [ha₂, hv] using absNorm_mul_finprod_finitePlace_eq_one (show ![a, n] ≠ 0 by simp [hn])
  rw [pow_sub_one_mul (totalWeight_pos K).ne', mul_left_comm, this, mul_one,
    totalWeight_eq_sum_mult, ← prod_pow_eq_pow_sum univ]
  gcongr
  exact Finite.le_ciSup_of_le 1 <| by simp
/-
**NumberField.pow_totalWeight_sub_one_eq** 是 Mathlib 中的一个引理，位于命名空间 `NumberField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma pow_totalWeight_sub_one_eq [DecidableEq (InfinitePlace K)] {n : ℕ} (hn : n ≠ 0)
    (v : InfinitePlace K) :
    (n ^ (totalWeight K - 1) : ℝ) = (∏ w ∈ univ.erase v, (n ^ w.mult : ℝ)) * n ^ (v.mult - 1) := by
  refine mul_right_cancel₀ (b := (n : ℝ)) (mod_cast hn) ?_
  rw [pow_sub_one_mul (totalWeight_pos K).ne', totalWeight_eq_sum_mult, ← prod_pow_eq_pow_sum,
    ← prod_erase_mul _ _ (mem_univ v), ← pow_sub_one_mul v.mult_ne_zero, ← mul_assoc]
/-
**NumberField.infinitePlace_apply_le_of_prod_le** 是 Mathlib 中的一个引理，位于命名空间 `Numbe
rField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma infinitePlace_apply_le_of_prod_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) {x : 𝓞 K}
    (h : ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult ≤ B) (v : InfinitePlace K) :
    v x ≤ B / n ^ (totalWeight K - 1) := by
  classical
  rw [le_div_iff₀' (by positivity)]
  calc
    _ ≤ n ^ (totalWeight K - 1) * ⨆ i, v (![(x : K), n] i) := by
      gcongr; exact Finite.le_ciSup_of_le 0 le_rfl
    _ ≤ (∏ v' ∈ univ.erase v, (⨆ i, v' (![↑x, ↑n] i)) ^ v'.mult) *
         (⨆ i, v (![↑x, ↑n] i)) ^ (v.mult - 1) * ⨆ i, v (![(x : K), n] i) := by
      rw [pow_totalWeight_sub_one_eq hn]
      gcongr
      · exact Real.iSup_nonneg_of_nonnegHomClass ..
      · exact prod_nonneg fun _ _ ↦ pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _
      all_goals exact Finite.le_ciSup_of_le 1 <| by simp
    _ ≤ B := by
      rwa [mul_assoc, pow_sub_one_mul v.mult_ne_zero, prod_erase_mul _ _ (mem_univ v)]

end withFinset

/-
**NumberField.finite_setOfPred_prod_infinitePlace_iSup_le** 是 Mathlib 中的一个引理，位于命
名空间 `NumberField`。
形式化陈述：finite_setOfPred_prod_infinitePlace_iSup_le {n : Nat} (hn : n != 0) (B : R
eal) : {x : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult <= 
B}.Finite
参数：hn : n != 0；B : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mk`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β} {f
 : α → β},   Set.MapsTo f s t → Set.InjOn f s → Set.SurjOn f s t → Set.BijOn f s
 t
· 使用定理 `NumberField.RingOfIntegers.isIntegral_coe`：isIntegral_coe (x : 𝓞 K) : Is
Integral Int (algebraMap _ K x)
· 使用定理 `NumberField.RingOfIntegers.ext`：∀ {K : Type u_1} [inst : Field K] {x y :
 NumberField.RingOfIntegers K}, ↑x = ↑y → x = y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_integralClosure_iff`：mem_integralClosure_iff {a : A} : a in integral
Closure R A ↔ IsIntegral R a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `NumberField.InfinitePlace.norm_embedding_eq`：norm_embedding_eq (w : Infi
nitePlace K) (x : K) : ‖(embedding w) x‖ = w x
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.BijOn.finite_iff_finite`：∀ {α : Type u} {β : Type v} {f : α → β} {s 
: Set α} {t : Set β}, Set.BijOn f s t → (s.Finite ↔ t.Finite)
· 使用定理 `NumberField.Embeddings.finite_of_norm_le`：finite_of_norm_le (B : Real) :
 {x : K | IsIntegral Int x ∧ forall φ : K ->+* A, ‖φ x‖ <= B}.Finite
-/
lemma finite_setOfPred_prod_infinitePlace_iSup_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : 𝓞 K | ∏ v : InfinitePlace K, (⨆ i, v (![(x : K), n] i)) ^ v.mult ≤ B}.Finite := by
  set B' := B / n ^ (totalWeight K - 1)
  suffices Set.BijOn ((↑) : 𝓞 K → K) {x | ∀ (v : InfinitePlace K), v x ≤ B'}
      {x | IsIntegral ℤ x ∧ ∀ (φ : K →+* ℂ), ‖φ x‖ ≤ B'} from
    this.finite_iff_finite.mpr (Embeddings.finite_of_norm_le K ℂ B') |>.subset
      fun _ _ ↦ by grind [infinitePlace_apply_le_of_prod_le hn B]
  refine .mk (fun x hx ↦ ?_) (fun _ _ _ _ ↦ RingOfIntegers.ext) fun a ha ↦ ?_ <;>
    simp only [Set.mem_image, Set.mem_ofPred_eq] at *
  · exact ⟨x.isIntegral_coe, fun φ ↦ hx <| .mk φ⟩
  · rw [← mem_integralClosure_iff ℤ K] at ha
    exact ⟨⟨a, ha.1⟩, fun v ↦ v.norm_embedding_eq a ▸ ha.2 v.embedding, rfl⟩

@[deprecated (since := "2026-07-09")]
alias finite_setOf_prod_infinitePlace_iSup_le := finite_setOfPred_prod_infinitePlace_iSup_le

/-- The set of `a : 𝓞 K` such that `mulHeight₁ (a / n) = mulHeight ![a, n]` is bounded
(for some given nonzero `n : ℕ`) is finite. -/
/-
**NumberField.finite_setOfPred_mulHeight_nat_le** 是 Mathlib 中的一个引理，位于命名空间 `Numbe
rField`。
形式化陈述：finite_setOfPred_mulHeight_nat_le {n : Nat} (hn : n != 0) (B : Real) : {a 
: 𝓞 K | mulHeight ![(a : K), n] <= B}.Finite
参数：hn : n != 0；B : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ofPred_subset_ofPred_of_imp`：∀ {α : Type u} {p q : α → Prop}, (∀ (a 
: α), p a → q a) → {a | p a} ⊆ {a | q a}
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `NumberField.mulHeight_eq`：mulHeight_eq {ι : Type*} {x : ι -> K} (hx : x 
!= 0) : mulHeight x = (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : 
FinitePlace K,…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NumberField.RingOfIntegers.instIsTorsionFree_2`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   Module.IsT
orsionFree (NumberField.RingOfIntege…
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The set of `a : 𝓞 K` such that `mulHeight₁ (a / n) = mulHeight ![a, n]` is bound
ed
(for some given nonzero `n : ℕ`) is finite.
-/
lemma finite_setOfPred_mulHeight_nat_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B}.Finite := by
  suffices {a : 𝓞 K | mulHeight ![(a : K), n] ≤ B} ⊆
      {a | ∏ v : InfinitePlace K, (⨆ i, v (![(a : K), n] i)) ^ v.mult ≤ n ^ totalWeight K * B} from
    (finite_setOfPred_prod_infinitePlace_iSup_le hn _).subset this
  refine Set.ofPred_subset_ofPred_of_imp fun a ha ↦ ?_
  rw [mulHeight_eq <| by simp [hn], mul_comm] at ha
  grw [← ha, ← mul_assoc, ← one_le_pow_totalWeight_mul_finprod hn, one_mul]
  -- nonnegativity side goal
  exact Finset.prod_nonneg fun _ _ ↦ pow_nonneg (Real.iSup_nonneg_of_nonnegHomClass ..) _

@[deprecated (since := "2026-07-09")]
alias finite_setOf_mulHeight_nat_le := finite_setOfPred_mulHeight_nat_le

variable (K) in
/- The set of `x : K` such that `mulHeight₁ x` is bounded and `n * x` is integral
(for some given nonzero `n : ℕ`) is finite.
This is a stepping stone for the proof of the next result, which is strictly stronger. -/
/-
**NumberField.finite_setOfPred_isIntegral_nat_mul_and_mulHeight** 是 Mathlib 中的一个
引理，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of `x : K` such that `mulHeight₁ x` is bounded and `n * x` is integral
(for some given nonzero `n : ℕ`) is finite.
This is a stepping stone for the proof of the next result, which is strictly str
onger.
-/
private lemma finite_setOfPred_isIntegral_nat_mul_and_mulHeight₁_le {n : ℕ} (hn : n ≠ 0) (B : ℝ) :
    {x : K | IsIntegral ℤ (n * x) ∧ mulHeight₁ x ≤ B}.Finite := by
  have hn' : (n : K) ≠ 0 := mod_cast hn
  suffices Set.BijOn (fun a : 𝓞 K ↦ (a / n : K)) {a | mulHeight ![(a : K), n] ≤ B}
      {x | IsIntegral ℤ (n * x) ∧ mulHeight₁ x ≤ B} from
    this.finite_iff_finite.mp <| finite_setOfPred_mulHeight_nat_le hn B
  refine .mk (fun a ha ↦ ?_) (fun a _ b _ h ↦ ?_) fun x ⟨hx₁, hx₂⟩ ↦ ?_
  · simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [mul_div_cancel₀ (a : K) hn', mulHeight₁_div_eq_mulHeight]
    exact ⟨a.isIntegral_coe, ha⟩
  · rwa [div_left_inj' hn', RingOfIntegers.eq_iff] at h
  · simp only [Set.mem_ofPred_eq, Set.mem_image]
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 K, n * x = a := ⟨⟨_, hx₁⟩, rfl⟩
    refine ⟨a, ?_, (EuclideanDomain.eq_div_of_mul_eq_right hn' ha).symm⟩
    rwa [← ha, ← mulHeight₁_div_eq_mulHeight, mul_div_cancel_left₀ x hn']

variable (K) in
/-- A number field `K` satisfies the **Northcott property**:
The set of elements of bounded multiplicative height is finite. -/
/-
**NumberField.finite_setOfPred_mulHeight** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A number field `K` satisfies the **Northcott property**:
The set of elements of bounded multiplicative height is finite.
-/
theorem finite_setOfPred_mulHeight₁_le (B : ℝ) : {x : K | mulHeight₁ x ≤ B}.Finite := by
  have H : {x : K | mulHeight₁ x ≤ B} =
      ⋃ n : Fin ⌊B⌋₊, {x : K | IsIntegral ℤ ((n + 1) * x) ∧ mulHeight₁ x ≤ B} := by
    ext x : 1
    obtain ⟨n, hn₀, hn₁, hn⟩ := exists_nat_le_mulHeight₁ x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_and_right, iff_and_self]
    refine fun h ↦ ⟨⟨n - 1, by grind [Nat.le_floor <| hn₁.trans h]⟩, ?_⟩
    rwa [← Nat.cast_add_one, Nat.sub_one_add_one hn₀]
  rw [H]
  exact Set.finite_iUnion fun n ↦
    mod_cast finite_setOfPred_isIntegral_nat_mul_and_mulHeight₁_le K (Nat.zero_ne_add_one n).symm B

@[deprecated (since := "2026-07-09")]
alias finite_setOf_mulHeight₁_le := finite_setOfPred_mulHeight₁_le
/-
**NumberField.** 是 Mathlib 中的一个实例，位于命名空间 `NumberField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Northcott (mulHeight₁ (K := K)) where
  finite_le := finite_setOfPred_mulHeight₁_le K

variable (K) in
/-- A number field `K` satisfies the **Northcott property**:
The set of elements of bounded logarithmic height is finite. -/
/-
**NumberField.finite_setOfPred_logHeight** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A number field `K` satisfies the **Northcott property**:
The set of elements of bounded logarithmic height is finite.
-/
theorem finite_setOfPred_logHeight₁_le (B : ℝ) :
    {x : K | logHeight₁ x ≤ B}.Finite :=
  Northcott.finite_le B

@[deprecated (since := "2026-07-09")]
alias finite_setOf_logHeight₁_le := finite_setOfPred_logHeight₁_le

end NumberField

end Northcott

/-!
### Positivity extension for totalWeight on number fields
-/

namespace Mathlib.Meta.Positivity

open Lean.Meta Qq

/-- Extension for the `positivity` tactic: `Height.totalWeight` is positive for number fields. -/
@[positivity Height.totalWeight _]
meta def evalHeightTotalWeight : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℕ), ~q(@Height.totalWeight $K $KF $KA) =>
    -- Check whether there is a `NumberField` instance for `$K` around.
    match ← trySynthInstanceQ q(NumberField $K) with
    | .some _inst =>
      assertInstancesCommute
      return .positive q(NumberField.totalWeight_pos $K)
    | _ => throwError "field in Height.totalWeight not known to be a number field"
  | _, _, _ => throwError "not Height.totalWeight"

end Mathlib.Meta.Positivity

/-!
### Heights over the rational numbers

We show that the `Height.mulHeight` of a tuple of coprime integers (considered as rational numbers)
equals the maximum of their absolute values and that the `Height.mulHeight₁` of a rational
number is the maximum of the absolute value of the numerator and the denominator.
We add the corresponding results for logarithmic heights.
-/

namespace Rat

open NumberField Height

section tuples

variable {ι : Type*} [Fintype ι] [Nonempty ι] {x : ι → ℤ}

/-- The term corresponding to a finite place in the definition of the multiplicative height
of a tuple of rational numbers equals `1` if the tuple consists of coprime integers. -/
/-
**Rat.iSup_finitePlace_apply_eq_one_of_gcd_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Rat
`。
形式化陈述：iSup_finitePlace_apply_eq_one_of_gcd_eq_one (v : FinitePlace Rat) (hx : Fi
nset.univ.gcd x = 1) : ⨆ i, v (x i) = 1
参数：v : FinitePlace Rat；hx : Finset.univ.gcd x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用引理 `NumberField.FinitePlace.add_le`：add_le (v : FinitePlace K) (x y : K) : v
 (x + y) <= max (v x) (v y)
· 使用定理 `IsNonarchimedean.apply_intCast_le_one`：apply_intCast_le_one [IsStrictOrd
eredRing R] {F α : Type*} [AddGroupWithOne α] [FunLike F α R] [AddGroupSeminormC
lass F α R] [OneHomClass F …
· 使用定理 `MulRingSeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_7} {α : outP
aram (Type u_8)} {β : outParam (Type u_9)} {inst : NonAssocRing α} {inst_1 : Sem
iring β}   {inst_2 : PartialOrder …
· 使用定理 `MulRingNormClass.toMulRingSeminormClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : NonAssocRing α} {inst_1 : Semiring
 β}   {inst_2 : PartialOrder …
· 使用定理 `NumberField.FinitePlace.instMulRingNormClassReal`：∀ {K : Type u_1} [inst
 : Field K] [inst_1 : NumberField K], MulRingNormClass (NumberField.FinitePlace 
K) K ℝ
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `NumberField.FinitePlace.instMonoidWithZeroHomClassReal`：∀ {K : Type u_1}
 [inst : Field K] [inst_1 : NumberField K], MonoidWithZeroHomClass (NumberField.
FinitePlace K) K ℝ
· 使用引理 `Finset.gcd_eq_sum_mul`：Finset.gcd_eq_sum_mul {α : Type*} [CommRing R] [I
sBezout R] [NormalizedGCDMonoid R] (s : Finset α) (f : α -> R) : exists g : α ->
 R, s.gcd f…
· 使用定理 `IsBezout.of_isPrincipalIdealRing`：∀ (R : Type u) [inst : Semiring R] [Is
PrincipalIdealRing R], IsBezout R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用引理 `Int.cast_sum`：cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> 
Int) : ↑(∑ x in s, f x : Int) = ∑ x in s, (f x : R)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsNonarchimedean.apply_sum_univ_le`：apply_sum_univ_le [Fintype α] (hv : 
IsNonarchimedean v) : v (∑ i, l i) <= ⨆ i, v (l i)
· 使用定理 `NumberField.FinitePlace.instNonnegHomClassReal`：∀ {K : Type u_1} [inst :
 Field K] [inst_1 : NumberField K], NonnegHomClass (NumberField.FinitePlace K) K
 ℝ
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `exists_eq_ciSup_of_finite`：exists_eq_ciSup_of_finite [Nonempty ι] [Finit
e ι] {f : ι -> α} : exists i, f i = ⨆ i, f i
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The term corresponding to a finite place in the definition of the multiplicative
 height
of a tuple of rational numbers equals `1` if the tuple consists of coprime integ
ers.
-/
lemma iSup_finitePlace_apply_eq_one_of_gcd_eq_one (v : FinitePlace ℚ) (hx : Finset.univ.gcd x = 1) :
    ⨆ i, v (x i) = 1 := by
  have hv : IsNonarchimedean (v ·) := FinitePlace.add_le v
  have H (n : ℤ) : v n ≤ 1 := IsNonarchimedean.apply_intCast_le_one hv
  obtain ⟨f, hf⟩ := Finset.gcd_eq_sum_mul .univ x
  apply_fun v at hf
  simp_rw [hx, Int.cast_one, map_one, Int.cast_sum, Int.cast_mul] at hf
  replace hf := hf.trans_le hv.apply_sum_univ_le
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i ↦ v (x i * f i))
  rw [← hi, map_mul] at hf
  replace hf : 1 ≤ v (x i) := hf.trans <| mul_le_of_le_one_right (apply_nonneg v _) (H _)
  exact le_antisymm (ciSup_le (H <| x ·)) <| Finite.le_ciSup_of_le i hf

open AdmissibleAbsValues in
/-- The multiplicative height of a tuple of rational numbers that consists of coprime integers
is the maximum of the absolute values of the entries. -/
/-
**Rat.mulHeight_eq_max_abs_of_gcd_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：mulHeight_eq_max_abs_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) : mulHeigh
t (((↑) : Int -> Rat) ∘ x) = ⨆ i, |x i|
参数：hx : Finset.univ.gcd x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_eq_zero_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3
} [inst : Zero β] [inst_1 : Zero γ] (f : α → β) {g : β → γ},   Function.Injectiv
e g → g 0 = 0 →…
· 使用引理 `Rat.intCast_injective`：intCast_injective : Injective (Int.cast : Int -> 
Rat)
· 使用定理 `Rat.intCast_zero`：↑0 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.gcd_eq_zero_iff`：gcd_eq_zero_iff : s.gcd f = 0 ↔ forall x in s, f
 x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用引理 `Finite.map_iSup_of_monotone`：map_iSup_of_monotone (f : ι -> α) {g : α ->
 β} (hg : Monotone g) : g (⨆ i, f i) = ⨆ i, g (f i)
· 使用引理 `Int.cast_mono`：cast_mono : Monotone (Int.cast : Int -> R)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `NumberField.mulHeight_eq`：mulHeight_eq {ι : Type*} {x : ι -> K} (hx : x 
!= 0) : mulHeight x = (∏ v : InfinitePlace K, (⨆ i, v (x i)) ^ v.mult) * ∏ᶠ v : 
FinitePlace K,…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Rat.infinitePlace_apply`：∀ (v : NumberField.InfinitePlace ℚ) (x : ℚ), v 
x = ↑|x|
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Rat.cast_abs`：∀ {K : Type u_5} [inst : Field K] [inst_1 : LinearOrder K]
 [IsStrictOrderedRing K] (q : ℚ), ↑|q| = |↑q|
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The multiplicative height of a tuple of rational numbers that consists of coprim
e integers
is the maximum of the absolute values of the entries.
-/
lemma mulHeight_eq_max_abs_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) :
    mulHeight (((↑) : ℤ → ℚ) ∘ x) = ⨆ i, |x i| := by
  have hx₀ : Int.cast ∘ x ≠ (0 : ι → ℚ) := by
    contrapose! hx
    rw [Function.comp_eq_zero_iff x intCast_injective Rat.intCast_zero] at hx
    rw [hx, Finset.gcd_eq_zero_iff.mpr (by simp)]
    exact zero_ne_one
  simp_rw [Finite.map_iSup_of_monotone _ Int.cast_mono, NumberField.mulHeight_eq hx₀,
    infinitePlace_apply]
  simp [finprod_eq_one_of_forall_eq_one (iSup_finitePlace_apply_eq_one_of_gcd_eq_one · hx)]

open Real in
/-- The logarithmic height of a tuple of rational numbers that consists of coprime integers
is the logarithm of the maximum of the absolute values of the entries. -/
/-
**Rat.logHeight_eq_max_abs_of_gcd_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：logHeight_eq_max_abs_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) : logHeigh
t (((↑) : Int -> Rat) ∘ x) = log ↑(⨆ i, |x i|)
参数：hx : Finset.univ.gcd x = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Height.logHeight_eq_log_mulHeight`：logHeight_eq_log_mulHeight (x : ι -> 
K) : logHeight x = log (mulHeight x)
· 使用引理 `Rat.mulHeight_eq_max_abs_of_gcd_eq_one`：mulHeight_eq_max_abs_of_gcd_eq_o
ne (hx : Finset.univ.gcd x = 1) : mulHeight (((↑) : Int -> Rat) ∘ x) = ⨆ i, |x i
|

--- 原说明 ---
The logarithmic height of a tuple of rational numbers that consists of coprime i
ntegers
is the logarithm of the maximum of the absolute values of the entries.
-/
lemma logHeight_eq_max_abs_of_gcd_eq_one (hx : Finset.univ.gcd x = 1) :
    logHeight (((↑) : ℤ →  ℚ) ∘ x) = log ↑(⨆ i, |x i|) := by
  rw [logHeight_eq_log_mulHeight, mulHeight_eq_max_abs_of_gcd_eq_one hx]

end tuples

section mulHeight₁

/-
**Rat.mulHeight_self_one_eq_mulHeight_num_den** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
形式化陈述：mulHeight_self_one_eq_mulHeight_num_den (q : Rat) : mulHeight ![q, 1] = mu
lHeight ![(q.num : Rat), q.den]
参数：q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Rat.den_nz`：∀ (self : ℚ), self.den ≠ 0
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用引理 `Height.mulHeight_smul_eq_mulHeight`：mulHeight_smul_eq_mulHeight (x : ι -
> K) {c : K} (hc : c != 0) : mulHeight (c • x) = mulHeight x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.smul_cons`：∀ {α : Type u_1} {M : Type u_2} {n : ℕ} [inst : SMul M
 α] (x : M) (y : α) (v : Fin n → α),   x • Matrix.vecCons y v = Matrix.vecCons (
x • y)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Rat.den_mul_eq_num`：∀ (q : ℚ), ↑q.den * q = ↑q.num
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Matrix.smul_empty`：∀ {α : Type u_1} {M : Type u_2} [inst : SMul M α] (x 
: M) (v : Fin 0 → α), x • v = ![]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulHeight_self_one_eq_mulHeight_num_den (q : ℚ) :
    mulHeight ![q, 1] = mulHeight ![(q.num : ℚ), q.den] := by
  have hq₀ : (q.den : ℚ) ≠ 0 := mod_cast q.den_nz
  rw [← mulHeight_smul_eq_mulHeight _ hq₀]
  simp

/-- The multiplicative height of a rational number is the maximum of the absolute value of
its numerator and its denominator. -/
/-
**Rat.mulHeight** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of a rational number is the maximum of the absolute va
lue of
its numerator and its denominator.
-/
lemma mulHeight₁_eq_max (q : ℚ) : mulHeight₁ q = max q.num.natAbs q.den := by
  rw [mulHeight₁_eq_mulHeight, mulHeight_self_one_eq_mulHeight_num_den, ← intCast_natCast q.den]
  have : (.univ : Finset (Fin 2)).gcd ![q.num, q.den] = 1 := by
    simpa [Finset.univ_fin2, Int.normalize_coe_nat, ← Int.coe_gcd q.num q.den] using
      Int.isCoprime_iff_gcd_eq_one.mp <| isCoprime_num_den q
  convert! mulHeight_eq_max_abs_of_gcd_eq_one this
  · ext i; fin_cases i <;> simp
  · rw [← Int.cast_natCast, Int.cast_inj]
    push_cast
    refine le_antisymm (max_le ?_ ?_) <| ciSup_le fun i ↦ ?_
    · exact Finite.le_ciSup_of_le 0 <| by simp
    · exact Finite.le_ciSup_of_le 1 <| by simp
    · fin_cases i <;> simp

open Real in
/-- The logarithmic height of a rational number is the logarithm of the maximum of the absolute
value of its numerator and its denominator. -/
/-
**Rat.logHeight** 是 Mathlib 中的一个引理，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of a rational number is the logarithm of the maximum of t
he absolute
value of its numerator and its denominator.
-/
lemma logHeight₁_eq_log_max (q : ℚ) : logHeight₁ q = log ↑(max q.num.natAbs q.den) := by
  rw [logHeight₁_eq_log_mulHeight₁, mulHeight₁_eq_max]

/-- The multiplicative height of a positive natural number `n` cast to `ℚ` equals `n`. -/
/-
**Rat.mulHeight** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicative height of a positive natural number `n` cast to `ℚ` equals `n
`.
-/
theorem mulHeight₁_natCast (n : ℕ) [NeZero n] :
    mulHeight₁ (n : ℚ) = n := by
  simp [mulHeight₁_eq_max, show 1 ≤ n by grind [NeZero.ne n]]

/-- The logarithmic height of a positive natural number `n` cast to `ℚ` equals `log n`. -/
/-
**Rat.logHeight** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The logarithmic height of a positive natural number `n` cast to `ℚ` equals `log 
n`.
-/
theorem logHeight₁_natCast (n : ℕ) [NeZero n] :
    logHeight₁ (n : ℚ) = Real.log n := by
  simp [logHeight₁_eq_log_mulHeight₁, mulHeight₁_natCast n]

end mulHeight₁

end Rat

end

