/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic

import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# The semivariation of a vector measure

The semivariation of a vector measure is the supremum of the variations of its push-forwards
to `ℝ` through all linear forms of norm at most `1`. The interest of this notion is that, in the
reals, any set has nonnegative or nonpositive measure, so that the variation is realized by
a subset (up to a factor of at most `2`). This property is inherited by the semivariation in
general: one has the inequalities
```
‖μ s‖ₑ ≤ μ.semivariation s ≤ 2 sup_{t ⊆ s} ‖μ t‖ₑ
```

The notion of semivariation can in particular be used to show that any vector measure is bounded:
there exists `C < ∞` such that `‖μ s‖ ≤ C` for all `s`.

## Main results

* `μ.semivariation`: the semivariation of the vector measure `μ`.
* `exists_subset_lt_enorm_apply_of_lt_semivariation`: given `s`, there exists `t ⊆ s` such that
  `μ.semivariation s ≤ 2 ‖μ t‖ₑ` up to an arbitrarily small error.
* `μ.bound`: the semivariation of `univ`, in `ℝ≥0`. It is finite by definition.
* `enorm_apply_le_bound`: the inequality `‖μ s‖ₑ ≤ μ.bound`, uniformly in `s`.

## References

* [J. Diestel and J.J. Uhl, Vector Measures][DiestelUhl1977]

-/

public section

open scoped ENNReal Function Topology NNReal
open Set Filter

namespace MeasureTheory.VectorMeasure

variable {X E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {mX : MeasurableSpace X}
  {μ : VectorMeasure X E} {s t : Set X}

/-- The semivariation of a vector measure, defined as the supremum of the variations
of the images of the vector measures under continuous linear forms of norm at most `1`. -/
/-
**MeasureTheory.VectorMeasure.semivariation** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTh
eory.VectorMeasure`。
形式化陈述：semivariation (μ : VectorMeasure X E) (s : Set X) : Real>=0∞
参数：μ : VectorMeasure X E；s : Set X。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The semivariation of a vector measure, defined as the supremum of the variations
of the images of the vector measures under continuous linear forms of norm at mo
st `1`.
-/
noncomputable def semivariation (μ : VectorMeasure X E) (s : Set X) : ℝ≥0∞ :=
  ⨆ ℓ ∈ {ℓ : StrongDual ℝ E | ‖ℓ‖ₑ ≤ 1}, (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation s
/-
**MeasureTheory.VectorMeasure.semivariation_union_le** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.VectorMeasure`。
形式化陈述：semivariation_union_le : μ.semivariation (s union t) <= μ.semivariation s 
+ μ.semivariation t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
-/
lemma semivariation_union_le :
    μ.semivariation (s ∪ t) ≤ μ.semivariation s + μ.semivariation t := by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_union_le _ _).trans
  gcongr <;> apply le_biSup _ hℓ
/-
**MeasureTheory.VectorMeasure.semivariation_mono** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：semivariation_mono (hst : s subseteq t) : μ.semivariation s <= μ.semivaria
tion t
参数：hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
-/
lemma semivariation_mono (hst : s ⊆ t) : μ.semivariation s ≤ μ.semivariation t := by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  apply (measure_mono hst).trans
  apply le_biSup _ hℓ

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.semivariation_le_variation** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：semivariation_le_variation : μ.semivariation s <= μ.variation s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用引理 `MeasureTheory.VectorMeasure.variation_le_of_forall_enorm_le`：variation_l
e_of_forall_enorm_le {m : Measure X} (h : forall E, MeasurableSet E -> ‖μ E‖ₑ <=
 m E) : μ.variation <= m
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ContinuousLinearMap.le_opENorm`：le_opENorm (f : E ->SL[σ₁₂] F) (x : E) :
 ‖f x‖ₑ <= ‖f‖ₑ * ‖x‖ₑ
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
-/
lemma semivariation_le_variation : μ.semivariation s ≤ μ.variation s := by
  simp only [semivariation, iSup_le_iff]
  intro ℓ hℓ
  suffices (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation ≤ μ.variation from this s
  apply variation_le_of_forall_enorm_le (fun t ht ↦ ?_)
  simp only [mapRange_apply, AddMonoidHom.coe_coe]
  apply le_trans ?_ (enorm_measure_le_variation _ _)
  exact (ContinuousLinearMap.le_opENorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)

set_option backward.isDefEq.respectTransparency.types false in
/-
**MeasureTheory.VectorMeasure.enorm_apply_le_semivariation** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：enorm_apply_le_semivariation : ‖μ s‖ₑ <= μ.semivariation s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_dual_vector''`：exists_dual_vector'' (x : E) : exists g : StrongDu
al 𝕜 E, ‖g‖ <= 1 ∧ g x = ‖x‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.enorm_measure_le_variation`：enorm_measure_le
_variation (μ : VectorMeasure X V) (E : Set X) : ‖μ E‖ₑ <= variation μ E
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma enorm_apply_le_semivariation : ‖μ s‖ₑ ≤ μ.semivariation s := by
  by_cases hs : MeasurableSet s; swap
  · simp [not_measurable, hs]
  obtain ⟨ℓ, ℓ_norm, hℓ⟩ : ∃ ℓ : StrongDual ℝ E, ‖ℓ‖ ≤ 1 ∧ ℓ (μ s) = ‖μ s‖ :=
    exists_dual_vector'' _ _
  have h'ℓ : ℓ ∈ {ℓ : StrongDual ℝ E | ‖ℓ‖ₑ ≤ 1} := by
    simp [enorm_eq_nnnorm, ← NNReal.coe_le_one, ℓ_norm]
  calc ‖μ s‖ₑ
  _ = ‖(μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous) s‖ₑ := by simp [← ofReal_norm, hℓ]
  _ ≤ (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation s := enorm_measure_le_variation _ _
  _ ≤ μ.semivariation s := by apply le_biSup _ h'ℓ
/-
**MeasureTheory.VectorMeasure.enorm_apply_le_semivariation_of_subset** 是 Mathlib
 中的一个引理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：enorm_apply_le_semivariation_of_subset (hst : s subseteq t) : ‖μ s‖ₑ <= μ.
semivariation t
参数：hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.VectorMeasure.enorm_apply_le_semivariation`：enorm_apply_le
_semivariation : ‖μ s‖ₑ <= μ.semivariation s
· 使用引理 `MeasureTheory.VectorMeasure.semivariation_mono`：semivariation_mono (hst 
: s subseteq t) : μ.semivariation s <= μ.semivariation t
-/
lemma enorm_apply_le_semivariation_of_subset (hst : s ⊆ t) :
    ‖μ s‖ₑ ≤ μ.semivariation t :=
  enorm_apply_le_semivariation.trans (semivariation_mono hst)
/-
**MeasureTheory.VectorMeasure.exists_subset_lt_enorm_apply_of_lt_semivariation**
 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：exists_subset_lt_enorm_apply_of_lt_semivariation (hs : MeasurableSet s) {a
 : Real>=0∞} (ha : a < μ.semivariation s) : exists t subseteq s, MeasurableSet t
 ∧ a < 2 * ‖μ t‖ₑ
参数：hs : MeasurableSet s；ha : a < μ.semivariation s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_biSup_iff`：lt_biSup_iff {s : Set β} {f : β -> α} : a < ⨆ i in s, f i 
↔ exists i in s, a < f i
· 使用定理 `MeasureTheory.SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation
`：∀ {X : Type u_1} {mX : MeasurableSpace X} (μ : MeasureTheory.SignedMeasure X) 
{s : Set X},   MeasurableSet s →     ∀ {a : ENNReal}, a < (Mea…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ContinuousLinearMap.le_opENorm`：le_opENorm (f : E ->SL[σ₁₂] F) (x : E) :
 ‖f x‖ₑ <= ‖f‖ₑ * ‖x‖ₑ
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
lemma exists_subset_lt_enorm_apply_of_lt_semivariation (hs : MeasurableSet s)
    {a : ℝ≥0∞} (ha : a < μ.semivariation s) :
    ∃ t ⊆ s, MeasurableSet t ∧ a < 2 * ‖μ t‖ₑ := by
  obtain ⟨ℓ, hℓ, h'ℓ⟩ : ∃ ℓ ∈ {ℓ : StrongDual ℝ E | ‖ℓ‖ₑ ≤ 1},
    a < (μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous).variation s := lt_biSup_iff.1 ha
  obtain ⟨t, ts, t_meas, ht⟩ :
      ∃ t ⊆ s, MeasurableSet t ∧ a < 2 * ‖μ.mapRange (ℓ : E →+ ℝ) ℓ.continuous t‖ₑ :=
    SignedMeasure.exists_subset_lt_enorm_apply_of_lt_variation _ hs h'ℓ
  refine ⟨t, ts, t_meas, ht.trans_le ?_⟩
  gcongr
  exact (ContinuousLinearMap.le_opENorm _ _).trans (mul_le_of_le_one_left (by positivity) hℓ)
/-
**MeasureTheory.VectorMeasure.exists_one_le_enorm_apply_of_semivariation_eq_top*
* 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_one_le_enorm_apply_of_semivariation_eq_top
    (hs : MeasurableSet s) (h's : μ.semivariation s = ∞) :
    ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ.semivariation t = ∞ ∧ 1 ≤ ‖μ (s \ t)‖ₑ := by
  obtain ⟨t, ts, t_meas, ht⟩ : ∃ t ⊆ s, MeasurableSet t ∧ 2 * ‖μ s‖ₑ + 2 < 2 * ‖μ t‖ₑ := by
    apply exists_subset_lt_enorm_apply_of_lt_semivariation hs
    rw [h's]
    finiteness
  have h't : 1 + ‖μ s‖ₑ ≤ ‖μ t‖ₑ := by
    apply (ENNReal.mul_le_mul_iff_right (a := 2) (by simp) (by simp)).1
    rw [mul_add, add_comm, mul_one]
    exact ht.le
  have I : ∞ ≤ μ.semivariation t + μ.semivariation (s \ t) := by
    rw [← h's]
    apply le_trans (semivariation_mono (by simp)) semivariation_union_le
  simp only [top_le_iff, ENNReal.add_eq_top] at I
  rcases I with hI | hI
  · refine ⟨t, t_meas, ts, hI, ?_⟩
    have : 1 + ‖μ s‖ₑ ≤ ‖μ (s \ t)‖ₑ + ‖μ s‖ₑ := by
      apply h't.trans
      have : μ t = μ s - μ (s \ t) := by rw [← of_add_of_sdiff t_meas hs ts]; abel
      rw [this, add_comm]
      exact enorm_sub_le
    rwa [ENNReal.add_le_add_iff_right (by simp)] at this
  · refine ⟨s \ t, hs.diff t_meas, sdiff_subset, hI, ?_⟩
    simp only [_root_.sdiff_sdiff_right_self, ts, inf_of_le_right]
    exact le_trans (by simp) h't
/-
**MeasureTheory.VectorMeasure.semivariation_univ_lt_top** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma semivariation_univ_lt_top : μ.semivariation univ < ∞ := by
  apply Ne.lt_top (fun h ↦ ?_)
  have A (s : Set X) (hs : MeasurableSet s) (h's : μ.semivariation s = ∞) :
      ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ.semivariation t = ∞ ∧ 1 ≤ ‖μ (s \ t)‖ₑ :=
    exists_one_le_enorm_apply_of_semivariation_eq_top hs h's
  choose! t t_meas t_subs t_var ht using A
  let s n := t^[n] univ
  have hs n : MeasurableSet (s n) ∧ μ.semivariation (s n) = ∞ := by
    induction n with
    | zero => simp [s, h]
    | succ n ih =>
      simp only [Function.iterate_succ', Function.comp_apply, s]
      exact ⟨t_meas _ ih.1 ih.2, t_var _ ih.1 ih.2⟩
  let u n := s n \ s (n + 1)
  have hu n : 1 ≤ ‖μ (u n)‖ₑ := by
    simp only [Function.iterate_succ', Function.comp_apply, u, s]
    exact ht _ (hs n).1 (hs n).2
  have s_anti : Antitone s := by
    apply antitone_nat_of_succ_le (fun n ↦ ?_)
    simp only [Function.iterate_succ', Function.comp_apply, s]
    apply t_subs _ (hs n).1 (hs n).2
  have u_disj : Pairwise (Disjoint on u) := by
    apply (pairwise_disjoint_on _).2 (fun m n hmn ↦ ?_)
    have : Disjoint (u m) (s (m + 1)) := by simp [u, disjoint_sdiff_left]
    apply this.mono_right
    simp only [sdiff_le_iff, sup_eq_union, u]
    exact Subset.trans (s_anti (by grind)) subset_union_right
  have : HasSum (fun i => μ (u i)) (μ (⋃ i, u i)) :=
    hasSum_of_disjoint_iUnion (fun n ↦ (hs n).1.diff (hs (n + 1)).1) u_disj
  have : Tendsto (fun x ↦ ‖μ (u x)‖ₑ) atTop (𝓝 0) :=
    tendsto_zero_iff_enorm_tendsto_zero.1 this.summable.tendsto_atTop_zero
  obtain ⟨n, hn⟩ : ∃ n, ‖μ (u n)‖ₑ < 1 := ((tendsto_order.1 this).2 _ zero_lt_one).exists
  order [hu n]

variable (μ) in
/-- A constant bounding the norm of `μ s` for any set `s`. -/
/-
**MeasureTheory.VectorMeasure.bound** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Vec
torMeasure`。
形式化陈述：{X : Type u_1} →   {E : Type u_2} →     [inst : NormedAddCommGroup E] →   
    [NormedSpace ℝ E] → {mX : MeasurableSpace X} → MeasureTheory.VectorMeasure X
 E → NNReal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A constant bounding the norm of `μ s` for any set `s`.
-/
protected noncomputable def bound : ℝ≥0 := (μ.semivariation univ).toNNReal
/-
**MeasureTheory.VectorMeasure.semivariation_apply_le_bound** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：semivariation_apply_le_bound : μ.semivariation s <= μ.bound
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `MeasureTheory.VectorMeasure.semivariation_mono`：semivariation_mono (hst 
: s subseteq t) : μ.semivariation s <= μ.semivariation t
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Variation.Semivariation.0.M
easureTheory.VectorMeasure.semivariation_univ_lt_top`：∀ {X : Type u_1} {E : Type
 u_2} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] {mX : MeasurableS
pace X}   {μ : MeasureTheory.Vecto…
-/
lemma semivariation_apply_le_bound : μ.semivariation s ≤ μ.bound := by
  apply (semivariation_mono (subset_univ _)).trans_eq
  simp only [VectorMeasure.bound]
  rw [ENNReal.coe_toNNReal semivariation_univ_lt_top.ne]
/-
**MeasureTheory.VectorMeasure.enorm_apply_le_bound** 是 Mathlib 中的一个引理，位于命名空间 `Me
asureTheory.VectorMeasure`。
形式化陈述：enorm_apply_le_bound : ‖μ s‖ₑ <= μ.bound
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `MeasureTheory.VectorMeasure.enorm_apply_le_semivariation`：enorm_apply_le
_semivariation : ‖μ s‖ₑ <= μ.semivariation s
· 使用引理 `MeasureTheory.VectorMeasure.semivariation_apply_le_bound`：semivariation_
apply_le_bound : μ.semivariation s <= μ.bound
-/
lemma enorm_apply_le_bound : ‖μ s‖ₑ ≤ μ.bound :=
  (enorm_apply_le_semivariation).trans semivariation_apply_le_bound
/-
**MeasureTheory.VectorMeasure.nnnorm_apply_le_bound** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：nnnorm_apply_le_bound : ‖μ s‖₊ <= μ.bound
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用引理 `enorm_eq_nnnorm`：enorm_eq_nnnorm (x : E) : ‖x‖ₑ = ‖x‖₊
· 使用引理 `MeasureTheory.VectorMeasure.enorm_apply_le_bound`：enorm_apply_le_bound :
 ‖μ s‖ₑ <= μ.bound
-/
lemma nnnorm_apply_le_bound : ‖μ s‖₊ ≤ μ.bound := by
  rw [← ENNReal.coe_le_coe, ← enorm_eq_nnnorm]
  exact enorm_apply_le_bound
/-
**MeasureTheory.VectorMeasure.norm_apply_le_bound** 是 Mathlib 中的一个引理，位于命名空间 `Mea
sureTheory.VectorMeasure`。
形式化陈述：norm_apply_le_bound : ‖μ s‖ <= μ.bound
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.VectorMeasure.nnnorm_apply_le_bound`：nnnorm_apply_le_bound
 : ‖μ s‖₊ <= μ.bound
-/
lemma norm_apply_le_bound : ‖μ s‖ ≤ μ.bound := by
  simpa [← coe_nnnorm] using nnnorm_apply_le_bound

end MeasureTheory.VectorMeasure

