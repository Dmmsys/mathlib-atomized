/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Louis (Yiyang) Liu
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral average over an interval

In this file we introduce notation `⨍ x in a..b, f x` for the average `⨍ x in Ι a b, f x` of `f`
over the interval `Ι a b = Set.Ioc (min a b) (max a b)` w.r.t. the Lebesgue measure, then prove
formulas for this average:

* `interval_average_eq`: `⨍ x in a..b, f x = (b - a)⁻¹ • ∫ x in a..b, f x`;
* `interval_average_eq_div`: `⨍ x in a..b, f x = (∫ x in a..b, f x) / (b - a)`;
* `exists_eq_interval_average_of_measure`:
    `∃ c ∈ Ι a b, f c = ⨍ x in Ι a b, f x ∂μ`.
* `exists_eq_interval_average_of_nullSingletonClass`:
    `∃ c ∈ uIoo a b, f c = ⨍ x in Ι a b, f x ∂μ`.
* `exists_eq_interval_average`:
    `∃ c ∈ uIoo a b, f c = ⨍ x in a..b, f x`.

We also prove that `⨍ x in a..b, f x = ⨍ x in b..a, f x`, see `interval_average_symm`.

## Notation

`⨍ x in a..b, f x`: average of `f` over the interval `Ι a b` w.r.t. the Lebesgue measure.

-/

public section


open MeasureTheory Set intervalIntegral

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `⨍ x in a..b, f x` is the average of `f` over the interval `Ι a b` w.r.t. the Lebesgue
measure. -/
notation3 "⨍ "(...)" in "a".."b",
  "r:60:(scoped f => average (Measure.restrict volume (uIoc a b)) f) => r

/-
**interval_average_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interval_average_symm (f : Real -> E) (a b : Real) : (⨍ x in a..b, f x) = 
⨍ x in b..a, f x
参数：f : Real -> E；a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setAverage_eq`：setAverage_eq (f : α -> E) (s : Set α) : ⨍ 
x in s, f x ∂μ = (μ.real s)⁻¹ • ∫ x in s, f x ∂μ
· 使用引理 `Set.uIoc_comm`：uIoc_comm (a b : α) : Ι a b = Ι b a
-/
theorem interval_average_symm (f : ℝ → E) (a b : ℝ) : (⨍ x in a..b, f x) = ⨍ x in b..a, f x := by
  rw [setAverage_eq, setAverage_eq, uIoc_comm]
/-
**interval_average_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interval_average_eq (f : Real -> E) (a b : Real) : (⨍ x in a..b, f x) = (b
 - a)⁻¹ • ∫ x in a..b, f x
参数：f : Real -> E；a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setAverage_eq`：setAverage_eq (f : α -> E) (s : Set α) : ⨍ 
x in s, f x ∂μ = (μ.real s)⁻¹ • ∫ x in s, f x ∂μ
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `Real.volume_real_Ioc_of_le`：volume_real_Ioc_of_le {a b : Real} (hab : a 
<= b) : volume.real (Ioc a b) = b - a
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `Set.uIoc_of_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a
 → Set.uIoc a b = Set.Ioc b a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `intervalIntegral.integral_of_ge`：integral_of_ge (h : b <= a) : ∫ x in a.
.b, f x ∂μ = -∫ x in Ioc b a, f x ∂μ
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem interval_average_eq (f : ℝ → E) (a b : ℝ) :
    (⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x := by
  rcases le_or_gt a b with h | h
  · rw [setAverage_eq, uIoc_of_le h, Real.volume_real_Ioc_of_le h, integral_of_le h]
  · rw [setAverage_eq, uIoc_of_ge h.le, Real.volume_real_Ioc_of_le h.le, integral_of_ge h.le,
      smul_neg, ← neg_smul, ← inv_neg, neg_sub]
/-
**interval_average_eq_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interval_average_eq_div (f : Real -> Real) (a b : Real) : (⨍ x in a..b, f 
x) = (∫ x in a..b, f x) / (b - a)
参数：f : Real -> Real；a b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interval_average_eq`：interval_average_eq (f : Real -> E) (a b : Real) : 
(⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
-/
theorem interval_average_eq_div (f : ℝ → ℝ) (a b : ℝ) :
    (⨍ x in a..b, f x) = (∫ x in a..b, f x) / (b - a) := by
  rw [interval_average_eq, smul_eq_mul, div_eq_inv_mul]

/-- Interval averages are invariant when functions change along discrete sets. -/
/-
**intervalAverage_congr_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：intervalAverage_congr_codiscreteWithin {a b : Real} {f₁ f₂ : Real -> Real}
 (hf : f₁ =ᶠ[Filter.codiscreteWithin (Ι a b)] f₂) : ⨍ (x : Real) in a..b, f₁ x =
 ⨍ (x : Real) in a..b, f₂ x
参数：hf : f₁ =ᶠ[Filter.codiscreteWithin (Ι a b)] f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interval_average_eq`：interval_average_eq (f : Real -> E) (a b : Real) : 
(⨍ x in a..b, f x) = (b - a)⁻¹ • ∫ x in a..b, f x
· 使用定理 `intervalIntegral.integral_congr_codiscreteWithin`：integral_congr_codiscr
eteWithin {a b : Real} {f₁ f₂ : Real -> Real} (hf : f₁ =ᶠ[codiscreteWithin (Ι a 
b)] f₂) : ∫ (x : Real) in a..b, f₁ x =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Interval averages are invariant when functions change along discrete sets.
-/
theorem intervalAverage_congr_codiscreteWithin {a b : ℝ} {f₁ f₂ : ℝ → ℝ}
    (hf : f₁ =ᶠ[Filter.codiscreteWithin (Ι a b)] f₂) :
    ⨍ (x : ℝ) in a..b, f₁ x = ⨍ (x : ℝ) in a..b, f₂ x := by
  rw [interval_average_eq, integral_congr_codiscreteWithin hf, ← interval_average_eq]

variable {f : ℝ → ℝ} {a b : ℝ} {μ : Measure ℝ}

/-- If `f : ℝ → ℝ` is continuous on `uIcc a b`, the interval has finite and nonzero `μ`-measure,
then `∃ c ∈ Ι a b, f c = ⨍ x in Ι a b, f x ∂μ`. -/
/-
**exists_eq_interval_average_of_measure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_interval_average_of_measure (hf : ContinuousOn f (uIcc a b)) (hμ
fin : μ (Ι a b) != ⊤) (hμ0 : μ (Ι a b) != 0) : exists c in Ι a b, f c = ⨍ x in Ι
 a b, f x ∂μ
参数：hf : ContinuousOn f (uIcc a b)；hμfin : μ (Ι a b) != ⊤；hμ0 : μ (Ι a b) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.exists_eq_setAverage`：exists_eq_setAverage [TopologicalSpa
ce α] {f : α -> Real} (hs : IsConnected s) (hf : ContinuousOn f s) (hint : Integ
rableOn f s μ) (hμfin : …
· 使用定理 `MeasureTheory.nonempty_of_measure_ne_zero`：nonempty_of_measure_ne_zero (
h : μ s != 0) : s.Nonempty
· 使用定理 `isPreconnected_Ioc`：isPreconnected_Ioc : IsPreconnected (Ioc a b)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `Set.uIoc_subset_uIcc`：uIoc_subset_uIcc : Ι a b subseteq uIcc a b
· 使用定理 `ContinuousOn.integrableOn_of_subset_isCompact`：ContinuousOn.integrableOn
_of_subset_isCompact (hf : ContinuousOn f K) (hK : IsCompact K) (hs : Measurable
Set s) (h's : s subseteq K) (mus : …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `measurableSet_uIoc`：measurableSet_uIoc [ClosedIicTopology α] : Measurabl
eSet (uIoc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
If `f : ℝ → ℝ` is continuous on `uIcc a b`, the interval has finite and nonzero 
`μ`-measure,
then `∃ c ∈ Ι a b, f c = ⨍ x in Ι a b, f x ∂μ`.
-/
theorem exists_eq_interval_average_of_measure
    (hf : ContinuousOn f (uIcc a b)) (hμfin : μ (Ι a b) ≠ ⊤) (hμ0 : μ (Ι a b) ≠ 0) :
    ∃ c ∈ Ι a b, f c = ⨍ x in Ι a b, f x ∂μ :=
  exists_eq_setAverage ⟨nonempty_of_measure_ne_zero hμ0, isPreconnected_Ioc⟩
    (hf.mono uIoc_subset_uIcc) (hf.integrableOn_of_subset_isCompact
    isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc hμfin) hμfin hμ0

/-- If `f : ℝ → ℝ` is continuous on `uIcc a b`, the interval has finite and nonzero `μ`-measure,
and `μ` has value zero on singletons, then `∃ c ∈ uIoo a b, f c = ⨍ x in Ι a b, f x ∂μ`. -/
/-
**exists_eq_interval_average_of_nullSingletonClass** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_interval_average_of_nullSingletonClass [NullSingletonClass μ] (h
f : ContinuousOn f (uIcc a b)) (hμfin : μ (Ι a b) != ⊤) (hμ0 : μ (Ι a b) != 0) :
 exists c in uIoo a b, f c = ⨍ x in Ι a b, f x ∂μ
参数：hf : ContinuousOn f (uIcc a b)；hμfin : μ (Ι a b) != ⊤；hμ0 : μ (Ι a b) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.integrableOn_of_subset_isCompact`：ContinuousOn.integrableOn
_of_subset_isCompact (hf : ContinuousOn f K) (hK : IsCompact K) (hs : Measurable
Set s) (h's : s subseteq K) (mus : …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isCompact_uIcc`：isCompact_uIcc {α : Type*} [LinearOrder α] [TopologicalS
pace α] [CompactIccSpace α] {a b : α} : IsCompact (uIcc a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `measurableSet_uIoc`：measurableSet_uIoc [ClosedIicTopology α] : Measurabl
eSet (uIoc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `Set.uIoc_subset_uIcc`：uIoc_subset_uIcc : Ι a b subseteq uIcc a b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.uIoc_of_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b
 → Set.uIoc a b = Set.Ioc a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Ioc_eq_empty`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, ¬b < a
 → Set.Ioc b a = ∅
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc`：Ioo_ae_eq_Ioc : Ioo a b =ᵐ[μ] Ioc a b
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.exists_eq_setAverage`：exists_eq_setAverage [TopologicalSpa
ce α] {f : α -> Real} (hs : IsConnected s) (hf : ContinuousOn f s) (hint : Integ
rableOn f s μ) (hμfin : …
· 使用定理 `isConnected_uIoo`：isConnected_uIoo (h : a != b) : IsConnected (uIoo a b)
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `f : ℝ → ℝ` is continuous on `uIcc a b`, the interval has finite and nonzero 
`μ`-measure,
and `μ` has value zero on singletons, then `∃ c ∈ uIoo a b, f c = ⨍ x in Ι a b, 
f x ∂μ`.
-/
theorem exists_eq_interval_average_of_nullSingletonClass
    [NullSingletonClass μ] (hf : ContinuousOn f (uIcc a b)) (hμfin : μ (Ι a b) ≠ ⊤)
    (hμ0 : μ (Ι a b) ≠ 0) : ∃ c ∈ uIoo a b, f c = ⨍ x in Ι a b, f x ∂μ := by
  have hint : IntegrableOn f (Ι a b) μ := hf.integrableOn_of_subset_isCompact
    isCompact_uIcc measurableSet_uIoc uIoc_subset_uIcc hμfin
  have h : a ≠ b := by intro hab; simp [hab] at hμ0
  let s := uIoo a b
  have hs' : s ⊆ Ι a b := by intro x hx; rcases hx with ⟨h1, h2⟩; grind
  have hs_ev : s =ᵐ[μ] Ι a b := by simpa using! Ioo_ae_eq_Ioc
  have hμ0' : μ s ≠ 0 := by
    have hμ : μ s = μ (Ι a b) := by rw [measure_congr hs_ev]
    rwa [hμ]
  obtain ⟨c, hc, heq⟩ := exists_eq_setAverage (isConnected_uIoo h) (hf.mono uIoo_subset_uIcc_self)
    (hint.mono_set hs') (measure_ne_top_of_subset hs' hμfin) hμ0'
  exact ⟨c, hc, by rwa [← setAverage_congr hs_ev]⟩

@[deprecated (since := "2026-06-09")]
alias exists_eq_interval_average_of_noAtoms := exists_eq_interval_average_of_nullSingletonClass

/-- The mean value theorem for integrals:
There exists a point in an interval such that the mean of a continuous function over the interval
equals the value of the function at the point. -/
/-
**exists_eq_interval_average** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_interval_average (hab : a != b) (hf : ContinuousOn f (uIcc a b))
 : exists c in uIoo a b, f c = ⨍ x in a..b, f x
参数：hab : a != b；hf : ContinuousOn f (uIcc a b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_interval_average_of_nullSingletonClass`：exists_eq_interval_ave
rage_of_nullSingletonClass [NullSingletonClass μ] (hf : ContinuousOn f (uIcc a b
)) (hμfin : μ (Ι a b) != ⊤) (hμ0 : μ (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.volume_uIoc`：volume_uIoc {a b : Real} : volume (uIoc a b) = ofReal 
|b - a|
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
The mean value theorem for integrals:
There exists a point in an interval such that the mean of a continuous function 
over the interval
equals the value of the function at the point.
-/
theorem exists_eq_interval_average
    (hab : a ≠ b) (hf : ContinuousOn f (uIcc a b)) :
    ∃ c ∈ uIoo a b, f c = ⨍ x in a..b, f x :=
  exists_eq_interval_average_of_nullSingletonClass hf (by simp)
    (by simpa using sub_ne_zero.mpr hab.symm)
