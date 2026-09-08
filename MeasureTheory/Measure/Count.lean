/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac

import Mathlib.SetTheory.Cardinal.ENNReal

/-!
# Counting measure

In this file we define the counting measure `MeasureTheory.Measure.count`
as `MeasureTheory.Measure.sum MeasureTheory.Measure.dirac`
and prove basic properties of this measure.
-/

@[expose] public section

open Set
open scoped ENNReal Finset

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {s : Set α}

noncomputable section

namespace MeasureTheory.Measure

/-- Counting measure on any measurable space. -/
/-
**MeasureTheory.Measure.count** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：count : Measure α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Counting measure on any measurable space.
-/
def count : Measure α :=
  sum dirac
/-
**MeasureTheory.Measure.count_ne_zero''** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] [Nonempty α], MeasureTheory.Me
asure.count ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma count_ne_zero'' [Nonempty α] : (count : Measure α) ≠ 0 := by simp [count]
/-
**MeasureTheory.Measure.le_count_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：le_count_apply : ∑' _ : s, (1 : Real>=0∞) <= count s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] (s : Set β) (f : β → α),   ∑' (x : ↑s), f ↑x = ∑' (
x …
· 使用定理 `ENNReal.tsum_le_tsum`：∀ {α : Type u_1} {f g : α → ENNReal}, (∀ (a : α), 
f a ≤ g a) → ∑' (a : α), f a ≤ ∑' (a : α), g a
· 使用定理 `MeasureTheory.Measure.le_dirac_apply`：le_dirac_apply {a} : s.indicator 1
 a <= dirac a s
· 使用定理 `MeasureTheory.Measure.le_sum_apply`：le_sum_apply (f : ι -> Measure α) (s
 : Set α) : ∑' i, f i s <= sum f s
-/
theorem le_count_apply : ∑' _ : s, (1 : ℝ≥0∞) ≤ count s :=
  calc
    (∑' _ : s, 1 : ℝ≥0∞) = ∑' i, indicator s 1 i := tsum_subtype s 1
    _ ≤ ∑' i, dirac i s := ENNReal.tsum_le_tsum fun _ => le_dirac_apply
    _ ≤ count s := le_sum_apply _ _
/-
**MeasureTheory.Measure.count_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：count_apply (hs : MeasurableSet s) : count s = s.encard
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用引理 `ENNReal.tsum_one`：tsum_one : ∑' _ : α, (1 : Real>=0∞) = ENat.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_apply (hs : MeasurableSet s) : count s = s.encard := by
  simp [count, hs, ← tsum_subtype]

@[simp]
/-
**MeasureTheory.Measure.count_apply_finset'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：count_apply_finset' {s : Finset α} (hs : MeasurableSet (s : Set α)) : coun
t (↑s : Set α) = #s
参数：hs : MeasurableSet (s : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_apply`：count_apply (hs : MeasurableSet s) : 
count s = s.encard
· 使用定理 `Set.encard_coe_eq_coe_finsetCard`：∀ {α : Type u_1} (s : Finset α), (↑s).
encard = ↑s.card
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_apply_finset' {s : Finset α} (hs : MeasurableSet (s : Set α)) :
    count (↑s : Set α) = #s := by simp [count_apply hs]

@[simp]
/-
**MeasureTheory.Measure.count_apply_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：count_apply_finset [MeasurableSingletonClass α] (s : Finset α) : count (↑s
 : Set α) = #s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.count_apply_finset'`：count_apply_finset' {s : Fins
et α} (hs : MeasurableSet (s : Set α)) : count (↑s : Set α) = #s
· 使用定理 `Finset.measurableSet`：∀ {α : Type u_1} [inst : MeasurableSpace α] [Measu
rableSingletonClass α] (s : Finset α), MeasurableSet ↑s
-/
theorem count_apply_finset [MeasurableSingletonClass α] (s : Finset α) :
    count (↑s : Set α) = #s :=
  count_apply_finset' s.measurableSet
/-
**MeasureTheory.Measure.count_apply_finite'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：count_apply_finite' {s : Set α} (s_fin : s.Finite) (s_mble : MeasurableSet
 s) : count s = #s_fin.toFinset
参数：s_fin : s.Finite；s_mble : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.count_apply_finset'`：count_apply_finset' {s : Fins
et α} (hs : MeasurableSet (s : Set α)) : count (↑s : Set α) = #s
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_apply_finite' {s : Set α} (s_fin : s.Finite) (s_mble : MeasurableSet s) :
    count s = #s_fin.toFinset := by
  simp [←
    @count_apply_finset' _ _ s_fin.toFinset (by simpa only [Finite.coe_toFinset] using s_mble)]
/-
**MeasureTheory.Measure.count_apply_finite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：count_apply_finite [MeasurableSingletonClass α] (s : Set α) (hs : s.Finite
) : count s = #hs.toFinset
参数：s : Set α；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.count_apply_finset`：count_apply_finset [Measurable
SingletonClass α] (s : Finset α) : count (↑s : Set α) = #s
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
-/
theorem count_apply_finite [MeasurableSingletonClass α] (s : Set α) (hs : s.Finite) :
    count s = #hs.toFinset := by rw [← count_apply_finset, Finite.coe_toFinset]

/-- `count` measure evaluates to infinity at infinite sets. -/
/-
**MeasureTheory.Measure.count_apply_infinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：count_apply_infinite (hs : s.Infinite) : count s = ∞
参数：hs : s.Infinite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `le_of_tendsto'`：le_of_tendsto' {x : Filter β} [hx : NeBot x] (lim : Tend
sto f x (𝓝 a)) (h : forall c, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ENNReal.tendsto_nat_nhds_top`：tendsto_nat_nhds_top : Tendsto (fun n : Na
t => ↑n) atTop (𝓝 ∞)
· 使用定理 `Set.Infinite.exists_subset_card_eq`：∀ {α : Type u} {s : Set α}, s.Infini
te → ∀ (n : ℕ), ∃ t, ↑t ⊆ s ∧ t.card = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.tsum_subtype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMono
id α] [inst_1 : TopologicalSpace α] (s : Finset β) (f : β → α),   ∑' (x : ↥s), f
 ↑x = ∑ x…
· 使用定理 `MeasureTheory.Measure.le_count_apply`：le_count_apply : ∑' _ : s, (1 : Re
al>=0∞) <= count s
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
`count` measure evaluates to infinity at infinite sets.
-/
theorem count_apply_infinite (hs : s.Infinite) : count s = ∞ := by
  refine top_unique (le_of_tendsto' ENNReal.tendsto_nat_nhds_top fun n => ?_)
  rcases hs.exists_subset_card_eq n with ⟨t, ht, rfl⟩
  calc
    (#t : ℝ≥0∞) = ∑ i ∈ t, 1 := by simp
    _ = ∑' i : (t : Set α), 1 := (t.tsum_subtype 1).symm
    _ ≤ count (t : Set α) := le_count_apply
    _ ≤ count s := measure_mono ht

@[simp]
/-
**MeasureTheory.Measure.count_apply_eq_top'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：count_apply_eq_top' (s_mble : MeasurableSet s) : count s = ∞ ↔ s.Infinite
参数：s_mble : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.count_apply_finite'`：count_apply_finite' {s : Set 
α} (s_fin : s.Finite) (s_mble : MeasurableSet s) : count s = #s_fin.toFinset
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MeasureTheory.Measure.count_apply_infinite`：count_apply_infinite (hs : s
.Infinite) : count s = ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_apply_eq_top' (s_mble : MeasurableSet s) : count s = ∞ ↔ s.Infinite := by
  by_cases hs : s.Finite
  · simp [Set.Infinite, hs, count_apply_finite' hs s_mble]
  · change s.Infinite at hs
    simp [hs, count_apply_infinite]

@[simp]
/-
**MeasureTheory.Measure.count_apply_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：count_apply_eq_top [MeasurableSingletonClass α] : count s = ∞ ↔ s.Infinite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.count_apply_eq_top'`：count_apply_eq_top' (s_mble :
 MeasurableSet s) : count s = ∞ ↔ s.Infinite
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.count_apply_infinite`：count_apply_infinite (hs : s
.Infinite) : count s = ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem count_apply_eq_top [MeasurableSingletonClass α] : count s = ∞ ↔ s.Infinite := by
  by_cases hs : s.Finite
  · exact count_apply_eq_top' hs.measurableSet
  · change s.Infinite at hs
    simp [hs, count_apply_infinite]

@[simp]
/-
**MeasureTheory.Measure.count_apply_lt_top'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：count_apply_lt_top' (s_mble : MeasurableSet s) : count s < ∞ ↔ s.Finite
参数：s_mble : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.Measure.count_apply_eq_top'`：count_apply_eq_top' (s_mble :
 MeasurableSet s) : count s = ∞ ↔ s.Infinite
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem count_apply_lt_top' (s_mble : MeasurableSet s) : count s < ∞ ↔ s.Finite :=
  calc
    count s < ∞ ↔ count s ≠ ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := not_congr (count_apply_eq_top' s_mble)
    _ ↔ s.Finite := Classical.not_not

@[simp]
/-
**MeasureTheory.Measure.count_apply_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：count_apply_lt_top [MeasurableSingletonClass α] : count s < ∞ ↔ s.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.Measure.count_apply_eq_top`：count_apply_eq_top [Measurable
SingletonClass α] : count s = ∞ ↔ s.Infinite
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem count_apply_lt_top [MeasurableSingletonClass α] : count s < ∞ ↔ s.Finite :=
  calc
    count s < ∞ ↔ count s ≠ ∞ := lt_top_iff_ne_top
    _ ↔ ¬s.Infinite := not_congr count_apply_eq_top
    _ ↔ s.Finite := Classical.not_not

@[simp]
/-
**MeasureTheory.Measure.count_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：count_eq_zero_iff : count s = 0 ↔ s = ∅ where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_of_forall_notMem`：eq_empty_of_forall_notMem (h : forall x, 
x ∉ s) : s = ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.dirac_apply_of_mem`：dirac_apply_of_mem {a : α} (h 
: a in s) : dirac a s = 1
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ENNReal.le_tsum`：∀ {α : Type u_1} {f : α → ENNReal} (a : α), f a ≤ ∑' (a
 : α), f a
· 使用定理 `MeasureTheory.Measure.le_sum_apply`：le_sum_apply (f : ι -> Measure α) (s
 : Set α) : ∑' i, f i s <= sum f s
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem count_eq_zero_iff : count s = 0 ↔ s = ∅ where
  mp h := eq_empty_of_forall_notMem fun x hx ↦ by
    simpa [hx] using ((ENNReal.le_tsum x).trans <| le_sum_apply _ _).trans_eq h
  mpr := by rintro rfl; exact measure_empty
/-
**MeasureTheory.Measure.count_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：count_ne_zero_iff : count s != 0 ↔ s.Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.Measure.count_eq_zero_iff`：count_eq_zero_iff : count s = 0
 ↔ s = ∅ where mp h
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
-/
lemma count_ne_zero_iff : count s ≠ 0 ↔ s.Nonempty :=
  count_eq_zero_iff.not.trans nonempty_iff_ne_empty.symm

alias ⟨_, count_ne_zero⟩ := count_ne_zero_iff

@[simp]
/-
**MeasureTheory.Measure.ae_count_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：ae_count_iff {p : α -> Prop} : (forallᵐ x ∂count, p x) ↔ forall x, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_empty_iff_false`：mem_empty_iff_false (x : α) : x in (∅ : Set α) 
↔ False
· 使用定理 `MeasureTheory.Measure.count_eq_zero_iff`：count_eq_zero_iff : count s = 0
 ↔ s = ∅ where mp h
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
-/
lemma ae_count_iff {p : α → Prop} : (∀ᵐ x ∂count, p x) ↔ ∀ x, p x := by
  refine ⟨fun h x ↦ ?_, ae_of_all _⟩
  rw [ae_iff, count_eq_zero_iff] at h
  by_contra hx
  rwa [← mem_empty_iff_false x, ← h]

@[simp]
/-
**MeasureTheory.Measure.count_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：count_singleton' {a : α} (ha : MeasurableSet ({a} : Set α)) : count ({a} :
 Set α) = 1
参数：ha : MeasurableSet ({a} : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_apply_finite'`：count_apply_finite' {s : Set 
α} (s_fin : s.Finite) (s_mble : MeasurableSet s) : count s = #s_fin.toFinset
· 使用定理 `Set.Finite.toFinset.eq_1`：∀ {α : Type u} {s : Set α} (h : s.Finite), h.t
oFinset = s.toFinset
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.toFinset_singleton`：toFinset_singleton (a : α) [Fintype ({a} : Set α
)] : ({a} : Set α).toFinset = {a}
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_singleton' {a : α} (ha : MeasurableSet ({a} : Set α)) : count ({a} : Set α) = 1 := by
  rw [count_apply_finite' (Set.finite_singleton a) ha, Set.Finite.toFinset]
  simp
/-
**MeasureTheory.Measure.count_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：count_singleton [MeasurableSingletonClass α] (a : α) : count ({a} : Set α)
 = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.count_singleton'`：count_singleton' {a : α} (ha : M
easurableSet ({a} : Set α)) : count ({a} : Set α) = 1
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
-/
theorem count_singleton [MeasurableSingletonClass α] (a : α) : count ({a} : Set α) = 1 :=
  count_singleton' (measurableSet_singleton a)

@[simp]
/-
**MeasureTheory.Measure._root_.MeasureTheory.count_real_singleton'** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.count_real_singleton'
    {a : α} (ha : MeasurableSet ({a} : Set α)) :
    count.real ({a} : Set α) = 1 := by
  rw [measureReal_def, count_singleton' ha, ENNReal.toReal_one]
/-
**MeasureTheory.Measure._root_.MeasureTheory.count_real_singleton** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.count_real_singleton [MeasurableSingletonClass α] (a : α) :
    count.real ({a} : Set α) = 1 :=
  count_real_singleton' (measurableSet_singleton a)
/-
**MeasureTheory.Measure.count_injective_image'** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：count_injective_image' {f : β -> α} (hf : Function.Injective f) {s : Set β
} (s_mble : MeasurableSet s) (fs_mble : MeasurableSet (f '' s)) : count (f '' s)
 = count s
参数：hf : Function.Injective f；s_mble : MeasurableSet s；fs_mble : MeasurableSet (f
 '' s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `MeasureTheory.Measure.count_apply_finset'`：count_apply_finset' {s : Fins
et α} (hs : MeasurableSet (s : Set α)) : count (↑s : Set α) = #s
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `MeasureTheory.Measure.count_apply_infinite`：count_apply_infinite (hs : s
.Infinite) : count s = ∞
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem count_injective_image' {f : β → α} (hf : Function.Injective f) {s : Set β}
    (s_mble : MeasurableSet s) (fs_mble : MeasurableSet (f '' s)) : count (f '' s) = count s := by
  classical
  by_cases hs : s.Finite
  · lift s to Finset β using hs
    rw [← Finset.coe_image, count_apply_finset' _, count_apply_finset' s_mble,
      s.card_image_of_injective hf]
    simpa only [Finset.coe_image] using fs_mble
  · rw [count_apply_infinite hs]
    rw [← finite_image_iff hf.injOn] at hs
    rw [count_apply_infinite hs]
/-
**MeasureTheory.Measure.count_injective_image** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：count_injective_image [MeasurableSingletonClass α] [MeasurableSingletonCla
ss β] {f : β -> α} (hf : Function.Injective f) (s : Set β) : count (f '' s) = co
unt s
参数：hf : Function.Injective f；s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.count_injective_image'`：count_injective_image' {f 
: β -> α} (hf : Function.Injective f) {s : Set β} (s_mble : MeasurableSet s) (fs
_mble : MeasurableSet (f '' s)) : …
· 使用定理 `Set.Finite.measurableSet`：Set.Finite.measurableSet {s : Set α} (hs : s.F
inite) : MeasurableSet s
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_apply_infinite`：count_apply_infinite (hs : s
.Infinite) : count s = ∞
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem count_injective_image [MeasurableSingletonClass α] [MeasurableSingletonClass β] {f : β → α}
    (hf : Function.Injective f) (s : Set β) : count (f '' s) = count s := by
  by_cases hs : s.Finite
  · exact count_injective_image' hf hs.measurableSet (Finite.image f hs).measurableSet
  rw [count_apply_infinite hs]
  rw [← finite_image_iff hf.injOn] at hs
  rw [count_apply_infinite hs]
/-
**MeasureTheory.Measure.count.instSigmaFinite** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.count`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] [MeasurableSingletonClass α] [
Countable α],   MeasureTheory.SigmaFinite MeasureTheory.Measure.count
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_singleton'`：count_singleton' {a : α} (ha : M
easurableSet ({a} : Set α)) : count ({a} : Set α) = 1
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance count.instSigmaFinite [MeasurableSingletonClass α] [Countable α] :
    SigmaFinite (count : Measure α) := by simp [sigmaFinite_iff_measure_singleton_lt_top]
/-
**MeasureTheory.Measure.count.isFiniteMeasure** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure.count`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α] [Finite α], MeasureTheory.IsFi
niteMeasure MeasureTheory.Measure.count
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_apply`：count_apply (hs : MeasurableSet s) : 
count s = s.encard
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
-/
instance count.isFiniteMeasure [Finite α] :
    IsFiniteMeasure (Measure.count : Measure α) :=
  ⟨by simp [Measure.count_apply]⟩

@[simp]
/-
**MeasureTheory.Measure.count_univ** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：count_univ : count (univ : Set α) = ENat.card α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.count_apply`：count_apply (hs : MeasurableSet s) : 
count s = s.encard
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.encard_univ`：∀ (α : Type u_3), Set.univ.encard = ENat.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma count_univ : count (univ : Set α) = ENat.card α := by simp [count_apply .univ, encard_univ]
/-
**MeasureTheory.Measure.count_real_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：∀ {α : Type u_1} [inst : MeasurableSpace α], MeasureTheory.Measure.count.r
eal Set.univ = ↑(Nat.card α)
参数：Nat.card α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.count_univ`：count_univ : count (univ : Set α) = EN
at.card α
· 使用定理 `ENNReal.toReal_enatCard`：∀ (α : Type u_1), (↑(ENat.card α)).toReal = ↑(N
at.card α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma count_real_univ : count.real (.univ : Set α) = Nat.card α := by simp [Measure.real]
/-
**MeasureTheory.Measure.neZero_count** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：neZero_count [Nonempty α] : NeZero (count : Measure α) where out
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.count_univ`：count_univ : count (univ : Set α) = EN
at.card α
-/
instance neZero_count [Nonempty α] : NeZero (count : Measure α) where
  out := by rintro h; simpa using congr($h .univ)
/-
**MeasureTheory.Measure._root_.Subsingleton.count_eq_dirac** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Subsingleton.count_eq_dirac [Subsingleton α] (i : α) :
    count = dirac i := by
  calc count
      = count.restrict univ := by simp
    _ = count.restrict {i} := by congr; ext j; simp [Subsingleton.elim j i]
    _ = dirac i := by simp
/-
**MeasureTheory.Measure._root_.Unique.count_eq_dirac** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Unique.count_eq_dirac [Unique α] : count = dirac (default : α) :=
  Subsingleton.count_eq_dirac _
/-
**MeasureTheory.Measure._root_.Function.Injective.map_count_le** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Function.Injective.map_count_le {f : α → β}
    (hf : f.Injective) (h2f : Measurable f) : count.map f ≤ count := by
  refine le_intro fun s hs _ ↦ ?_
  rw [map_apply h2f hs, count_apply (hs.preimage h2f), count_apply hs, ← hf.encard_image]
  have := image_preimage_subset f s
  gcongr

end Measure

end MeasureTheory

