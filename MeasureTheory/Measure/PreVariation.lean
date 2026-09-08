/-
Copyright (c) 2025 Oliver Butterley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Butterley, Yoh Tanimoto
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Basic
public import Mathlib.Order.Partition.Finpartition

/-!
# Pre-variation of a subadditive set function

Given a σ-subadditive `ℝ≥0∞`-valued set function `f`, we define the pre-variation as the supremum
over finite measurable partitions of the sum of `f` on the parts. This construction yields a
measure.

## Main definitions

* `IsSigmaSubadditiveSetFun f`: `f` is σ-subadditive on measurable sets
* `ennrealPreVariation f`: the `VectorMeasure X ℝ≥0∞` built from a σ-subadditive function
* `preVariation f`: the `Measure X` built from a σ-subadditive function

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

@[expose] public section

variable {X : Type*} [MeasurableSpace X]

open NNReal ENNReal Function

namespace MeasureTheory

/-!
## Pre-variation of a subadditive `ℝ≥0∞`-valued function

Given a set function `f : Set X → ℝ≥0∞` we can define another set function by taking the supremum
over all finite partitions of measurable sets `E i` of the sum of `∑ i, f (E i)`. If `f` is
σ-subadditive then the function defined is an `ℝ≥0∞`-valued measure.
-/

section

variable (f : Set X → ℝ≥0∞)

open scoped Classical in
/-- If `s` is measurable then `preVariationFun f s` is the supremum over partitions `P` of `s` of
the quantity `∑ p ∈ P.parts, f p`. If `s` is not measurable then it is set to `0`. -/
/-
**MeasureTheory.preVariationFun** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：preVariationFun (s : Set X) : Real>=0∞
参数：s : Set X。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is measurable then `preVariationFun f s` is the supremum over partitions 
`P` of `s` of
the quantity `∑ p ∈ P.parts, f p`. If `s` is not measurable then it is set to `0
`.
-/
noncomputable def preVariationFun (s : Set X) : ℝ≥0∞ :=
  if h : MeasurableSet s then
    ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p ∈ P.parts, f p
  else 0
/-
**MeasureTheory.preVariationFun_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：preVariationFun_apply {s : Set X} (h : MeasurableSet s) : preVariationFun 
f s = ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p in P.parts, f p
参数：h : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preVariationFun_apply {s : Set X} (h : MeasurableSet s) :
    preVariationFun f s =
      ⨆ (P : Finpartition (⟨s, h⟩ : Subtype MeasurableSet)), ∑ p ∈ P.parts, f p := by
  simp [preVariationFun, h]
/-
**MeasureTheory.preVariationFun_of_not_measurableSet** 是 Mathlib 中的一个引理，位于命名空间 `
MeasureTheory`。
形式化陈述：preVariationFun_of_not_measurableSet {s : Set X} (h : ¬ MeasurableSet s) :
 preVariationFun f s = 0
参数：h : ¬ MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preVariationFun_of_not_measurableSet {s : Set X} (h : ¬ MeasurableSet s) :
    preVariationFun f s = 0 := by
  simp [preVariationFun, h]

end

namespace preVariation

variable (f : Set X → ℝ≥0∞)

/-- `preVariationFun` of the empty set is equal to zero. -/
/-
**MeasureTheory.preVariation.empty** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.preV
ariation`。
形式化陈述：empty : preVariationFun f ∅ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `ciSup_unique`：ciSup_unique [Unique ι] {s : ι -> α} : ⨆ i, s i = s defaul
t
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finpartition.empty_parts`：∀ (α : Type u_1) [inst : Lattice α] [inst_1 : 
OrderBot α], (Finpartition.empty α).parts = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`preVariationFun` of the empty set is equal to zero.
-/
lemma empty : preVariationFun f ∅ = 0 := by simp [preVariationFun]

@[simp]
/-
**MeasureTheory.preVariation.zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.preVa
riation`。
形式化陈述：zero : preVariationFun (0 : Set X -> Real>=0∞) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma zero : preVariationFun (0 : Set X → ℝ≥0∞) = 0 := by ext; simp [preVariationFun]
/-
**MeasureTheory.preVariation.sum_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.pre
Variation`。
形式化陈述：sum_le {s : Set X} (hs : MeasurableSet s) (P : Finpartition (⟨s, hs⟩ : Sub
type MeasurableSet)) : ∑ p in P.parts, f p <= preVariationFun f s
参数：hs : MeasurableSet s；P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma sum_le {s : Set X} (hs : MeasurableSet s)
    (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) :
    ∑ p ∈ P.parts, f p ≤ preVariationFun f s := by
  simpa [preVariationFun, hs, le_iSup_iff] using fun _ a ↦ a P

/-- A `Finpartition` constructor in the subtype of `MeasurableSet` from a `P : Finpartition s` with
explicit measurability assumptions. -/
/-
**MeasureTheory.preVariation._root_.Finpartition.toMeasurableSet** 是 Mathlib 中的一
个缩写定义，位于命名空间 `MeasureTheory.preVariation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Finpartition` constructor in the subtype of `MeasurableSet` from a `P : Finpa
rtition s` with
explicit measurability assumptions.
-/
noncomputable abbrev _root_.Finpartition.toMeasurableSet {s : Set X} (P : Finpartition s)
    (hs : MeasurableSet s) (hP : ∀ p ∈ P.parts, MeasurableSet p) :
    Finpartition (⟨s, hs⟩ : Subtype MeasurableSet) :=
  P.toSubtype (by measurability) (by measurability) (by measurability) hs hP
/-
**MeasureTheory.preVariation.sum_le'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.pr
eVariation`。
形式化陈述：sum_le' {s : Set X} (hs : MeasurableSet s) (P : Finpartition s) (hP : fora
ll p in P.parts, MeasurableSet p) : ∑ p in P.parts, f p <= preVariationFun f s
参数：hs : MeasurableSet s；P : Finpartition s；hP : forall p in P.parts, MeasurableS
et p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finpartition.sum_eq_sum_finpartition_subtype`：sum_eq_sum_finpartition_su
btype {X : Type*} [AddCommMonoid X] (f : α -> X) : letI : Lattice (Subtype Pr)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `MeasureTheory.preVariation.sum_le`：sum_le {s : Set X} (hs : MeasurableSe
t s) (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) : ∑ p in P.parts, f p 
<= preVariationFun f s
-/
lemma sum_le' {s : Set X} (hs : MeasurableSet s)
    (P : Finpartition s) (hP : ∀ p ∈ P.parts, MeasurableSet p) :
    ∑ p ∈ P.parts, f p ≤ preVariationFun f s := by
  simp only [P.sum_eq_sum_finpartition_subtype (by measurability) (by measurability)
    (by measurability) hs hP f, sum_le f hs (P.toMeasurableSet hs hP)]

/-- If `P` is a partition of `s₁` and `s₁ ⊆ s₂` then
`∑ p ∈ P.parts, f p ≤ preVariationFun f s₂`. -/
/-
**MeasureTheory.preVariation.sum_le_preVariationFun_of_subset** 是 Mathlib 中的一个引理
，位于命名空间 `MeasureTheory.preVariation`。
形式化陈述：sum_le_preVariationFun_of_subset {s₁ s₂ : Set X} (hs₁ : MeasurableSet s₁) 
(hs₂ : MeasurableSet s₂) (h : s₁ subseteq s₂) (P : Finpartition (⟨s₁, hs₁⟩ : Sub
type MeasurableSet)) : ∑ p in P.parts, f p <= preVariationFun f s₂
参数：hs₁ : MeasurableSet s₁；hs₂ : MeasurableSet s₂；h : s₁ subseteq s₂；P : Finparti
tion (⟨s₁, hs₁⟩ : Subtype MeasurableSet)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_le_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s t
 : Finset ι}, s ⊆…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `Finpartition.parts_subset_extendOfLE`：parts_subset_extendOfLE (hab : a <
= b) : P.parts subseteq (P.extendOfLE hab).parts
· 使用引理 `MeasureTheory.preVariation.sum_le`：sum_le {s : Set X} (hs : MeasurableSe
t s) (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) : ∑ p in P.parts, f p 
<= preVariationFun f s

--- 原说明 ---
If `P` is a partition of `s₁` and `s₁ ⊆ s₂` then
`∑ p ∈ P.parts, f p ≤ preVariationFun f s₂`.
-/
lemma sum_le_preVariationFun_of_subset {s₁ s₂ : Set X} (hs₁ : MeasurableSet s₁)
    (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) (P : Finpartition (⟨s₁, hs₁⟩ : Subtype MeasurableSet)) :
    ∑ p ∈ P.parts, f p ≤ preVariationFun f s₂ := by
  calc
    ∑ p ∈ P.parts, f p ≤ ∑ p ∈ (P.extendOfLE h).parts, f p :=
      Finset.sum_le_sum_of_subset (P.parts_subset_extendOfLE h)
    _ ≤ preVariationFun f s₂ := sum_le f hs₂ _

/-- `preVariationFun` is monotone in terms of the (measurable) set. -/
/-
**MeasureTheory.preVariation.mono** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.preVa
riation`。
形式化陈述：mono {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ subseteq s₂) : preVa
riationFun f s₁ <= preVariationFun f s₂
参数：hs₂ : MeasurableSet s₂；h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.preVariation.sum_le_preVariationFun_of_subset`：sum_le_preV
ariationFun_of_subset {s₁ s₂ : Set X} (hs₁ : MeasurableSet s₁) (hs₂ : Measurable
Set s₂) (h : s₁ subseteq s₂) (P : Finpartition (⟨…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal

--- 原说明 ---
`preVariationFun` is monotone in terms of the (measurable) set.
-/
lemma mono {s₁ s₂ : Set X} (hs₂ : MeasurableSet s₂) (h : s₁ ⊆ s₂) :
    preVariationFun f s₁ ≤ preVariationFun f s₂ := by
  by_cases hs₁ : MeasurableSet s₁
  · have := sum_le_preVariationFun_of_subset f hs₁ hs₂ h
    simp_all [preVariationFun]
  · simp [preVariationFun, hs₁]
/-
**MeasureTheory.preVariation.exists_Finpartition_sum_gt** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.preVariation`。
形式化陈述：exists_Finpartition_sum_gt {s : Set X} (hs : MeasurableSet s) {a : Real>=0
∞} (ha : a < preVariationFun f s) : exists P : Finpartition (⟨s, hs⟩ : Subtype M
easurableSet), a < ∑ p in P.parts, f p
参数：hs : MeasurableSet s；ha : a < preVariationFun f s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma exists_Finpartition_sum_gt {s : Set X} (hs : MeasurableSet s) {a : ℝ≥0∞}
    (ha : a < preVariationFun f s) : ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    a < ∑ p ∈ P.parts, f p := by
  simp_all [preVariationFun, lt_iSup_iff]
/-
**MeasureTheory.preVariation.exists_Finpartition_sum_ge** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.preVariation`。
形式化陈述：exists_Finpartition_sum_ge {s : Set X} (hs : MeasurableSet s) {ε : Real>=0
} (hε : 0 < ε) (h : preVariationFun f s != ∞) : exists P : Finpartition (⟨s, hs⟩
 : Subtype MeasurableSet), preVariationFun f s <= ∑ p in P.parts, f p + ε
参数：hs : MeasurableSet s；hε : 0 < ε；h : preVariationFun f s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ne_or_eq`：ne_or_eq {α : Sort*} (x y : α) : x != y ∨ x = y
· 使用定理 `ENNReal.toNNReal_pos`：toNNReal_pos {a : Real>=0∞} (ha₀ : a != 0) (ha_top
 : a != ∞) : 0 < a.toNNReal
· 使用定理 `ENNReal.sub_lt_self`：∀ {a b : ENNReal}, a ≠ ⊤ → a ≠ 0 → b ≠ 0 → a - b < 
a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.coe_pos`：∀ {r : NNReal}, 0 < ↑r ↔ 0 < r
· 使用引理 `MeasureTheory.preVariation.exists_Finpartition_sum_gt`：exists_Finpartiti
on_sum_gt {s : Set X} (hs : MeasurableSet s) {a : Real>=0∞} (ha : a < preVariati
onFun f s) : exists P : Finpartition (⟨s, h…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `ENNReal.add_le_add_iff_right`：∀ {a b c : ENNReal}, a ≠ ⊤ → (b + a ≤ c + 
a ↔ b ≤ c)
· 使用定理 `ENNReal.coe_ne_top`：coe_ne_top : (r : Real>=0∞) != ∞
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.coe_le_coe._gcongr_2`：∀ {r q : NNReal}, r ≤ q → ↑r ≤ ↑q
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
-/
lemma exists_Finpartition_sum_ge {s : Set X} (hs : MeasurableSet s) {ε : ℝ≥0} (hε : 0 < ε)
    (h : preVariationFun f s ≠ ∞) :
    ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    preVariationFun f s ≤ ∑ p ∈ P.parts, f p + ε := by
  let ε' := min ε (preVariationFun f s).toNNReal
  have hε' : ε' ≤ preVariationFun f s := by simp_all [ε']
  have : ε' ≤ ε := by simp_all [ε']
  obtain hw | hw : preVariationFun f s ≠ 0 ∨ preVariationFun f s = 0 := ne_or_eq _ _
  · have : 0 < ε' := by
      simp only [lt_inf_iff, ε']
      exact ⟨hε, toNNReal_pos hw h⟩
    let a := preVariationFun f s - ε'
    have ha : a < preVariationFun f s := ENNReal.sub_lt_self h hw (by positivity)
    obtain ⟨P, hP⟩ := exists_Finpartition_sum_gt f hs ha
    use P
    calc preVariationFun f s
      _ = a + ε' := (tsub_add_cancel_of_le hε').symm
      _ ≤ ∑ p ∈ P.parts, f p + ε' := by
        exact (ENNReal.add_le_add_iff_right coe_ne_top).mpr (le_of_lt hP)
      _ ≤ ∑ p ∈ P.parts, f p + ε := by gcongr
  · simp [*]
/-
**MeasureTheory.preVariation.exists_Finpartition_sum_ge'** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.preVariation`。
形式化陈述：exists_Finpartition_sum_ge' {s : Set X} (hs : MeasurableSet s) {ε : Real>=
0∞} (hε : 0 < ε) (h : preVariationFun f s != ∞) : exists P : Finpartition (⟨s, h
s⟩ : Subtype MeasurableSet), preVariationFun f s <= ∑ p in P.parts, f p + ε
参数：hs : MeasurableSet s；hε : 0 < ε；h : preVariationFun f s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `MeasureTheory.preVariation.exists_Finpartition_sum_ge`：exists_Finpartiti
on_sum_ge {s : Set X} (hs : MeasurableSet s) {ε : Real>=0} (hε : 0 < ε) (h : pre
VariationFun f s != ∞) : exists P : Finpart…
-/
lemma exists_Finpartition_sum_ge' {s : Set X} (hs : MeasurableSet s) {ε : ℝ≥0∞} (hε : 0 < ε)
    (h : preVariationFun f s ≠ ∞) :
    ∃ P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet),
    preVariationFun f s ≤ ∑ p ∈ P.parts, f p + ε := by
  rcases eq_top_or_lt_top ε with rfl | h'ε
  · simp
  lift ε to NNReal using h'ε.ne
  exact exists_Finpartition_sum_ge _ hs (by simpa using hε) h
/-
**MeasureTheory.preVariation.sum_le_preVariationFun_iUnion'** 是 Mathlib 中的一个引理，位
于命名空间 `MeasureTheory.preVariation`。
形式化陈述：sum_le_preVariationFun_iUnion' {s : Nat -> Set X} (hs : forall i, Measurab
leSet (s i)) (hs' : Pairwise (Disjoint on s)) (P : forall (i : Nat), Finpartitio
n (⟨s i, hs i⟩ : Subtype MeasurableSet)) (n : Nat) : ∑ i in Finset.range n, ∑ p 
in (P i).parts, f p <= preVariationFun f (⋃ i, s i)
参数：hs : forall i, MeasurableSet (s i)；hs' : Pairwise (Disjoint on s)；P : forall 
(i : Nat), Finpartition (⟨s i, hs i⟩ : Subtype MeasurableSet)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅
· 使用定理 `DistribLattice.instIsModularLattice`：∀ {α : Type u_1} [inst : DistribLat
tice α], IsModularLattice α
· 使用定理 `Set.PairwiseDisjoint.supIndep`：∀ {α : Type u_1} {ι : Type u_3} [inst : D
istribLattice α] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α},   (↑s).Pairwi
seDisjoint f → s.Su…
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.sup_coe`：sup_coe {P : α -> Prop} {Pbot : P ⊥} {Psup : forall ⦃x y
⦄, P x -> P y -> P (x ⊔ y)} (t : Finset β) (f : β -> { x : α // P x }) : letI
· 使用定理 `Finset.sup_set_eq_biUnion`：sup_set_eq_biUnion (s : Finset α) (f : α -> S
et β) : s.sup f = ⋃ x in s, f x
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用引理 `Finpartition.sum_combine`：sum_combine {ι : Type*} {I : Finset ι} {s : ι 
-> α} (P : forall i, Finpartition (s i)) (ha : I.SupIndep s) {M : Type*} [AddCom
mMonoid M] (f …
· 使用定理 `Finset.sum_le_sum_of_subset`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] [inst_1 : Preorder M] [CanonicallyOrderedAdd M] {f : ι → M}   {s t
 : Finset ι}, s ⊆…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `Finpartition.parts_subset_extendOfLE`：parts_subset_extendOfLE (hab : a <
= b) : P.parts subseteq (P.extendOfLE hab).parts
· 使用引理 `MeasureTheory.preVariation.sum_le`：sum_le {s : Set X} (hs : MeasurableSe
t s) (P : Finpartition (⟨s, hs⟩ : Subtype MeasurableSet)) : ∑ p in P.parts, f p 
<= preVariationFun f s
-/
lemma sum_le_preVariationFun_iUnion' {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s))
    (P : ∀ (i : ℕ), Finpartition (⟨s i, hs i⟩ : Subtype MeasurableSet)) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p ≤ preVariationFun f (⋃ i, s i) := by
  let s' (i : ℕ) : Subtype MeasurableSet := ⟨s i, hs i⟩
  have hs_disj : Set.PairwiseDisjoint (Finset.range n : Set ℕ) s' := fun i _ j _ hij => by
    simp only [Function.onFun, disjoint_iff, Subtype.ext_iff]
    exact Set.disjoint_iff_inter_eq_empty.mp (hs' hij)
  let Q := Finpartition.combine P hs_disj.supIndep
  have hQ_le : (Finset.range n).sup s' ≤ ⟨⋃ i, s i, MeasurableSet.iUnion hs⟩ := by
    rw [← Subtype.coe_le_coe, Finset.sup_coe (Psup := by measurability), Finset.sup_set_eq_biUnion]
    exact Set.iUnion₂_subset fun i _ => Set.subset_iUnion s i
  let R := Q.extendOfLE hQ_le
  calc ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p
    _ = ∑ p ∈ Q.parts, f p := (Finpartition.sum_combine P hs_disj.supIndep (fun p => f p)).symm
    _ ≤ ∑ p ∈ R.parts, f p := Finset.sum_le_sum_of_subset (Q.parts_subset_extendOfLE hQ_le)
    _ ≤ preVariationFun f (⋃ i, s i) := sum_le f (MeasurableSet.iUnion hs) R
/-
**MeasureTheory.preVariation.sum_le_preVariationFun_iUnion** 是 Mathlib 中的一个引理，位于
命名空间 `MeasureTheory.preVariation`。
形式化陈述：sum_le_preVariationFun_iUnion {s : Nat -> Set X} (hs : forall i, Measurabl
eSet (s i)) (hs' : Pairwise (Disjoint on s)) : ∑' i, preVariationFun f (s i) <= 
preVariationFun f (⋃ i, s i)
参数：hs : forall i, MeasurableSet (s i)；hs' : Pairwise (Disjoint on s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.tsum_le_of_sum_range_le`：tsum_le_of_sum_range_le {f : Nat -> Rea
l>=0∞} {c : Real>=0∞} (h : forall n, ∑ i in Finset.range n, f i <= c) : ∑' n, f 
n <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.le_of_forall_pos_le_add`：le_of_forall_pos_le_add (h : forall ε :
 Real>=0, 0 < ε -> b < ∞ -> a <= b + ε) : a <= b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `lt_of_le_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `MeasureTheory.preVariation.mono`：mono {s₁ s₂ : Set X} (hs₂ : MeasurableS
et s₂) (h : s₁ subseteq s₂) : preVariationFun f s₁ <= preVariationFun f s₂
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
（共 67 条，此处仅展示前 30 条）
-/
lemma sum_le_preVariationFun_iUnion {s : ℕ → Set X} (hs : ∀ i, MeasurableSet (s i))
    (hs' : Pairwise (Disjoint on s)) :
    ∑' i, preVariationFun f (s i) ≤ preVariationFun f (⋃ i, s i) := by
  refine ENNReal.tsum_le_of_sum_range_le fun n ↦ ?_
  by_cases hn : n = 0
  · simp [hn]
  refine ENNReal.le_of_forall_pos_le_add fun ε' hε' hsnetop ↦ ?_
  let ε := ε' / n
  have hε : 0 < ε := by positivity
  have hs'' i : preVariationFun f (s i) ≠ ⊤ := lt_top_iff_ne_top.mp <|
    (mono f (MeasurableSet.iUnion hs) (Set.subset_iUnion s i)).trans_lt hsnetop
  -- For each set `s i` we choose a Finpartition `P i` such that, for each `i`,
  -- `preVariationFun f (s i) ≤ ∑ p ∈ (P i), f p + ε`.
  choose P hP using fun i ↦ exists_Finpartition_sum_ge f (hs i) (hε) (hs'' i)
  calc ∑ i ∈ Finset.range n, preVariationFun f (s i)
    _ ≤ ∑ i ∈ Finset.range n, (∑ p ∈ (P i).parts, f p + ε) := Finset.sum_le_sum fun i _ => hP i
    _ = ∑ i ∈ Finset.range n, ∑ p ∈ (P i).parts, f p + ε' := by
      rw [Finset.sum_add_distrib]; norm_cast
      simp [show n * ε = ε' by field]
    _ ≤ preVariationFun f (⋃ i, s i) + ε' := by
      gcongr; exact sum_le_preVariationFun_iUnion' f hs hs' P n

end preVariation

/-- A set function is σ-subadditive on measurable sets if the value assigned to the union of a
countable disjoint family of measurable sets is bounded above by the sum of values on the family. -/
/-
**MeasureTheory.IsSigmaSubadditiveSetFun** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheor
y`。
形式化陈述：IsSigmaSubadditiveSetFun (f : Set X -> Real>=0∞) : Prop
参数：f : Set X -> Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set function is σ-subadditive on measurable sets if the value assigned to the 
union of a
countable disjoint family of measurable sets is bounded above by the sum of valu
es on the family.
-/
def IsSigmaSubadditiveSetFun (f : Set X → ℝ≥0∞) : Prop :=
  ∀ (s : ℕ → {t : Set X // MeasurableSet t}), Pairwise (Disjoint on (Subtype.val ∘ s)) →
    f (⋃ i, (s i).val) ≤ ∑' i, f (s i)
/-
**MeasureTheory.isSigmaSubadditiveSetFun_zero** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：isSigmaSubadditiveSetFun_zero : IsSigmaSubadditiveSetFun (0 : Set X -> Rea
l>=0∞)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma isSigmaSubadditiveSetFun_zero : IsSigmaSubadditiveSetFun (0 : Set X → ℝ≥0∞) := by intro; simp

namespace preVariation

variable {f : Set X → ℝ≥0∞}

/-- Additivity of `preVariationFun` for disjoint measurable sets. -/
/-
**MeasureTheory.preVariation.iUnion** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.pre
Variation`。
形式化陈述：iUnion (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Nat -> Set X
) (hs : forall i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) : HasSum
 (fun i => preVariationFun f (s i)) (preVariationFun f (⋃ i, s i))
参数：hf : IsSigmaSubadditiveSetFun f；hf' : f ∅ = 0；s : Nat -> Set X；hs : forall i,
 MeasurableSet (s i)；hs' : Pairwise (Disjoint on s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Summable.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMono
id α] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α
} [T2Spac…
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `MeasureTheory.preVariation.sum_le_preVariationFun_iUnion`：sum_le_preVari
ationFun_iUnion {s : Nat -> Set X} (hs : forall i, MeasurableSet (s i)) (hs' : P
airwise (Disjoint on s)) : ∑' i, preVariationF…
· 使用定理 `ENNReal.le_tsum_of_forall_lt_exists_sum`：∀ {α : Type u_1} {a : ENNReal} 
{f : α → ENNReal}, (∀ b < a, ∃ I, b < ∑ i ∈ I, f i) → a ≤ ∑' (i : α), f i
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `Finpartition.le`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : OrderBot 
α] {a : α} (P : Finpartition a) {b : α}, b ∈ P.parts → b ≤ a
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Summable.tsum_finsetSum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : AddCommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFilter β}
 [T2Space α] …
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Additivity of `preVariationFun` for disjoint measurable sets.
-/
lemma iUnion (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : ℕ → Set X)
    (hs : ∀ i, MeasurableSet (s i)) (hs' : Pairwise (Disjoint on s)) :
    HasSum (fun i ↦ preVariationFun f (s i)) (preVariationFun f (⋃ i, s i)) := by
  refine ENNReal.summable.hasSum_iff.mpr (le_antisymm (sum_le_preVariationFun_iUnion f hs hs') ?_)
  refine ENNReal.le_tsum_of_forall_lt_exists_sum fun b hb ↦ ?_
  simp only [preVariationFun, MeasurableSet.iUnion hs, reduceDIte, lt_iSup_iff] at hb
  obtain ⟨Q, hQ⟩ := hb
  let s' (i : ℕ) : Subtype MeasurableSet := ⟨s i, hs i⟩
  let P (i : ℕ) := Q.restrict (b := s' i) (Set.subset_iUnion s i)
  have splitting : ∑ q ∈ Q.parts, f q ≤ ∑' i, ∑ p ∈ (P i).parts, f p := by
    calc ∑ q ∈ Q.parts, f q
      _ ≤ ∑ q ∈ Q.parts, ∑' i, f (q ⊓ s' i) := by
          apply Finset.sum_le_sum fun q hq => ?_
          have hq_eq : q.val = ⋃ i, q.val ∩ s i := by
            rw [← Set.inter_iUnion]; exact (Set.inter_eq_left.mpr (Q.le hq)).symm
          let t (i : ℕ) : Subtype MeasurableSet := ⟨q.val ∩ s i, q.2.inter (hs i)⟩
          have ht_disj : Pairwise (Disjoint on (Subtype.val ∘ t)) :=
            fun i j hij => (hs' hij).mono Set.inter_subset_right Set.inter_subset_right
          calc f q
            _ = f (⋃ i, q.val ∩ s i) := congrArg f hq_eq
            _ = f (⋃ i, (t i).val) := rfl
            _ ≤ ∑' i, f (t i) := hf t ht_disj
            _ = ∑' i, f (q ⊓ s' i) := rfl
      _ = ∑' i, ∑ q ∈ Q.parts, f (q ⊓ s' i) :=
          (Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)).symm
      _ = ∑' i, ∑ p ∈ (P i).parts, f p := by
          congr 1; funext i
          exact (Q.sum_restrict _ (fun p => f p) hf').symm
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp <| ENNReal.tsum_eq_iSup_nat ▸ lt_of_lt_of_le hQ splitting
  have bound (i : ℕ) : ∑ p ∈ (P i).parts, f p ≤ preVariationFun f (s i) := sum_le f (hs i) (P i)
  exact ⟨Finset.range n, lt_of_lt_of_le hn (Finset.sum_le_sum fun i _ => bound i)⟩

end preVariation

/-!
## Construction of measures from σ-subadditive functions
-/

variable (f : Set X → ℝ≥0∞)

/-- The `VectorMeasure X ℝ≥0∞` built from a σ-subadditive function. -/
/-
**MeasureTheory.ennrealPreVariation** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：ennrealPreVariation (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) : Ve
ctorMeasure X Real>=0∞ where measureOf'
参数：hf : IsSigmaSubadditiveSetFun f；hf' : f ∅ = 0。
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.preVariation.empty`：empty : preVariationFun f ∅ = 0
· 使用引理 `MeasureTheory.preVariation.iUnion`：iUnion (hf : IsSigmaSubadditiveSetFun
 f) (hf' : f ∅ = 0) (s : Nat -> Set X) (hs : forall i, MeasurableSet (s i)) (hs'
 : Pairwise (Disjoint o…

--- 原说明 ---
The `VectorMeasure X ℝ≥0∞` built from a σ-subadditive function.
-/
noncomputable def ennrealPreVariation (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) :
    VectorMeasure X ℝ≥0∞ where
  measureOf' := preVariationFun f
  empty' := preVariation.empty f
  not_measurable' _ h := by simp [preVariationFun, h]
  m_iUnion' := preVariation.iUnion hf hf'
/-
**MeasureTheory.ennrealPreVariation_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：ennrealPreVariation_apply (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0
) (s : Set X) : ennrealPreVariation f hf hf' s = preVariationFun f s
参数：hf : IsSigmaSubadditiveSetFun f；hf' : f ∅ = 0；s : Set X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ennrealPreVariation_apply (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Set X) :
  ennrealPreVariation f hf hf' s = preVariationFun f s := rfl

@[simp]
/-
**MeasureTheory.ennrealPreVariation_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheor
y`。
形式化陈述：ennrealPreVariation_zero : ennrealPreVariation (0 : Set X -> Real>=0∞) isS
igmaSubadditiveSetFun_zero (by simp) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.ext`：ext {s t : VectorMeasure α M} (h : fora
ll i : Set α, MeasurableSet i -> s i = t i) : s = t
· 使用引理 `MeasureTheory.isSigmaSubadditiveSetFun_zero`：isSigmaSubadditiveSetFun_ze
ro : IsSigmaSubadditiveSetFun (0 : Set X -> Real>=0∞)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `MeasureTheory.preVariation.zero`：zero : preVariationFun (0 : Set X -> Re
al>=0∞) = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ennrealPreVariation_zero :
    ennrealPreVariation (0 : Set X → ℝ≥0∞) isSigmaSubadditiveSetFun_zero (by simp) = 0 := by
  ext; simp [ennrealPreVariation_apply]

/-- The `Measure X` built from a σ-subadditive function. -/
/-
**MeasureTheory.preVariation** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：preVariation (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) : Measure X
参数：hf : IsSigmaSubadditiveSetFun f；hf' : f ∅ = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Measure X` built from a σ-subadditive function.
-/
noncomputable def preVariation (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) : Measure X :=
  (ennrealPreVariation f hf hf').ennrealToMeasure
/-
**MeasureTheory.preVariation_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：preVariation_apply (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : 
Set X) : preVariation f hf hf' s = (ennrealPreVariation f hf hf').ennrealToMeasu
re s
参数：hf : IsSigmaSubadditiveSetFun f；hf' : f ∅ = 0；s : Set X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preVariation_apply (hf : IsSigmaSubadditiveSetFun f) (hf' : f ∅ = 0) (s : Set X) :
    preVariation f hf hf' s = (ennrealPreVariation f hf hf').ennrealToMeasure s := rfl

@[simp]
/-
**MeasureTheory.preVariation_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：preVariation_zero : preVariation (0 : Set X -> Real>=0∞) isSigmaSubadditiv
eSetFun_zero (by simp) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用引理 `MeasureTheory.isSigmaSubadditiveSetFun_zero`：isSigmaSubadditiveSetFun_ze
ro : IsSigmaSubadditiveSetFun (0 : Set X -> Real>=0∞)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.ennrealPreVariation_zero`：ennrealPreVariation_zero : ennre
alPreVariation (0 : Set X -> Real>=0∞) isSigmaSubadditiveSetFun_zero (by simp) =
 0
· 使用定理 `MeasureTheory.VectorMeasure.ennrealToMeasure_zero`：ennrealToMeasure_zero
 : ennrealToMeasure (0 : VectorMeasure α Real>=0∞) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma preVariation_zero :
    preVariation (0 : Set X → ℝ≥0∞) isSigmaSubadditiveSetFun_zero (by simp) = 0 := by
  ext; simp [preVariation_apply]

end MeasureTheory

