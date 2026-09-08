/-
Copyright (c) 2026 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!
# Set integral

In this file we prove properties of `∫ᵛ x in s, f x ∂[B; μ]`. Recall that this notation
is defined as `∫ᵛ x, f x ∂[B; μ.restrict s]`.

The API in this file is modelled on the API for the Bochner integral.
-/

@[expose] public section

assert_not_exists InnerProductSpace

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology ContinuousLinearMap
open scoped ENNReal NNReal Finset

variable {ι X E F G H : Type*} {mX : MeasurableSpace X}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]
  {μ ν : VectorMeasure X F} {f g : X → E} {s t : Set X}

namespace MeasureTheory.VectorMeasure

/-
**MeasureTheory.VectorMeasure.IntegrableOn.mono** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure.IntegrableOn`。
形式化陈述：∀ {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory
.VectorMeasure X F} {f : X → E} {s t : Set X},   MeasurableSet s → t ⊆ s → μ.Int
egrableOn f s → μ.IntegrableOn f t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
-/
theorem IntegrableOn.mono (hs : MeasurableSet s) (hts : t ⊆ s) (h : μ.IntegrableOn f s) :
    μ.IntegrableOn f t := by
  by_cases ht : MeasurableSet t; swap
  · simp [VectorMeasure.IntegrableOn, restrict_not_measurable _ ht]
  apply Integrable.mono_measure h
  simp [variation_restrict, hs, ht, Measure.restrict_mono hts le_rfl]
/-
**MeasureTheory.VectorMeasure.IntegrableOn.union** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure.IntegrableOn`。
形式化陈述：∀ {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory
.VectorMeasure X F} {f : X → E} {s t : Set X},   MeasurableSet s → MeasurableSet
 t → μ.IntegrableOn f s → μ.IntegrableOn f t → μ.IntegrableOn f (s ∪ t)
参数：s ∪ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.mono_measure`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace 
ε]   [inst_1 : ContinuousEN…
· 使用定理 `MeasureTheory.Integrable.add_measure`：∀ {α : Type u_1} {ε : Type u_5} {m
 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α} [inst : TopologicalSpace ε
]   [inst_1 : ContinuousEN…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict_le`：variation_restrict_le
 : (μ.restrict s).variation <= μ.variation.restrict s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_union_le`：restrict_union_le (s s' : Set α
) : μ.restrict (s union s') <= μ.restrict s + μ.restrict s'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
-/
theorem IntegrableOn.union (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hf : μ.IntegrableOn f s) (h'f : μ.IntegrableOn f t) :
    μ.IntegrableOn f (s ∪ t) := by
  apply Integrable.mono_measure (hf.add_measure h'f)
  grw [variation_restrict_le, Measure.restrict_union_le]
  simp [variation_restrict, hs, ht]

/- `simpNF` complains that this lemma can be proved by `simp`, because the `simp`-generated lemma
unfolds the abbrev `VectorMeasure.Integrable`. TODO: fix `simp`. See lean4#13958. -/
/-
**MeasureTheory.VectorMeasure.IntegrableOn.empty** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure.IntegrableOn`。
形式化陈述：∀ {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory
.VectorMeasure X F} {f : X → E}, μ.IntegrableOn f ∅
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_empty`：restrict_empty : v.restrict 
∅ = 0

--- 原说明 ---
`simpNF` complains that this lemma can be proved by `simp`, because the `simp`-g
enerated lemma
unfolds the abbrev `VectorMeasure.Integrable`. TODO: fix `simp`. See lean4#13958
.
-/
@[simp, nolint simpNF] theorem IntegrableOn.empty : μ.IntegrableOn f ∅ := by
  simp [VectorMeasure.IntegrableOn]
/-
**MeasureTheory.VectorMeasure.IntegrableOn.biUnion_finite** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure.IntegrableOn`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : Measur
ableSpace X} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ 
: MeasureTheory.VectorMeasure X F} {f : X → E} {s : Set ι},   s.Finite →     ∀ {
t : ι → Set X},       (∀ i ∈ s, MeasurableSet (t i)) → (∀ i ∈ s, μ.IntegrableOn 
f (t i)) → μ.IntegrableOn f (⋃ i ∈ s, t i)
参数：∀ i ∈ s, MeasurableSet (t i)；∀ i ∈ s, μ.IntegrableOn f (t i)；⋃ i ∈ s, t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `Set.iUnion_iUnion_eq_or_left`：iUnion_iUnion_eq_or_left {b : β} {p : β ->
 Prop} {s : forall x : β, x = b ∨ p x -> Set α} : ⋃ (x) (h), s x h = s b (Or.inl
 rfl) union ⋃ (x) …
· 使用定理 `MeasureTheory.VectorMeasure.IntegrableOn.union`：∀ {X : Type u_2} {E : Ty
pe u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]   
[inst_1 : NormedAddCommGroup F] {μ :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.Finite.measurableSet_biUnion`：Set.Finite.measurableSet_biUnion {f : 
β -> Set α} {s : Set β} (hs : s.Finite) (h : forall b in s, MeasurableSet (f b))
 : MeasurableSet (⋃ b …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IntegrableOn.biUnion_finite
    {s : Set ι} (hs : s.Finite) {t : ι → Set X} (ht : ∀ i ∈ s, MeasurableSet (t i))
    (h't : ∀ i ∈ s, μ.IntegrableOn f (t i)) :
    μ.IntegrableOn f (⋃ i ∈ s, t i) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | insert _ h's hf =>
    simp only [mem_insert_iff, forall_eq_or_imp, iUnion_iUnion_eq_or_left] at ht h't ⊢
    exact IntegrableOn.union ht.1 (h's.measurableSet_biUnion ht.2)  h't.1 (hf ht.2 h't.2)
/-
**MeasureTheory.VectorMeasure.IntegrableOn.biUnion_finset** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure.IntegrableOn`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : Measur
ableSpace X} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ 
: MeasureTheory.VectorMeasure X F} {f : X → E} {s : Finset ι} {t : ι → Set X},  
 (∀ i ∈ s, MeasurableSet (t i)) → (∀ i ∈ s, μ.IntegrableOn f (t i)) → μ.Integrab
leOn f (⋃ i ∈ s, t i)
参数：∀ i ∈ s, MeasurableSet (t i)；∀ i ∈ s, μ.IntegrableOn f (t i)；⋃ i ∈ s, t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.IntegrableOn.biUnion_finite`：∀ {ι : Type u_1
} {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : 
NormedAddCommGroup E]   [inst_1 : NormedAddCo…
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem IntegrableOn.biUnion_finset {s : Finset ι} {t : ι → Set X}
    (ht : ∀ i ∈ s, MeasurableSet (t i)) (h't : ∀ i ∈ s, μ.IntegrableOn f (t i)) :
    μ.IntegrableOn f (⋃ i ∈ s, t i) :=
  IntegrableOn.biUnion_finite s.finite_toSet ht h't
/-
**MeasureTheory.VectorMeasure.IntegrableOn.iUnion_finite** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure.IntegrableOn`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : Measur
ableSpace X} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ 
: MeasureTheory.VectorMeasure X F} {f : X → E} [Finite ι] {t : ι → Set X},   (∀ 
(i : ι), MeasurableSet (t i)) → (∀ (i : ι), μ.IntegrableOn f (t i)) → μ.Integrab
leOn f (⋃ i, t i)
参数：∀ (i : ι), MeasurableSet (t i)；∀ (i : ι), μ.IntegrableOn f (t i)；⋃ i, t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `MeasureTheory.VectorMeasure.IntegrableOn.biUnion_finset`：∀ {ι : Type u_1
} {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : 
NormedAddCommGroup E]   [inst_1 : NormedAddCo…
-/
theorem IntegrableOn.iUnion_finite [Finite ι] {t : ι → Set X}
    (ht : ∀ i, MeasurableSet (t i)) (h't : ∀ i, μ.IntegrableOn f (t i)) :
    μ.IntegrableOn f (⋃ i, t i) := by
  cases nonempty_fintype ι
  simpa using IntegrableOn.biUnion_finset (f := f) (μ := μ) (s := Finset.univ) (t := t)
    (fun i hi ↦ ht i) (fun i hi ↦ h't i)
/-
**MeasureTheory.VectorMeasure.integrableOn_univ** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：∀ {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory
.VectorMeasure X F} {f : X → E},   μ.IntegrableOn f Set.univ ↔ μ.Integrable f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_univ`：restrict_univ : v.restrict Se
t.univ = v
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem integrableOn_univ : μ.IntegrableOn f univ ↔ μ.Integrable f := by
  simp [VectorMeasure.IntegrableOn]
/-
**MeasureTheory.VectorMeasure.Integrable.integrableOn** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory
.VectorMeasure X F} {f : X → E} {s : Set X},   μ.Integrable f → μ.IntegrableOn f
 s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.VectorMeasure.IntegrableOn.mono`：∀ {X : Type u_2} {E : Typ
e u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]   [
inst_1 : NormedAddCommGroup F] {μ :…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.integrableOn_univ`：∀ {X : Type u_2} {E : Typ
e u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]   [
inst_1 : NormedAddCommGroup F] {μ :…
-/
theorem Integrable.integrableOn (h : μ.Integrable f) : μ.IntegrableOn f s := by
  rw [← integrableOn_univ] at h
  exact h.mono MeasurableSet.univ (subset_univ _)
/-
**MeasureTheory.VectorMeasure.integrable_indicator_iff** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：integrable_indicator_iff (hs : MeasurableSet s) : μ.Integrable (indicator 
s f) ↔ μ.IntegrableOn f s
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem integrable_indicator_iff (hs : MeasurableSet s) :
    μ.Integrable (indicator s f) ↔ μ.IntegrableOn f s := by
  simp [VectorMeasure.Integrable, VectorMeasure.IntegrableOn, MeasureTheory.IntegrableOn,
    MeasureTheory.integrable_indicator_iff hs, variation_restrict hs]
/-
**MeasureTheory.VectorMeasure.IntegrableOn.integrable_indicator** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.VectorMeasure.IntegrableOn`。
形式化陈述：∀ {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [i
nst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] {μ : MeasureTheory
.VectorMeasure X F} {f : X → E} {s : Set X},   μ.IntegrableOn f s → MeasurableSe
t s → μ.Integrable (s.indicator f)
参数：s.indicator f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.VectorMeasure.integrable_indicator_iff`：integrable_indicat
or_iff (hs : MeasurableSet s) : μ.Integrable (indicator s f) ↔ μ.IntegrableOn f 
s
-/
theorem IntegrableOn.integrable_indicator (h : μ.IntegrableOn f s) (hs : MeasurableSet s) :
    μ.Integrable (indicator s f) :=
  (integrable_indicator_iff hs).2 h

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G] [NormedSpace ℝ H]
  {B : E →L[ℝ] F →L[ℝ] G}
/-
**MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in
 s, f x ∂[B; μ] = 0
参数：hs : ¬MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero_vectorMeasure`：integral_zero_v
ectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) :
    ∫ᵛ x in s, f x ∂[B; μ] = 0 := by
  simp [restrict_not_measurable _ hs]
/-
**MeasureTheory.VectorMeasure.setIntegral_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.VectorMeasure`。
形式化陈述：setIntegral_congr_ae (h : forallᵐ x ∂μ.variation, x in s -> f x = g x) : ∫
ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in s, g x ∂[B; μ]
参数：h : forallᵐ x ∂μ.variation, x in s -> f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.VectorMeasure.integral_congr_ae`：integral_congr_ae (h : f 
=ᵐ[μ.variation] g) : ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_congr_ae (h : ∀ᵐ x ∂μ.variation, x ∈ s → f x = g x) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in s, g x ∂[B; μ] := by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  apply integral_congr_ae
  rw [variation_restrict hs]
  exact (ae_restrict_iff' hs).2 h
/-
**MeasureTheory.VectorMeasure.setIntegral_congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：setIntegral_congr_fun (h : EqOn f g s) : ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in 
s, g x ∂[B; μ]
参数：h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_congr_ae`：setIntegral_congr_ae (
h : forallᵐ x ∂μ.variation, x in s -> f x = g x) : ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x
 in s, g x ∂[B; μ]
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem setIntegral_congr_fun (h : EqOn f g s) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in s, g x ∂[B; μ] :=
  setIntegral_congr_ae <| Eventually.of_forall h
/-
**MeasureTheory.VectorMeasure.setIntegral_union** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：setIntegral_union (hst : Disjoint s t) (hs : MeasurableSet s) (ht : Measur
ableSet t) (hfs : μ.IntegrableOn f s) (hft : μ.IntegrableOn f t) : ∫ᵛ x in s uni
on t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in t, f x ∂[B; μ]
参数：hst : Disjoint s t；hs : MeasurableSet s；ht : MeasurableSet t；hfs : μ.Integrab
leOn f s；hft : μ.IntegrableOn f t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.integral_add_vectorMeasure`：integral_add_vec
torMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) : ∫ᵛ x, f x ∂[B; μ + ν] =
 ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[B; ν]
· 使用定理 `MeasureTheory.VectorMeasure.restrict_union`：restrict_union (h : Disjoint
 s t) (hs : MeasurableSet s) (ht : MeasurableSet t) : v.restrict (s union t) = v
.restrict s + v.restrict t
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem setIntegral_union (hst : Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) (hft : μ.IntegrableOn f t) :
    ∫ᵛ x in s ∪ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in t, f x ∂[B; μ] := by
  rw [← integral_add_vectorMeasure hfs hft, μ.restrict_union hst hs ht]
/-
**MeasureTheory.VectorMeasure.setIntegral_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：setIntegral_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t) (hfs : μ.I
ntegrableOn f s) (hts : t subseteq s) : ∫ᵛ x in s \ t, f x ∂[B; μ] = ∫ᵛ x in s, 
f x ∂[B; μ] - ∫ᵛ x in t, f x ∂[B; μ]
参数：hs : MeasurableSet s；ht : MeasurableSet t；hfs : μ.IntegrableOn f s；hts : t su
bseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_union`：setIntegral_union (hst : 
Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t) (hfs : μ.IntegrableO
n f s) (hft : μ.IntegrableOn f t) :…
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasureTheory.VectorMeasure.IntegrableOn.mono`：∀ {X : Type u_2} {E : Typ
e u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]   [
inst_1 : NormedAddCommGroup F] {μ :…
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
-/
theorem setIntegral_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) (hts : t ⊆ s) :
    ∫ᵛ x in s \ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] - ∫ᵛ x in t, f x ∂[B; μ] := by
  rw [eq_sub_iff_add_eq, ← setIntegral_union (by grind) (hs.diff ht) ht (hfs.mono hs sdiff_subset)
    (hfs.mono hs hts), sdiff_union_of_subset hts]
/-
**MeasureTheory.VectorMeasure.setIntegral_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_inter_add_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t) 
(hfs : μ.IntegrableOn f s) : ∫ᵛ x in s inter t, f x ∂[B; μ] + ∫ᵛ x in s \ t, f x
 ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ]
参数：hs : MeasurableSet s；ht : MeasurableSet t；hfs : μ.IntegrableOn f s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_inter_add_sdiff`：restrict_inter_add
_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t) : v.restrict (s inter t) + 
v.restrict (s \ t) = v.restrict s
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.VectorMeasure.integral_add_vectorMeasure`：integral_add_vec
torMeasure (hμ : μ.Integrable f) (hν : ν.Integrable f) : ∫ᵛ x, f x ∂[B; μ + ν] =
 ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x, f x ∂[B; ν]
· 使用定理 `MeasureTheory.VectorMeasure.IntegrableOn.mono`：∀ {X : Type u_2} {E : Typ
e u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]   [
inst_1 : NormedAddCommGroup F] {μ :…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
theorem setIntegral_inter_add_sdiff (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hfs : μ.IntegrableOn f s) :
    ∫ᵛ x in s ∩ t, f x ∂[B; μ] + ∫ᵛ x in s \ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  rw [← μ.restrict_inter_add_sdiff hs ht,
    integral_add_vectorMeasure (hfs.mono hs inter_subset_left) (hfs.mono hs sdiff_subset)]
/-
**MeasureTheory.VectorMeasure.setIntegral_biUnion_finset** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_biUnion_finset {ι : Type*} (t : Finset ι) {s : ι -> Set X} (hs
 : forall i in t, MeasurableSet (s i)) (h's : Set.Pairwise (↑t) (Disjoint on s))
 (hf : forall i in t, μ.IntegrableOn f (s i)) : ∫ᵛ x in ⋃ i in t, s i, f x ∂[B; 
μ] = ∑ i in t, ∫ᵛ x in s i, f x ∂[B; μ]
参数：t : Finset ι；hs : forall i in t, MeasurableSet (s i)；h's : Set.Pairwise (↑t) 
(Disjoint on s)；hf : forall i in t, μ.IntegrableOn f (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_of_empty`：iUnion_of_empty [IsEmpty ι] (s : ι -> Set α) : ⋃ i,
 s i = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Set.iUnion_empty`：iUnion_empty : (⋃ _ : ι, ∅ : Set α) = ∅
· 使用定理 `MeasureTheory.VectorMeasure.restrict_empty`：restrict_empty : v.restrict 
∅ = 0
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero_vectorMeasure`：integral_zero_v
ectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.set_biUnion_insert`：set_biUnion_insert (a : α) (s : Finset α) (t 
: α -> Set β) : ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_union`：setIntegral_union (hst : 
Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t) (hfs : μ.IntegrableO
n f s) (hft : μ.IntegrableOn f t) :…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.measurableSet_biUnion`：Finset.measurableSet_biUnion {f : β -> Set
 α} (s : Finset β) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋃ b
 in s, f b)
· 使用定理 `MeasureTheory.VectorMeasure.IntegrableOn.biUnion_finset`：∀ {ι : Type u_1
} {X : Type u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : 
NormedAddCommGroup E]   [inst_1 : NormedAddCo…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
-/
theorem setIntegral_biUnion_finset {ι : Type*} (t : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ t, MeasurableSet (s i)) (h's : Set.Pairwise (↑t) (Disjoint on s))
    (hf : ∀ i ∈ t, μ.IntegrableOn f (s i)) :
    ∫ᵛ x in ⋃ i ∈ t, s i, f x ∂[B; μ] = ∑ i ∈ t, ∫ᵛ x in s i, f x ∂[B; μ] := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ hat IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact hs.1
    · exact Finset.measurableSet_biUnion _ hs.2
    · exact hf.1
    · apply IntegrableOn.biUnion_finset hs.2 hf.2
/-
**MeasureTheory.VectorMeasure.setIntegral_iUnion_fintype** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_iUnion_fintype {ι : Type*} [Fintype ι] {s : ι -> Set X} (hs : 
forall i, MeasurableSet (s i)) (h's : Pairwise (Disjoint on s)) (hf : forall i, 
μ.IntegrableOn f (s i)) : ∫ᵛ x in ⋃ i, s i, f x ∂[B; μ] = ∑ i, ∫ᵛ x in s i, f x 
∂[B; μ]
参数：hs : forall i, MeasurableSet (s i)；h's : Pairwise (Disjoint on s)；hf : forall
 i, μ.IntegrableOn f (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_true`：iUnion_true {s : True -> Set α} : iUnion s = s trivial
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_biUnion_finset`：setIntegral_biUn
ion_finset {ι : Type*} (t : Finset ι) {s : ι -> Set X} (hs : forall i in t, Meas
urableSet (s i)) (h's : Set.Pairwise (↑t) (D…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem setIntegral_iUnion_fintype {ι : Type*} [Fintype ι] {s : ι → Set X}
    (hs : ∀ i, MeasurableSet (s i)) (h's : Pairwise (Disjoint on s))
    (hf : ∀ i, μ.IntegrableOn f (s i)) :
    ∫ᵛ x in ⋃ i, s i, f x ∂[B; μ] = ∑ i, ∫ᵛ x in s i, f x ∂[B; μ] := by
  convert setIntegral_biUnion_finset Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]
/-
**MeasureTheory.VectorMeasure.setIntegral_empty** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：setIntegral_empty : ∫ᵛ x in ∅, f x ∂[B; μ] = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_empty`：restrict_empty : v.restrict 
∅ = 0
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero_vectorMeasure`：integral_zero_v
ectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_empty : ∫ᵛ x in ∅, f x ∂[B; μ] = 0 := by simp
/-
**MeasureTheory.VectorMeasure.setIntegral_univ** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.VectorMeasure`。
形式化陈述：setIntegral_univ : ∫ᵛ x in univ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_univ`：restrict_univ : v.restrict Se
t.univ = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_univ : ∫ᵛ x in univ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] := by simp
/-
**MeasureTheory.VectorMeasure.setIntegral_add_compl** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：setIntegral_add_compl (hs : MeasurableSet s) (hfi : μ.Integrable f) : ∫ᵛ x
 in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
参数：hs : MeasurableSet s；hfi : μ.Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_union`：setIntegral_union (hst : 
Disjoint s t) (hs : MeasurableSet s) (ht : MeasurableSet t) (hfs : μ.IntegrableO
n f s) (hft : μ.IntegrableOn f t) :…
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.VectorMeasure.Integrable.integrableOn`：∀ {X : Type u_2} {E
 : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : NormedAddCommGroup 
E]   [inst_1 : NormedAddCommGroup F] {μ :…
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_univ`：setIntegral_univ : ∫ᵛ x in
 univ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
-/
theorem setIntegral_add_compl (hs : MeasurableSet s) (hfi : μ.Integrable f) :
    ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] := by
  rw [← setIntegral_union disjoint_compl_right
    hs hs.compl hfi.integrableOn hfi.integrableOn, union_compl_self, setIntegral_univ]
/-
**MeasureTheory.VectorMeasure.setIntegral_compl** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：setIntegral_compl (hs : MeasurableSet s) (hfi : μ.Integrable f) : ∫ᵛ x in 
sᶜ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x in s, f x ∂[B; μ]
参数：hs : MeasurableSet s；hfi : μ.Integrable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_add_compl`：setIntegral_add_compl
 (hs : MeasurableSet s) (hfi : μ.Integrable f) : ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x i
n sᶜ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
theorem setIntegral_compl (hs : MeasurableSet s) (hfi : μ.Integrable f) :
    ∫ᵛ x in sᶜ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] - ∫ᵛ x in s, f x ∂[B; μ] := by
  rw [← setIntegral_add_compl (μ := μ) hs hfi, add_sub_cancel_left]

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ᵛ x in s, f x ∂[B; μ]`
defined as `∫ᵛ x, f x ∂[B; μ.restrict s]`. -/
/-
**MeasureTheory.VectorMeasure.integral_indicator** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：integral_indicator (hs : MeasurableSet s) : ∫ᵛ x, indicator s f x ∂[B; μ] 
= ∫ᵛ x in s, f x ∂[B; μ]
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_add_compl`：setIntegral_add_compl
 (hs : MeasurableSet s) (hfi : μ.Integrable f) : ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x i
n sᶜ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.IntegrableOn.integrable_indicator`：∀ {X : Ty
pe u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : NormedAdd
CommGroup E]   [inst_1 : NormedAddCommGroup F] {μ :…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `MeasureTheory.VectorMeasure.integral_congr_ae`：integral_congr_ae (h : f 
=ᵐ[μ.variation] g) : ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ]
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `indicator_ae_eq_restrict`：indicator_ae_eq_restrict (hs : MeasurableSet s
) : indicator s f =ᵐ[μ.restrict s] f
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `indicator_ae_eq_restrict_compl`：indicator_ae_eq_restrict_compl (hs : Mea
surableSet s) : indicator s f =ᵐ[μ.restrict sᶜ] 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero`：integral_zero : ∫ᵛ _, 0 ∂[B; 
μ] = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.integral_undef`：integral_undef (h : ¬ μ.Inte
grable f) : ∫ᵛ x, f x ∂[B; μ] = 0
· 使用定理 `MeasureTheory.VectorMeasure.integrable_indicator_iff`：integrable_indicat
or_iff (hs : MeasurableSet s) : μ.Integrable (indicator s f) ↔ μ.IntegrableOn f 
s

--- 原说明 ---
For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ᵛ x in s, f x ∂[B; μ]`
defined as `∫ᵛ x, f x ∂[B; μ.restrict s]`.
-/
theorem integral_indicator (hs : MeasurableSet s) :
    ∫ᵛ x, indicator s f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  by_cases hfi : μ.IntegrableOn f s; swap
  · rw [integral_undef hfi, integral_undef]
    rw [integrable_indicator_iff hs]
    simpa [transpose_restrict, variation_restrict hs] using hfi
  calc
    ∫ᵛ x, indicator s f x ∂[B; μ]
    _ = ∫ᵛ x in s, indicator s f x ∂[B; μ] + ∫ᵛ x in sᶜ, indicator s f x ∂[B; μ] :=
      (setIntegral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, 0 ∂[B; μ] := by
      apply congr_arg₂ (· + ·) (integral_congr_ae ?_) (integral_congr_ae ?_)
      · rw [variation_restrict hs]
        exact indicator_ae_eq_restrict hs
      · rw [variation_restrict hs.compl]
        exact indicator_ae_eq_restrict_compl hs
    _ = ∫ᵛ x in s, f x ∂[B; μ] := by simp
/-
**MeasureTheory.VectorMeasure.setIntegral_indicator** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：setIntegral_indicator (hs : MeasurableSet s) (ht : MeasurableSet t) : ∫ᵛ x
 in s, t.indicator f x ∂[B; μ] = ∫ᵛ x in s inter t, f x ∂[B; μ]
参数：hs : MeasurableSet s；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.integral_indicator`：integral_indicator (hs :
 MeasurableSet s) : ∫ᵛ x, indicator s f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.restrict_restrict`：restrict_restrict {s t : 
Set α} (hs : MeasurableSet s) (ht : MeasurableSet t) : (v.restrict t).restrict s
 = v.restrict (s inter t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem setIntegral_indicator (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ∫ᵛ x in s, t.indicator f x ∂[B; μ] = ∫ᵛ x in s ∩ t, f x ∂[B; μ] := by
  rw [integral_indicator ht, μ.restrict_restrict ht hs, Set.inter_comm]
/-
**MeasureTheory.VectorMeasure.setIntegral_congr_set** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：setIntegral_congr_set (hs : MeasurableSet s) (ht : MeasurableSet t) (hst :
 s =ᵐ[μ.variation] t) : ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in t, f x ∂[B; μ]
参数：hs : MeasurableSet s；ht : MeasurableSet t；hst : s =ᵐ[μ.variation] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.integral_indicator`：integral_indicator (hs :
 MeasurableSet s) : ∫ᵛ x, indicator s f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.integral_congr_ae`：integral_congr_ae (h : f 
=ᵐ[μ.variation] g) : ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem setIntegral_congr_set
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : s =ᵐ[μ.variation] t) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x in t, f x ∂[B; μ] := by
  rw [← integral_indicator hs, ← integral_indicator ht]
  apply integral_congr_ae
  filter_upwards [hst] with x hx
  replace hx : x ∈ s ↔ x ∈ t := by simpa using! hx
  simp [indicator]
  grind
/-
**MeasureTheory.VectorMeasure.integral_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：integral_piecewise [DecidablePred (· in s)] (hs : MeasurableSet s) (hf : μ
.IntegrableOn f s) (hg : μ.IntegrableOn g sᶜ) : ∫ᵛ x, s.piecewise f g x ∂[B; μ] 
= ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, g x ∂[B; μ]
参数：· in s；hs : MeasurableSet s；hf : μ.IntegrableOn f s；hg : μ.IntegrableOn g sᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_add_compl_eq_piecewise`：∀ {α : Type u_1} {M : Type u_4} [i
nst : AddZeroClass M] {s : Set α} [inst_1 : DecidablePred fun x => x ∈ s]   (f g
 : α → M), s.indicator f +…
· 使用定理 `MeasureTheory.VectorMeasure.integral_add`：integral_add (hf : μ.Integrabl
e f) (hg : μ.Integrable g) : ∫ᵛ x, (f + g) x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] + ∫ᵛ x,
 g x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.IntegrableOn.integrable_indicator`：∀ {X : Ty
pe u_2} {E : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : NormedAdd
CommGroup E]   [inst_1 : NormedAddCommGroup F] {μ :…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.VectorMeasure.integral_indicator`：integral_indicator (hs :
 MeasurableSet s) : ∫ᵛ x, indicator s f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ]
-/
theorem integral_piecewise [DecidablePred (· ∈ s)]
    (hs : MeasurableSet s) (hf : μ.IntegrableOn f s) (hg : μ.IntegrableOn g sᶜ) :
    ∫ᵛ x, s.piecewise f g x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] + ∫ᵛ x in sᶜ, g x ∂[B; μ] := by
  rw [← Set.indicator_add_compl_eq_piecewise,
    integral_add (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl),
    integral_indicator hs, integral_indicator hs.compl]
/-
**MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_ae_eq_zero** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_eq_zero_of_ae_eq_zero (ht_eq : forallᵐ x ∂μ.variation, x in t 
-> f x = 0) : ∫ᵛ x in t, f x ∂[B; μ] = 0
参数：ht_eq : forallᵐ x ∂μ.variation, x in t -> f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `MeasureTheory.VectorMeasure.integral_eq_zero_of_ae`：integral_eq_zero_of_
ae (hf : f =ᵐ[μ.variation] 0) : ∫ᵛ x, f x ∂[B; μ] = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.ae.congr_simp`：∀ {α : Type u_1} {F : Type u_3} [inst : Fun
Like F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   (μ μ_1 
: F), μ = μ_1 → M…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.integral_congr_ae`：integral_congr_ae (h : f 
=ᵐ[μ.variation] g) : ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.integral_undef`：integral_undef (h : ¬ μ.Inte
grable f) : ∫ᵛ x, f x ∂[B; μ] = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_eq_zero_of_ae_eq_zero
    (ht_eq : ∀ᵐ x ∂μ.variation, x ∈ t → f x = 0) :
    ∫ᵛ x in t, f x ∂[B; μ] = 0 := by
  by_cases ht : MeasurableSet t; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet ht]
  by_cases hf : AEStronglyMeasurable f (μ.restrict t).variation; swap
  · rw [integral_undef]
    contrapose hf
    exact hf.1
  simp only [variation_restrict ht] at hf
  have : ∫ᵛ x in t, hf.mk f x ∂[B; μ] = 0 := by
    refine integral_eq_zero_of_ae ?_
    simp only [variation_restrict ht]
    apply (ae_restrict_iff' ht).2
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  apply integral_congr_ae
  simp only [variation_restrict ht]
  exact hf.ae_eq_mk
/-
**MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_forall_eq_zero** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_eq_zero_of_forall_eq_zero (ht_eq : forall x in t, f x = 0) : ∫
ᵛ x in t, f x ∂[B; μ] = 0
参数：ht_eq : forall x in t, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_ae_eq_zero`：setIntegr
al_eq_zero_of_ae_eq_zero (ht_eq : forallᵐ x ∂μ.variation, x in t -> f x = 0) : ∫
ᵛ x in t, f x ∂[B; μ] = 0
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
-/
theorem setIntegral_eq_zero_of_forall_eq_zero (ht_eq : ∀ x ∈ t, f x = 0) :
    ∫ᵛ x in t, f x ∂[B; μ] = 0 :=
  setIntegral_eq_zero_of_ae_eq_zero (Eventually.of_forall ht_eq)
/-
**MeasureTheory.VectorMeasure.frequently_ae_ne_zero_of_setIntegral_ne_zero** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：frequently_ae_ne_zero_of_setIntegral_ne_zero (hU : ∫ᵛ x in t, f x ∂[B; μ] 
!= 0) : existsᶠ x in ae (μ.variation.restrict t), f x != 0
参数：hU : ∫ᵛ x in t, f x ∂[B; μ] != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `MeasureTheory.VectorMeasure.frequently_ae_ne_zero_of_integral_ne_zero`：f
requently_ae_ne_zero_of_integral_ne_zero (h : ∫ᵛ a, f a ∂[B; μ] != 0) : existsᶠ 
a in ae μ.variation, f a != 0
-/
theorem frequently_ae_ne_zero_of_setIntegral_ne_zero (hU : ∫ᵛ x in t, f x ∂[B; μ] ≠ 0) :
    ∃ᶠ x in ae (μ.variation.restrict t), f x ≠ 0 := by
  have ht : MeasurableSet t := by
    contrapose! hU
    simp [setIntegral_eq_zero_of_not_measurableSet hU]
  rw [← variation_restrict ht]
  exact frequently_ae_ne_zero_of_integral_ne_zero hU
/-
**MeasureTheory.VectorMeasure.exists_ne_zero_of_setIntegral_ne_zero** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：exists_ne_zero_of_setIntegral_ne_zero (hU : ∫ᵛ x in t, f x ∂[B; μ] != 0) :
 exists x, x in t ∧ f x != 0
参数：hU : ∫ᵛ x in t, f x ∂[B; μ] != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_forall_eq_zero`：setIn
tegral_eq_zero_of_forall_eq_zero (ht_eq : forall x in t, f x = 0) : ∫ᵛ x in t, f
 x ∂[B; μ] = 0
-/
theorem exists_ne_zero_of_setIntegral_ne_zero (hU : ∫ᵛ x in t, f x ∂[B; μ] ≠ 0) :
    ∃ x, x ∈ t ∧ f x ≠ 0 := by
  contrapose! hU; exact setIntegral_eq_zero_of_forall_eq_zero hU
/-
**MeasureTheory.VectorMeasure.setIntegral_of_variation_apply_eq_zero** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_of_variation_apply_eq_zero (f : X -> E) {s : Set X} (hs : μ.va
riation s = 0) : ∫ᵛ x in s, f x ∂[B; μ] = 0
参数：f : X -> E；hs : μ.variation s = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.VectorMeasure.variation_eq_zero`：∀ {X : Type u_1} {V : Typ
e u_2} {mX : MeasurableSpace X} [inst : TopologicalSpace V] [inst_1 : ENormedAdd
CommMonoid V]   [inst_2 : T2Space V…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero_vectorMeasure`：integral_zero_v
ectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.restrict_not_measurable`：restrict_not_measur
able {i : Set α} (hi : ¬MeasurableSet i) : v.restrict i = 0
-/
theorem setIntegral_of_variation_apply_eq_zero (f : X → E) {s : Set X}
    (hs : μ.variation s = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = 0 := by
  by_cases h's : MeasurableSet s; swap
  · simp [restrict_not_measurable μ h's]
  have : (μ.restrict s).variation = 0 := by
    rw [variation_restrict h's]
    apply Measure.restrict_eq_zero.2 hs
  have : μ.restrict s = 0 := variation_eq_zero.1 this
  simp [this]
/-
**MeasureTheory.VectorMeasure.setIntegral_dirac'** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：setIntegral_dirac' {mX : MeasurableSpace X} [CompleteSpace G] {a : X} {v :
 F} (hf : StronglyMeasurable f) {s : Set X} (hs : MeasurableSet s) [Decidable (a
 in s)] : ∫ᵛ x in s, f x ∂[B; VectorMeasure.dirac a v] = if a in s then B (f a) 
v else 0
参数：hf : StronglyMeasurable f；hs : MeasurableSet s；a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_dirac`：restrict_dirac {s : Set α} {
x : α} {m : M} (hs : MeasurableSet s) [Decidable (x in s)] : (dirac x m).restric
t s = if x in s then dirac x m e…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.VectorMeasure.integral_dirac'`：integral_dirac' [Measurable
Space X] [CompleteSpace G] {a : X} {v : F} (hfm : StronglyMeasurable f) : ∫ᵛ x, 
f x ∂[B; VectorMeasure.dirac a v]…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero_vectorMeasure`：integral_zero_v
ectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
-/
theorem setIntegral_dirac' {mX : MeasurableSpace X} [CompleteSpace G] {a : X} {v : F}
    (hf : StronglyMeasurable f) {s : Set X} (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫ᵛ x in s, f x ∂[B; VectorMeasure.dirac a v] = if a ∈ s then B (f a) v else 0 := by
  rw [restrict_dirac hs]
  split_ifs
  · exact integral_dirac' hf
  · exact integral_zero_vectorMeasure
/-
**MeasureTheory.VectorMeasure.setIntegral_dirac** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：setIntegral_dirac [MeasurableSpace X] [MeasurableSingletonClass X] [Comple
teSpace G] {a : X} {v : F} {s : Set X} (hs : MeasurableSet s) [Decidable (a in s
)] : ∫ᵛ x in s, f x ∂[B; VectorMeasure.dirac a v] = if a in s then B (f a) v els
e 0
参数：hs : MeasurableSet s；a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_dirac`：restrict_dirac {s : Set α} {
x : α} {m : M} (hs : MeasurableSet s) [Decidable (x in s)] : (dirac x m).restric
t s = if x in s then dirac x m e…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MeasureTheory.VectorMeasure.integral_dirac`：integral_dirac [MeasurableSp
ace X] [MeasurableSingletonClass X] [CompleteSpace G] {a : X} {v : F} : ∫ᵛ x, f 
x ∂[B; VectorMeasure.dirac a v] …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero_vectorMeasure`：integral_zero_v
ectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
-/
theorem setIntegral_dirac [MeasurableSpace X] [MeasurableSingletonClass X] [CompleteSpace G]
    {a : X} {v : F} {s : Set X} (hs : MeasurableSet s) [Decidable (a ∈ s)] :
    ∫ᵛ x in s, f x ∂[B; VectorMeasure.dirac a v] = if a ∈ s then B (f a) v else 0 := by
  rw [restrict_dirac hs]
  split_ifs
  · exact integral_dirac
  · exact integral_zero_vectorMeasure
/-
**MeasureTheory.VectorMeasure.integral_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.VectorMeasure`。
形式化陈述：integral_singleton' [CompleteSpace G] {a : X} (hf : StronglyMeasurable f) 
: ∫ᵛ a in {a}, f a ∂[B; μ] = B (f a) (μ {a})
参数：hf : StronglyMeasurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_singleton`：restrict_singleton {a : 
α} : v.restrict {a} = dirac a (v {a})
· 使用定理 `MeasureTheory.VectorMeasure.integral_dirac'`：integral_dirac' [Measurable
Space X] [CompleteSpace G] {a : X} {v : F} (hfm : StronglyMeasurable f) : ∫ᵛ x, 
f x ∂[B; VectorMeasure.dirac a v]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_singleton' [CompleteSpace G] {a : X} (hf : StronglyMeasurable f) :
    ∫ᵛ a in {a}, f a ∂[B; μ] = B (f a) (μ {a}) := by
  simp only [restrict_singleton, integral_dirac' hf]
/-
**MeasureTheory.VectorMeasure.integral_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory.VectorMeasure`。
形式化陈述：integral_singleton [MeasurableSingletonClass X] {a : X} [CompleteSpace G] 
: ∫ᵛ a in {a}, f a ∂[B; μ] = B (f a) (μ {a})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_singleton`：restrict_singleton {a : 
α} : v.restrict {a} = dirac a (v {a})
· 使用定理 `MeasureTheory.VectorMeasure.integral_dirac`：integral_dirac [MeasurableSp
ace X] [MeasurableSingletonClass X] [CompleteSpace G] {a : X} {v : F} : ∫ᵛ x, f 
x ∂[B; VectorMeasure.dirac a v] …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integral_singleton [MeasurableSingletonClass X] {a : X} [CompleteSpace G] :
    ∫ᵛ a in {a}, f a ∂[B; μ] = B (f a) (μ {a}) := by
  simp only [restrict_singleton, integral_dirac]
/-
**MeasureTheory.VectorMeasure.setIntegral_union_eq_left_of_ae** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_union_eq_left_of_ae (hs : MeasurableSet s) (ht : MeasurableSet
 t) (ht_eq : forallᵐ x ∂μ.variation.restrict t, f x = 0) : ∫ᵛ x in s union t, f 
x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ]
参数：hs : MeasurableSet s；ht : MeasurableSet t；ht_eq : forallᵐ x ∂μ.variation.rest
rict t, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.integral_indicator`：integral_indicator (hs :
 MeasurableSet s) : ∫ᵛ x, indicator s f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ]
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `MeasureTheory.VectorMeasure.integral_congr_ae`：integral_congr_ae (h : f 
=ᵐ[μ.variation] g) : ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ]
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
-/
theorem setIntegral_union_eq_left_of_ae (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ht_eq : ∀ᵐ x ∂μ.variation.restrict t, f x = 0) :
    ∫ᵛ x in s ∪ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  rw [← integral_indicator hs, ← integral_indicator (hs.union ht)]
  apply integral_congr_ae
  rw [ae_restrict_iff' ht] at ht_eq
  filter_upwards [ht_eq] with x hx
  classical
  simp only [indicator_apply, mem_union]
  grind
/-
**MeasureTheory.VectorMeasure.setIntegral_union_eq_left_of_forall** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_union_eq_left_of_forall (hs : MeasurableSet s) (ht : Measurabl
eSet t) (ht_eq : forall x in t, f x = 0) : ∫ᵛ x in s union t, f x ∂[B; μ] = ∫ᵛ x
 in s, f x ∂[B; μ]
参数：hs : MeasurableSet s；ht : MeasurableSet t；ht_eq : forall x in t, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_union_eq_left_of_ae`：setIntegral
_union_eq_left_of_ae (hs : MeasurableSet s) (ht : MeasurableSet t) (ht_eq : fora
llᵐ x ∂μ.variation.restrict t, f x = 0) : ∫ᵛ x in…
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem setIntegral_union_eq_left_of_forall (hs : MeasurableSet s) (ht : MeasurableSet t)
    (ht_eq : ∀ x ∈ t, f x = 0) : ∫ᵛ x in s ∪ t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  apply setIntegral_union_eq_left_of_ae hs ht
  rw [ae_restrict_iff' ht]
  filter_upwards with x using ht_eq x
/-
**MeasureTheory.VectorMeasure.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero** 是 M
athlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (hs : MeasurableSet s) (ht : 
MeasurableSet t) (hts : s subseteq t) (h't : forallᵐ x ∂μ.variation.restrict (t 
\ s), f x = 0) : ∫ᵛ x in t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ]
参数：hs : MeasurableSet s；ht : MeasurableSet t；hts : s subseteq t；h't : forallᵐ x 
∂μ.variation.restrict (t \ s), f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.union_sdiff_cancel`：union_sdiff_cancel {s t : Set α} (h : s subseteq
 t) : s union t \ s = t
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_union_eq_left_of_ae`：setIntegral
_union_eq_left_of_ae (hs : MeasurableSet s) (ht : MeasurableSet t) (ht_eq : fora
llᵐ x ∂μ.variation.restrict t, f x = 0) : ∫ᵛ x in…
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
-/
theorem setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hts : s ⊆ t) (h't : ∀ᵐ x ∂μ.variation.restrict (t \ s), f x = 0) :
    ∫ᵛ x in t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  rwa [← union_sdiff_cancel hts, setIntegral_union_eq_left_of_ae hs (ht.diff hs)]

/-- If a function vanishes on `t \ s` with `s ⊆ t`, then its integrals on `s`
and `t` coincide. -/
/-
**MeasureTheory.VectorMeasure.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hs : MeasurableSet s) (h
t : MeasurableSet t) (hts : s subseteq t) (h't : forall x in t \ s, f x = 0) : ∫
ᵛ x in t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ]
参数：hs : MeasurableSet s；ht : MeasurableSet t；hts : s subseteq t；h't : forall x i
n t \ s, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
`：setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (hs : MeasurableSet s) (ht : Meas
urableSet t) (hts : s subseteq t) (h't : forallᵐ x ∂μ.variatio…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
If a function vanishes on `t \ s` with `s ⊆ t`, then its integrals on `s`
and `t` coincide.
-/
theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hts : s ⊆ t)
    (h't : ∀ x ∈ t \ s, f x = 0) : ∫ᵛ x in t, f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ] := by
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs ht hts
  apply (ae_restrict_iff' (ht.diff hs)).2
  filter_upwards with x using h't x

/-- If a function vanishes almost everywhere on `sᶜ`, then its integral on `s`
coincides with its integral on the whole space. -/
/-
**MeasureTheory.VectorMeasure.setIntegral_eq_integral_of_ae_compl_eq_zero** 是 Ma
thlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_eq_integral_of_ae_compl_eq_zero (hs : MeasurableSet s) (h : fo
rallᵐ x ∂μ.variation, x ∉ s -> f x = 0) : ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B
; μ]
参数：hs : MeasurableSet s；h : forallᵐ x ∂μ.variation, x ∉ s -> f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_univ`：setIntegral_univ : ∫ᵛ x in
 univ, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero
`：setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (hs : MeasurableSet s) (ht : Meas
urableSet t) (hts : s subseteq t) (h't : forallᵐ x ∂μ.variatio…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a function vanishes almost everywhere on `sᶜ`, then its integral on `s`
coincides with its integral on the whole space.
-/
theorem setIntegral_eq_integral_of_ae_compl_eq_zero (hs : MeasurableSet s)
    (h : ∀ᵐ x ∂μ.variation, x ∉ s → f x = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] := by
  symm
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero hs MeasurableSet.univ (subset_univ _)
  apply (ae_restrict_iff' (MeasurableSet.univ.diff hs)).2
  filter_upwards [h] with x hx h'x using hx h'x.2

/-- If a function vanishes on `sᶜ`, then its integral on `s` coincides with its integral on the
whole space. -/
/-
**MeasureTheory.VectorMeasure.setIntegral_eq_integral_of_forall_compl_eq_zero** 
是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：setIntegral_eq_integral_of_forall_compl_eq_zero (hs : MeasurableSet s) (h 
: forall x, x ∉ s -> f x = 0) : ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
参数：hs : MeasurableSet s；h : forall x, x ∉ s -> f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_integral_of_ae_compl_eq_zero`
：setIntegral_eq_integral_of_ae_compl_eq_zero (hs : MeasurableSet s) (h : forallᵐ
 x ∂μ.variation, x ∉ s -> f x = 0) : ∫ᵛ x in s, f x ∂[B; μ] =…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α

--- 原说明 ---
If a function vanishes on `sᶜ`, then its integral on `s` coincides with its inte
gral on the
whole space.
-/
theorem setIntegral_eq_integral_of_forall_compl_eq_zero (hs : MeasurableSet s)
    (h : ∀ x, x ∉ s → f x = 0) :
    ∫ᵛ x in s, f x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ] :=
  setIntegral_eq_integral_of_ae_compl_eq_zero hs (Eventually.of_forall h)
/-
**MeasureTheory.VectorMeasure.setIntegral_const** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.VectorMeasure`。
形式化陈述：setIntegral_const [CompleteSpace G] [IsFiniteMeasure (μ.variation.restrict
 s)] (c : E) : ∫ᵛ _ in s, c ∂[B; μ] = B c (μ s)
参数：μ.variation.restrict s；c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `MeasureTheory.VectorMeasure.integral_const`：integral_const [CompleteSpac
e G] [IsFiniteMeasure μ.variation] (c : E) : ∫ᵛ _ : X, c ∂[B; μ] = B c (μ univ)
· 使用定理 `MeasureTheory.VectorMeasure.restrict_apply`：restrict_apply {i : Set α} (
hi : MeasurableSet i) {j : Set α} (hj : MeasurableSet j) : v.restrict i j = v (j
 inter i)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_const [CompleteSpace G] [IsFiniteMeasure (μ.variation.restrict s)]
    (c : E) : ∫ᵛ _ in s, c ∂[B; μ] = B c (μ s) := by
  by_cases hs : MeasurableSet s
  · have : IsFiniteMeasure (μ.restrict s).variation := by
      rwa [variation_restrict hs]
    rw [integral_const, restrict_apply _ hs MeasurableSet.univ, univ_inter]
  · simp [setIntegral_eq_zero_of_not_measurableSet hs, μ.not_measurable hs]

@[simp]
/-
**MeasureTheory.VectorMeasure.integral_indicator_const** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_indicator_const [CompleteSpace G] (e : E) ⦃s : Set X⦄ [IsFiniteMe
asure (μ.variation.restrict s)] (s_meas : MeasurableSet s) : ∫ᵛ x, s.indicator (
fun _ : X => e) x ∂[B; μ] = B e (μ s)
参数：e : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.integral_indicator`：integral_indicator (hs :
 MeasurableSet s) : ∫ᵛ x, indicator s f x ∂[B; μ] = ∫ᵛ x in s, f x ∂[B; μ]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_const`：setIntegral_const [Comple
teSpace G] [IsFiniteMeasure (μ.variation.restrict s)] (c : E) : ∫ᵛ _ in s, c ∂[B
; μ] = B c (μ s)
-/
theorem integral_indicator_const [CompleteSpace G]
    (e : E) ⦃s : Set X⦄ [IsFiniteMeasure (μ.variation.restrict s)]
    (s_meas : MeasurableSet s) :
    ∫ᵛ x, s.indicator (fun _ : X ↦ e) x ∂[B; μ] = B e (μ s) := by
  rw [integral_indicator s_meas, ← setIntegral_const]
/-
**MeasureTheory.VectorMeasure.setIntegral_map** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.VectorMeasure`。
形式化陈述：setIntegral_map {β : Type*} [MeasurableSpace β] {φ : X -> β} (hφ : Measura
ble φ) {f : β -> E} {s : Set β} (hs : MeasurableSet s) (hfm : AEStronglyMeasurab
le f ((μ.restrict (φ ⁻¹' s)).variation.map φ)) (hfi' : μ.Integrable (f ∘ φ)) : ∫
ᵛ y in s, f y ∂[B; μ.map φ] = ∫ᵛ x in φ ⁻¹' s, f (φ x) ∂[B; μ]
参数：hφ : Measurable φ；hs : MeasurableSet s；hfm : AEStronglyMeasurable f ((μ.restr
ict (φ ⁻¹' s)).variation.map φ)；hfi' : μ.Integrable (f ∘ φ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.restrict_map`：restrict_map {f : α -> β} (hf 
: Measurable f) {s : Set β} (hs : MeasurableSet s) : (v.map f).restrict s = (v.r
estrict (f ⁻¹' s)).map f
· 使用定理 `MeasureTheory.VectorMeasure.integral_map`：integral_map {β : Type*} [Meas
urableSpace β] {φ : X -> β} (hφ : Measurable φ) {f : β -> E} (hfm : AEStronglyMe
asurable f (μ.variation.map φ)…
· 使用定理 `MeasureTheory.VectorMeasure.Integrable.integrableOn`：∀ {X : Type u_2} {E
 : Type u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : NormedAddCommGroup 
E]   [inst_1 : NormedAddCommGroup F] {μ :…
-/
theorem setIntegral_map {β : Type*} [MeasurableSpace β]
    {φ : X → β} (hφ : Measurable φ) {f : β → E} {s : Set β} (hs : MeasurableSet s)
    (hfm : AEStronglyMeasurable f ((μ.restrict (φ ⁻¹' s)).variation.map φ))
    (hfi' : μ.Integrable (f ∘ φ)) :
    ∫ᵛ y in s, f y ∂[B; μ.map φ] = ∫ᵛ x in φ ⁻¹' s, f (φ x) ∂[B; μ] := by
  rw [restrict_map μ hφ hs, integral_map hφ hfm hfi'.integrableOn]
/-
**MeasureTheory.VectorMeasure._root_.MeasurableEmbedding.setIntegral_map_vectorM
easure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.setIntegral_map_vectorMeasure {β : Type*} [MeasurableSpace β]
    {φ : X → β} {f : β → E} (hφ : MeasurableEmbedding φ) {s : Set β} (hs : MeasurableSet s) :
    ∫ᵛ y in s, f y ∂[B; μ.map φ] = ∫ᵛ x in φ ⁻¹' s, f (φ x) ∂[B; μ] := by
  rw [restrict_map μ hφ.measurable hs, hφ.integral_map_vectorMeasure]
/-
**MeasureTheory.VectorMeasure._root_.Topology.IsClosedEmbedding.setIntegral_map_
vectorMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Topology.IsClosedEmbedding.setIntegral_map_vectorMeasure
    [TopologicalSpace X] [BorelSpace X] {β : Type*}
    [MeasurableSpace β] [TopologicalSpace β] [BorelSpace β] {φ : X → β} {f : β → E} {s : Set β}
    (hs : MeasurableSet s) (hφ : IsClosedEmbedding φ) :
    ∫ᵛ y in s, f y ∂[B; μ.map φ] = ∫ᵛ x in φ ⁻¹' s, f (φ x) ∂[B; μ] :=
  hφ.measurableEmbedding.setIntegral_map_vectorMeasure hs
/-
**MeasureTheory.VectorMeasure.setIntegral_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.VectorMeasure`。
形式化陈述：setIntegral_map_equiv {β : Type*} [MeasurableSpace β] {e : X ≃ᵐ β} {f : β 
-> E} {s : Set β} (hs : MeasurableSet s) : ∫ᵛ y in s, f y ∂[B; μ.map e] = ∫ᵛ x i
n e ⁻¹' s, f (e x) ∂[B; μ]
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasurableEmbedding.setIntegral_map_vectorMeasure`：∀ {X : Type u_2} {E :
 Type u_3} {F : Type u_4} {G : Type u_5} {mX : MeasurableSpace X} [inst : Normed
AddCommGroup E]   [inst_1 : NormedAddCo…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem setIntegral_map_equiv {β : Type*} [MeasurableSpace β] {e : X ≃ᵐ β} {f : β → E} {s : Set β}
    (hs : MeasurableSet s) :
    ∫ᵛ y in s, f y ∂[B; μ.map e] = ∫ᵛ x in e ⁻¹' s, f (e x) ∂[B; μ] :=
  e.measurableEmbedding.setIntegral_map_vectorMeasure hs
/-
**MeasureTheory.VectorMeasure.continuousLinearMap_apply_integral** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：continuousLinearMap_apply_integral [CompleteSpace G] [CompleteSpace H] {C 
: G ->L[Real] H} (hf : Integrable f μ.variation) : C (∫ᵛ y, f y ∂[B; μ]) = ∫ᵛ y,
 f y ∂[((compL Real F G H C) ∘L B); μ]
参数：hf : Integrable f μ.variation。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.induction`：∀ {α : Type u_1} {E : Type u_4} [ins
t : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Measur
e α}   (P : (α → E) → Pr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.VectorMeasure.integral_indicator_const`：integral_indicator
_const [CompleteSpace G] (e : E) ⦃s : Set X⦄ [IsFiniteMeasure (μ.variation.restr
ict s)] (s_meas : MeasurableSet s) : ∫ᵛ x,…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.integral_fun_add`：integral_fun_add (hf : μ.I
ntegrable f) (hg : μ.Integrable g) : ∫ᵛ x, f x + g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
 + ∫ᵛ x, g x ∂[B; μ]
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `MeasureTheory.VectorMeasure.continuous_integral`：continuous_integral : C
ontinuous fun f : X ->₁[μ.variation] E => ∫ᵛ a, f a ∂[B; μ]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.integral_congr_ae`：integral_congr_ae (h : f 
=ᵐ[μ.variation] g) : ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ]
-/
theorem continuousLinearMap_apply_integral
    [CompleteSpace G] [CompleteSpace H]
    {C : G →L[ℝ] H} (hf : Integrable f μ.variation) :
    C (∫ᵛ y, f y ∂[B; μ]) = ∫ᵛ y, f y ∂[((compL ℝ F G H C) ∘L B); μ] := by
  apply hf.induction (P := fun f ↦ C (∫ᵛ y, f y ∂[B; μ]) = ∫ᵛ y, f y ∂[((compL ℝ F G H C) ∘L B); μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    simp [integral_indicator_const _ hs]
  · intro f g _ f_int g_int hf hg
    simp only [Pi.add_apply]
    simp [integral_fun_add, f_int, g_int, hf, hg]
  · apply isClosed_eq
    · apply C.continuous.comp continuous_integral
    · exact continuous_integral
  · intro f g hfg _ hf
    rw [← integral_congr_ae hfg, ← integral_congr_ae hfg, hf]
/-
**MeasureTheory.VectorMeasure.integral_continuousLinearMap_comp** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：integral_continuousLinearMap_comp {f : X -> H} {C : H ->L[Real] E} (hf : I
ntegrable f μ.variation) : ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ]
参数：hf : Integrable f μ.variation。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Integrable.induction`：∀ {α : Type u_1} {E : Type u_4} [ins
t : MeasurableSpace α] [inst_1 : NormedAddCommGroup E] {μ : MeasureTheory.Measur
e α}   (P : (α → E) → Pr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.VectorMeasure.integral_indicator_const`：integral_indicator
_const [CompleteSpace G] (e : E) ⦃s : Set X⦄ [IsFiniteMeasure (μ.variation.restr
ict s)] (s_meas : MeasurableSet s) : ∫ᵛ x,…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `MeasureTheory.VectorMeasure.integral_fun_add`：integral_fun_add (hf : μ.I
ntegrable f) (hg : μ.Integrable g) : ∫ᵛ x, f x + g x ∂[B; μ] = ∫ᵛ x, f x ∂[B; μ]
 + ∫ᵛ x, g x ∂[B; μ]
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.integral_congr_ae`：integral_congr_ae (h : f 
=ᵐ[μ.variation] g) : ∫ᵛ x, f x ∂[B; μ] = ∫ᵛ x, g x ∂[B; μ]
· 使用定理 `ContinuousLinearMap.coeFn_compLp`：coeFn_compLp (L : E ->SL[σ] F) (f : Lp
 E p μ) : forallᵐ a ∂μ, (L.compLp f) a = L (f a)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MeasureTheory.VectorMeasure.continuous_integral`：continuous_integral : C
ontinuous fun f : X ->₁[μ.variation] E => ∫ᵛ a, f a ∂[B; μ]
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
（共 34 条，此处仅展示前 30 条）
-/
theorem integral_continuousLinearMap_comp
    {f : X → H} {C : H →L[ℝ] E} (hf : Integrable f μ.variation) :
    ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ] := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  apply hf.induction (P := fun f ↦ ∫ᵛ y, C (f y) ∂[B; μ] = ∫ᵛ y, f y ∂[B ∘L C; μ])
  · intro c s hs hc
    have : IsFiniteMeasure (μ.variation.restrict s) := ⟨by simpa⟩
    rw [integral_indicator_const _ hs]
    have : (fun y ↦ C (s.indicator (fun x ↦ c) y)) = s.indicator (fun x ↦ C c) := by
      ext; simp only [indicator]; grind
    simp_rw [this]
    rw [integral_indicator_const _ hs]
    rfl
  · intro f g _ f_int g_int hf hg
    simp only [Pi.add_apply, _root_.map_add]
    rw [integral_fun_add (C.integrable_comp f_int) (C.integrable_comp g_int), hf, hg,
      integral_fun_add f_int g_int]
  · apply isClosed_eq
    · have I (f : Lp H 1 μ.variation) : ∫ᵛ x, C (f x) ∂[B; μ] = ∫ᵛ x, (C.compLp f) x ∂[B; μ] :=
        (integral_congr_ae (coeFn_compLp _ _)).symm
      simp_rw [I]
      exact continuous_integral.comp (C.compLpL 1 μ.variation).continuous
    · exact continuous_integral
  · intro f g hfg _ hf
    have : ∀ᵐ x ∂μ.variation, C (f x) = C (g x) := by
      filter_upwards [hfg] with x hx using by simp [hx]
    rw [← integral_congr_ae hfg, ← integral_congr_ae this, hf]
/-
**MeasureTheory.VectorMeasure.enorm_setIntegral_le_of_enorm_le_const_ae** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：enorm_setIntegral_le_of_enorm_le_const_ae {C : Real>=0∞} (hC : forallᵐ x ∂
μ.variation.restrict s, ‖f x‖ₑ <= C) : ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ <= C * ‖B‖ₑ * μ
.variation s
参数：hC : forallᵐ x ∂μ.variation.restrict s, ‖f x‖ₑ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.VectorMeasure.enorm_integral_le_of_enorm_le_const`：enorm_i
ntegral_le_of_enorm_le_const {C : Real>=0∞} (h : forallᵐ x ∂μ.variation, ‖f x‖ₑ 
<= C) : ‖∫ᵛ x, f x ∂[B; μ]‖ₑ <= C * ‖B‖ₑ * μ.variatio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem enorm_setIntegral_le_of_enorm_le_const_ae {C : ℝ≥0∞}
    (hC : ∀ᵐ x ∂μ.variation.restrict s, ‖f x‖ₑ ≤ C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ ≤ C * ‖B‖ₑ * μ.variation s := by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  rw [← variation_restrict hs] at hC
  apply (enorm_integral_le_of_enorm_le_const hC).trans
  rw [variation_restrict hs, Measure.restrict_apply MeasurableSet.univ]
  simp
/-
**MeasureTheory.VectorMeasure.enorm_setIntegral_le_of_enorm_le_const** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：enorm_setIntegral_le_of_enorm_le_const {C : Real>=0∞} (hC : forall x in s,
 ‖f x‖ₑ <= C) : ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ <= C * ‖B‖ₑ * μ.variation s
参数：hC : forall x in s, ‖f x‖ₑ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.VectorMeasure.enorm_setIntegral_le_of_enorm_le_const_ae`：e
norm_setIntegral_le_of_enorm_le_const_ae {C : Real>=0∞} (hC : forallᵐ x ∂μ.varia
tion.restrict s, ‖f x‖ₑ <= C) : ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ <…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `enorm_zero`：∀ {E : Type u_8} [inst : TopologicalSpace E] [inst_1 : ESemi
normedAddMonoid E], ‖0‖ₑ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
theorem enorm_setIntegral_le_of_enorm_le_const {C : ℝ≥0∞}
    (hC : ∀ x ∈ s, ‖f x‖ₑ ≤ C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ ≤ C * ‖B‖ₑ * μ.variation s := by
  by_cases hs : MeasurableSet s; swap
  · simp [setIntegral_eq_zero_of_not_measurableSet hs]
  apply enorm_setIntegral_le_of_enorm_le_const_ae
  apply (ae_restrict_iff' hs).2
  filter_upwards with x using hC x
/-
**MeasureTheory.VectorMeasure.norm_setIntegral_le_of_norm_le_const_ae** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：norm_setIntegral_le_of_norm_le_const_ae {C : Real} [h : IsFiniteMeasure (μ
.variation.restrict s)] (hC : forallᵐ x ∂μ.variation.restrict s, ‖f x‖ <= C) : ‖
∫ᵛ x in s, f x ∂[B; μ]‖ <= C * ‖B‖ * μ.variation.real s
参数：μ.variation.restrict s；hC : forallᵐ x ∂μ.variation.restrict s, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const`：norm_inte
gral_le_of_norm_le_const [IsFiniteMeasure μ.variation] {C : Real} (h : forallᵐ x
 ∂μ.variation, ‖f x‖ <= C) : ‖∫ᵛ x, f x ∂[B; μ]‖ <=…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict`：variation_restrict (hs :
 MeasurableSet s) : (μ.restrict s).variation = μ.variation.restrict s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
-/
theorem norm_setIntegral_le_of_norm_le_const_ae {C : ℝ}
    [h : IsFiniteMeasure (μ.variation.restrict s)]
    (hC : ∀ᵐ x ∂μ.variation.restrict s, ‖f x‖ ≤ C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ ≤ C * ‖B‖ * μ.variation.real s := by
  by_cases hs : MeasurableSet s; swap
  · simp only [setIntegral_eq_zero_of_not_measurableSet hs, norm_zero]
    by_cases h's : μ.variation s = 0
    · simp [Measure.real, h's]
    · have : NeBot (ae (μ.variation.restrict s)) := by simpa using h's
      obtain ⟨x, hx⟩ : ∃ x, ‖f x‖ ≤ C := hC.exists
      have : 0 ≤ C := le_trans (norm_nonneg _) hx
      positivity
  rw [← variation_restrict hs] at hC h
  apply (norm_integral_le_of_norm_le_const hC).trans_eq
  simp [variation_restrict hs]
/-
**MeasureTheory.VectorMeasure.norm_setIntegral_le_of_norm_le_const** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：norm_setIntegral_le_of_norm_le_const {C : Real} [h : IsFiniteMeasure (μ.va
riation.restrict s)] (hC : forall x in s, ‖f x‖ <= C) : ‖∫ᵛ x in s, f x ∂[B; μ]‖
 <= C * ‖B‖ * μ.variation.real s
参数：μ.variation.restrict s；hC : forall x in s, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.VectorMeasure.restrict_empty`：restrict_empty : v.restrict 
∅ = 0
· 使用定理 `MeasureTheory.VectorMeasure.integral_zero_vectorMeasure`：integral_zero_v
ectorMeasure : ∫ᵛ x, f x ∂[B; (0 : VectorMeasure X F)] = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MeasureTheory.measureReal_empty`：∀ {α : Type u_1} {x : MeasurableSpace α
} {μ : MeasureTheory.Measure α}, μ.real ∅ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.norm_setIntegral_le_of_norm_le_const_ae`：nor
m_setIntegral_le_of_norm_le_const_ae {C : Real} [h : IsFiniteMeasure (μ.variatio
n.restrict s)] (hC : forallᵐ x ∂μ.variation.restrict s, ‖…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem`：ae_restrict_mem (hs : MeasurableSet s) : 
forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_eq_zero_of_not_measurableSet`：se
tIntegral_eq_zero_of_not_measurableSet (hs : ¬MeasurableSet s) : ∫ᵛ x in s, f x 
∂[B; μ] = 0
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `MeasureTheory.measureReal_nonneg`：∀ {α : Type u_1} {x : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α}, 0 ≤ μ.real s
-/
theorem norm_setIntegral_le_of_norm_le_const {C : ℝ}
    [h : IsFiniteMeasure (μ.variation.restrict s)]
    (hC : ∀ x ∈ s, ‖f x‖ ≤ C) :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ ≤ C * ‖B‖ * μ.variation.real s := by
  rcases eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
  · simp
  by_cases hs : MeasurableSet s; swap
  · simp only [setIntegral_eq_zero_of_not_measurableSet hs, norm_zero]
    have : 0 ≤ C := le_trans (norm_nonneg _) (hC x hx)
    positivity
  apply norm_setIntegral_le_of_norm_le_const_ae
  filter_upwards [ae_restrict_mem hs] with x hx using hC x hx
/-
**MeasureTheory.VectorMeasure.enorm_setIntegral_le_lintegral_enorm** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：enorm_setIntegral_le_lintegral_enorm : ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ <= ‖B‖ₑ *
 ∫⁻ x in s, ‖f x‖ₑ ∂μ.variation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.VectorMeasure.enorm_integral_le_lintegral_enorm`：enorm_int
egral_le_lintegral_enorm : ‖∫ᵛ a, f a ∂[B; μ]‖ₑ <= ‖B‖ₑ * ∫⁻ a, ‖f a‖ₑ ∂μ.variat
ion
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `ENNReal.instIsOrderedMonoid`：IsOrderedMonoid ENNReal
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict_le`：variation_restrict_le
 : (μ.restrict s).variation <= μ.variation.restrict s
-/
theorem enorm_setIntegral_le_lintegral_enorm :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ ≤ ‖B‖ₑ * ∫⁻ x in s, ‖f x‖ₑ ∂μ.variation := by
  grw [enorm_integral_le_lintegral_enorm, variation_restrict_le]
/-
**MeasureTheory.VectorMeasure.enorm_setIntegral_le_lintegral_enorm_transpose** 是
 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：enorm_setIntegral_le_lintegral_enorm_transpose : ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ
 <= ∫⁻ x in s, ‖f x‖ₑ ∂(μ.transpose B).variation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.VectorMeasure.enorm_integral_le_lintegral_enorm_transpose`
：enorm_integral_le_lintegral_enorm_transpose : ‖∫ᵛ a, f a ∂[B; μ]‖ₑ <= ∫⁻ a, ‖f 
a‖ₑ ∂(μ.transpose B).variation
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.VectorMeasure.transpose_restrict`：transpose_restrict (s : 
Set X) : (μ.restrict s).transpose B = (μ.transpose B).restrict s
· 使用定理 `MeasureTheory.lintegral_mono_fn'`：∀ {α : Type u_1} {m : MeasurableSpace 
α} {μ ν : MeasureTheory.Measure α},   μ ≤ ν → ∀ ⦃f g : α → ENNReal⦄, (∀ (x : α),
 f x ≤ g x) → ∫⁻ (a : …
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict_le`：variation_restrict_le
 : (μ.restrict s).variation <= μ.variation.restrict s
-/
theorem enorm_setIntegral_le_lintegral_enorm_transpose :
    ‖∫ᵛ x in s, f x ∂[B; μ]‖ₑ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂(μ.transpose B).variation := by
  grw [enorm_integral_le_lintegral_enorm_transpose, transpose_restrict,variation_restrict_le]
/-
**MeasureTheory.VectorMeasure.hasSum_setIntegral_iUnion_nat** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.VectorMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem hasSum_setIntegral_iUnion_nat {s : ℕ → Set X}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    HasSum (fun n ↦ ∫ᵛ x in s n, f x ∂[B; μ]) (∫ᵛ x in ⋃ n, s n, f x ∂[B; μ]) := by
  by_cases hG : CompleteSpace G; swap
  · simp [integral_of_not_completeSpace hG]
  have I : ∑' i, ‖B‖ₑ * ∫⁻ x in s i, ‖f x‖ₑ ∂μ.variation < ∞ := calc
    ∑' i, ‖B‖ₑ * ∫⁻ x in s i, ‖f x‖ₑ ∂μ.variation
    _ = ‖B‖ₑ * ∫⁻ x in (⋃ i, s i), ‖f x‖ₑ ∂μ.variation := by
      rw [ENNReal.tsum_mul_left, lintegral_iUnion hm hd]
    _ < ∞ := by
      simp only [VectorMeasure.IntegrableOn, VectorMeasure.Integrable,
        variation_restrict (MeasurableSet.iUnion hm)] at hfi
      exact ENNReal.mul_lt_top (by simp) hfi.2
  have : Summable (fun n ↦ ∫ᵛ x in s n, f x ∂[B; μ]) := by
    apply Summable.of_enorm (lt_of_le_of_lt _ I).ne
    gcongr
    exact enorm_setIntegral_le_lintegral_enorm
  apply (Summable.hasSum_iff_tendsto_nat this).2
  simp_rw [tendsto_iff_edist_tendsto_0, edist_eq_enorm_sub, enorm_sub_rev]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (ENNReal.tendsto_sum_nat_add _ I.ne) (by positivity) (fun N ↦ ?_)
  have : ⋃ n, s n = (⋃ n ∈ Finset.range N, s n) ∪ (⋃ n, s (n + N)) := by
    ext x
    have : (∃ i, x ∈ s (i + N)) ↔ (∃ i ≥ N, x ∈ s i) :=
      ⟨fun ⟨i, hi⟩ ↦ ⟨i + N, by grind⟩, fun ⟨i, hi, h'i⟩ ↦ ⟨i - N, by grind⟩⟩
    simp only [mem_iUnion, Finset.mem_range, mem_union, exists_prop, this, ge_iff_le]
    grind
  rw [this, setIntegral_union]; rotate_left
  · simp only [Finset.mem_range, disjoint_iUnion_right, disjoint_iUnion_left]
    intro i j hi
    apply hd (by grind)
  · apply MeasurableSet.biUnion (Finset.countable_toSet _) (fun i hi ↦ hm i)
  · apply MeasurableSet.iUnion (fun i ↦ hm _)
  · apply hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  · apply hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  rw [setIntegral_biUnion_finset]; rotate_left
  · exact fun i hi ↦ hm i
  · exact fun i hi j hj hij ↦ hd hij
  · exact fun i hi ↦ hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
  simp only [add_sub_cancel_left]
  apply enorm_setIntegral_le_lintegral_enorm.trans_eq
  rw [lintegral_iUnion (fun i ↦ hm _), ENNReal.tsum_mul_left]
  exact fun i j hij ↦ hd (by grind)
/-
**MeasureTheory.VectorMeasure.hasSum_setIntegral_iUnion** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.VectorMeasure`。
形式化陈述：hasSum_setIntegral_iUnion {ι : Type*} [Countable ι] {s : ι -> Set X} (hm :
 forall i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s)) (hfi : μ.Integra
bleOn f (⋃ i, s i)) : HasSum (fun n => ∫ᵛ x in s n, f x ∂[B; μ]) (∫ᵛ x in ⋃ n, s
 n, f x ∂[B; μ])
参数：hm : forall i, MeasurableSet (s i)；hd : Pairwise (Disjoint on s)；hfi : μ.Inte
grableOn f (⋃ i, s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.VectorMeasure.setIntegral_iUnion_fintype`：setIntegral_iUni
on_fintype {ι : Type*} [Fintype ι] {s : ι -> Set X} (hs : forall i, MeasurableSe
t (s i)) (h's : Pairwise (Disjoint on s)) (h…
· 使用定理 `MeasureTheory.VectorMeasure.IntegrableOn.mono`：∀ {X : Type u_2} {E : Typ
e u_3} {F : Type u_4} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]   [
inst_1 : NormedAddCommGroup F] {μ :…
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `hasSum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] [inst_2 : Fintype β] (f : β → α)   (L : optParam 
(Sum…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.iUnion_comp`：iUnion_comp {f : ι -> ι₂} (hf : Surject
ive f) (g : ι₂ -> Set α) : ⋃ x, g (f x) = ⋃ y, g y
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Equiv.hasSum_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst :
 AddCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {a : α} (e : γ ≃ β
), Has…
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.SetIntegral.0.MeasureTheory
.VectorMeasure.hasSum_setIntegral_iUnion_nat`：∀ {X : Type u_2} {E : Type u_3} {F
 : Type u_4} {G : Type u_5} {mX : MeasurableSpace X} [inst : NormedAddCommGroup 
E]   [inst_1 : NormedAddCo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem hasSum_setIntegral_iUnion {ι : Type*} [Countable ι] {s : ι → Set X}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    HasSum (fun n ↦ ∫ᵛ x in s n, f x ∂[B; μ]) (∫ᵛ x in ⋃ n, s n, f x ∂[B; μ]) := by
  rcases finite_or_infinite ι with hι | hι
  · let : Fintype ι := Fintype.ofFinite ι
    have : ∫ᵛ x in ⋃ n, s n, f x ∂[B; μ] = ∑ i, ∫ᵛ x in s i, f x ∂[B; μ] := by
      rw [setIntegral_iUnion_fintype hm hd (fun i ↦ ?_)]
      exact hfi.mono (MeasurableSet.iUnion hm) (by simp [subset_iUnion s])
    rw [this]
    apply hasSum_fintype
  obtain ⟨e⟩ : Nonempty (ι ≃ ℕ) := nonempty_equiv_of_countable
  rw [← e.symm.surjective.iUnion_comp, ← e.symm.hasSum_iff]
  apply hasSum_setIntegral_iUnion_nat (fun i ↦ hm _) (fun i j hij ↦ hd (by simp [hij]))
  rwa [e.symm.surjective.iUnion_comp]
/-
**MeasureTheory.VectorMeasure.integral_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.VectorMeasure`。
形式化陈述：integral_iUnion {ι : Type*} [Countable ι] {s : ι -> Set X} (hm : forall i,
 MeasurableSet (s i)) (hd : Pairwise (Disjoint on s)) (hfi : μ.IntegrableOn f (⋃
 i, s i)) : ∫ᵛ x in ⋃ n, s n, f x ∂[B; μ] = ∑' n, ∫ᵛ x in s n, f x ∂[B; μ]
参数：hm : forall i, MeasurableSet (s i)；hd : Pairwise (Disjoint on s)；hfi : μ.Inte
grableOn f (⋃ i, s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `MeasureTheory.VectorMeasure.hasSum_setIntegral_iUnion`：hasSum_setIntegra
l_iUnion {ι : Type*} [Countable ι] {s : ι -> Set X} (hm : forall i, MeasurableSe
t (s i)) (hd : Pairwise (Disjoint on s)) (h…
-/
theorem integral_iUnion {ι : Type*} [Countable ι] {s : ι → Set X} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hfi : μ.IntegrableOn f (⋃ i, s i)) :
    ∫ᵛ x in ⋃ n, s n, f x ∂[B; μ] = ∑' n, ∫ᵛ x in s n, f x ∂[B; μ] :=
  (HasSum.tsum_eq (hasSum_setIntegral_iUnion hm hd hfi)).symm
/-
**MeasureTheory.VectorMeasure.setIntegral_toSignedMeasure** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.VectorMeasure`。
形式化陈述：∀ {X : Type u_2} {G : Type u_5} {mX : MeasurableSpace X} [inst : NormedAdd
CommGroup G] [inst_1 : NormedSpace ℝ G]   {μ : MeasureTheory.Measure X} [inst_2 
: MeasureTheory.IsFiniteMeasure μ] {f : X → G} {s : Set X},   MeasurableSet s → 
∫ᵛ (x : X) in s, f x ∂<•μ.toSignedMeasure = ∫ (x : X) in s, f x ∂μ
参数：x : X；x : X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.VectorMeasure.integral_toSignedMeasure`：∀ {X : Type u_2} {
G : Type u_6} {mX : MeasurableSpace X} [inst : NormedAddCommGroup G] [inst_1 : N
ormedSpace ℝ G]   {μ : MeasureTheory.Measu…
· 使用定理 `MeasureTheory.VectorMeasure.restrict_toSignedMeasure`：restrict_toSignedM
easure {μ : Measure α} [IsFiniteMeasure μ] {s : Set α} (hs : MeasurableSet s) : 
μ.toSignedMeasure.restrict s = (μ.restrict…
-/
@[simp] theorem setIntegral_toSignedMeasure {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → G} {s : Set X} (hs : MeasurableSet s) :
    ∫ᵛ x in s, f x ∂<•μ.toSignedMeasure = ∫ x in s, f x ∂μ := by
  rw [← integral_toSignedMeasure, restrict_toSignedMeasure hs]

/-- If `f` is integrable, then `∫ᵛ x in s, f x ∂[B; μ]` is absolutely continuous in `s`:
it tends to zero as `μ.variation s` tends to zero. -/
/-
**MeasureTheory.VectorMeasure.Integrable.tendsto_setIntegral_nhds_zero** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.VectorMeasure.Integrable`。
形式化陈述：∀ {X : Type u_2} {E : Type u_3} {F : Type u_4} {G : Type u_5} {mX : Measur
ableSpace X} [inst : NormedAddCommGroup E]   [inst_1 : NormedAddCommGroup F] [in
st_2 : NormedAddCommGroup G] {μ : MeasureTheory.VectorMeasure X F} {f : X → E}  
 [inst_3 : NormedSpace ℝ E] [inst_4 : NormedSpace ℝ F] [inst_5 : NormedSpace ℝ G
] {B : E →L[ℝ] F →L[ℝ] G}   {ι : Type u_7},   μ.Integrable f →     ∀ {l : Filter
 ι} {s : ι → Set X},       Filter.Tendsto (⇑μ.variation ∘ s) l (nhds 0) → Filter
.Tendsto (fun i => ∫ᵛ (x : X) in s i, f x ∂[B; μ]) l (nhds 0)
参数：⇑μ.variation ∘ s；nhds 0；fun i => ∫ᵛ (x : X) in s i, f x ∂[B; μ]；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `ENNReal.Tendsto.const_mul`：∀ {α : Type u_1} {f : Filter α} {m : α → ENNR
eal} {a b : ENNReal},   Filter.Tendsto m f (nhds b) → b ≠ 0 ∨ a ≠ ⊤ → Filter.Ten
dsto (fun b => …
· 使用定理 `MeasureTheory.tendsto_setLIntegral_zero`：tendsto_setLIntegral_zero {ι} {
f : α -> Real>=0∞} (h : ∫⁻ x, f x ∂μ != ∞) {l : Filter ι} {s : ι -> Set α} (hl :
 Tendsto (μ ∘ s) l (𝓝 0)) : T…
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.VectorMeasure.enorm_integral_le_lintegral_enorm`：enorm_int
egral_le_lintegral_enorm : ‖∫ᵛ a, f a ∂[B; μ]‖ₑ <= ‖B‖ₑ * ∫⁻ a, ‖f a‖ₑ ∂μ.variat
ion
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is integrable, then `∫ᵛ x in s, f x ∂[B; μ]` is absolutely continuous in 
`s`:
it tends to zero as `μ.variation s` tends to zero.
-/
theorem Integrable.tendsto_setIntegral_nhds_zero {ι : Type*}
    (hf : μ.Integrable f) {l : Filter ι} {s : ι → Set X}
    (hs : Tendsto (μ.variation ∘ s) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫ᵛ x in s i, f x ∂[B; μ]) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [← coe_nnnorm, ← NNReal.coe_zero, NNReal.tendsto_coe, ← ENNReal.tendsto_coe,
    ENNReal.coe_zero]
  have : Tendsto (fun i ↦ ‖B‖ₑ * ∫⁻ (x : X) in s i, ‖f x‖ₑ ∂μ.variation) l (𝓝 (‖B‖ₑ * 0)) :=
    ENNReal.Tendsto.const_mul (tendsto_setLIntegral_zero (ne_of_lt hf.2) hs) (by simp)
  rw [mul_zero] at this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun i ↦ zero_le)
  intro i
  apply enorm_integral_le_lintegral_enorm.trans
  dsimp
  gcongr
  exact variation_restrict_le

/-- If `F i → f` in `L1`, then `∫ᵛ x in s, F i x ∂[B; μ] → ∫ᵛ x in s, f x ∂[B; μ]`. -/
/-
**MeasureTheory.VectorMeasure.tendsto_setIntegral_of_L1** 是 Mathlib 中的一个引理，位于命名空
间 `MeasureTheory.VectorMeasure`。
形式化陈述：tendsto_setIntegral_of_L1 {ι} (f : X -> E) (hfi : AEStronglyMeasurable f μ
.variation) {F : ι -> X -> E} {l : Filter ι} (hFi : forallᶠ i in l, μ.Integrable
 (F i)) (hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ.variation) l (𝓝 0)) (s :
 Set X) : Tendsto (fun i => ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; 
μ]))
参数：f : X -> E；hfi : AEStronglyMeasurable f μ.variation；hFi : forallᶠ i in l, μ.I
ntegrable (F i)；hF : Tendsto (fun i => ∫⁻ x, ‖F i x - f x‖ₑ ∂μ.variation) l (𝓝 0
)；s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.VectorMeasure.tendsto_integral_of_L1`：tendsto_integral_of_
L1 {ι} (f : X -> E) (hfi : AEStronglyMeasurable f μ.variation) {F : ι -> X -> E}
 {l : Filter ι} (hFi : forallᶠ i in l, μ…
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_measure`：mono_measure {ν : Measu
re α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ) : AEStronglyMeasurable[m] 
f ν
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `MeasureTheory.VectorMeasure.variation_restrict_le`：variation_restrict_le
 : (μ.restrict s).variation <= μ.variation.restrict s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.VectorMeasure.Integrable.restrict`：∀ {X : Type u_2} {E : T
ype u_4} {F : Type u_5} {mX : MeasurableSpace X} [inst : NormedAddCommGroup E]  
 [inst_1 : NormedAddCommGroup F] {f :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.eLpNorm_mono_measure`：eLpNorm_mono_measure (f : α -> ε) (h
μν : ν <= μ) : eLpNorm f p ν <= eLpNorm f p μ

--- 原说明 ---
If `F i → f` in `L1`, then `∫ᵛ x in s, F i x ∂[B; μ] → ∫ᵛ x in s, f x ∂[B; μ]`.
-/
lemma tendsto_setIntegral_of_L1 {ι} (f : X → E)
    (hfi : AEStronglyMeasurable f μ.variation) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i))
    (hF : Tendsto (fun i ↦ ∫⁻ x, ‖F i x - f x‖ₑ ∂μ.variation) l (𝓝 0))
    (s : Set X) :
    Tendsto (fun i ↦ ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ])) := by
  refine tendsto_integral_of_L1 f ?_ ?_ ?_
  · apply hfi.mono_measure
    grw [variation_restrict_le, Measure.restrict_le_self]
  · filter_upwards [hFi] with i hi using hi.restrict
  · simp_rw [← eLpNorm_one_eq_lintegral_enorm] at hF ⊢
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hF (fun _ ↦ zero_le)
      (fun i ↦ ?_)
    apply eLpNorm_mono_measure
    grw [variation_restrict_le]
    apply Measure.restrict_le_self

/-- If `F i → f` in `L1`, then `∫ᵛ x in s, F i x ∂[B; μ] → ∫ᵛ x in s, f x ∂[B; μ]`. -/
/-
**MeasureTheory.VectorMeasure.tendsto_setIntegral_of_L1'** 是 Mathlib 中的一个引理，位于命名
空间 `MeasureTheory.VectorMeasure`。
形式化陈述：tendsto_setIntegral_of_L1' {ι} (f : X -> E) (hfi : AEStronglyMeasurable f 
μ.variation) {F : ι -> X -> E} {l : Filter ι} (hFi : forallᶠ i in l, μ.Integrabl
e (F i)) (hF : Tendsto (fun i => eLpNorm (F i - f) 1 μ.variation) l (𝓝 0)) (s : 
Set X) : Tendsto (fun i => ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ
]))
参数：f : X -> E；hfi : AEStronglyMeasurable f μ.variation；hFi : forallᶠ i in l, μ.I
ntegrable (F i)；hF : Tendsto (fun i => eLpNorm (F i - f) 1 μ.variation) l (𝓝 0)；
s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `MeasureTheory.VectorMeasure.tendsto_setIntegral_of_L1`：tendsto_setIntegr
al_of_L1 {ι} (f : X -> E) (hfi : AEStronglyMeasurable f μ.variation) {F : ι -> X
 -> E} {l : Filter ι} (hFi : forallᶠ i in l…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MeasureTheory.eLpNorm_one_eq_lintegral_enorm`：eLpNorm_one_eq_lintegral_e
norm {f : α -> ε} : eLpNorm f 1 μ = ∫⁻ x, ‖f x‖ₑ ∂μ

--- 原说明 ---
If `F i → f` in `L1`, then `∫ᵛ x in s, F i x ∂[B; μ] → ∫ᵛ x in s, f x ∂[B; μ]`.
-/
lemma tendsto_setIntegral_of_L1' {ι} (f : X → E)
    (hfi : AEStronglyMeasurable f μ.variation) {F : ι → X → E}
    {l : Filter ι} (hFi : ∀ᶠ i in l, μ.Integrable (F i))
    (hF : Tendsto (fun i ↦ eLpNorm (F i - f) 1 μ.variation) l (𝓝 0))
    (s : Set X) :
    Tendsto (fun i ↦ ∫ᵛ x in s, F i x ∂[B; μ]) l (𝓝 (∫ᵛ x in s, f x ∂[B; μ])) := by
  refine tendsto_setIntegral_of_L1 f hfi hFi ?_ s
  simp_rw [eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply] at hF
  exact hF

end MeasureTheory.VectorMeasure

