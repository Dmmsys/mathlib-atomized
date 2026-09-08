/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Measure spaces

The definition of a measure and a measure space are in `MeasureTheory.MeasureSpaceDef`, with
only a few basic properties. This file provides many more properties of these objects.
This separation allows the measurability tactic to import only the file `MeasureSpaceDef`, and to
be available in `MeasureSpace` (through `MeasurableSpace`).

Given a measurable space `α`, a measure on `α` is a function that sends measurable sets to the
extended nonnegative reals that satisfies the following conditions:
1. `μ ∅ = 0`;
2. `μ` is countably additive. This means that the measure of a countable union of pairwise disjoint
   sets is equal to the measure of the individual sets.

Every measure can be canonically extended to an outer measure, so that it assigns values to
all subsets, not just the measurable subsets. On the other hand, a measure that is countably
additive on measurable sets can be restricted to measurable sets to obtain a measure.
In this file a measure is defined to be an outer measure that is countably additive on
measurable sets, with the additional assumption that the outer measure is the canonical
extension of the restricted measure.

Measures on `α` form a complete lattice, and are closed under scalar multiplication with `ℝ≥0∞`.

Given a measure, the null sets are the sets where `μ s = 0`, where `μ` denotes the corresponding
outer measure (so `s` might not be measurable). We can then define the completion of `μ` as the
measure on the least `σ`-algebra that also contains all null sets, by defining the measure to be `0`
on the null sets.

## Main statements

* `completion` is the completion of a measure to all null measurable sets.
* `Measure.ofMeasurable` and `OuterMeasure.toMeasure` are two important ways to define a measure.

## Implementation notes

Given `μ : Measure α`, `μ s` is the value of the *outer measure* applied to `s`.
This conveniently allows us to apply the measure to sets without proving that they are measurable.
We get countable subadditivity for all sets, but only countable additivity for measurable sets.

You often don't want to define a measure via its constructor.
Two ways that are sometimes more convenient:
* `Measure.ofMeasurable` is a way to define a measure by only giving its value on measurable sets
  and proving the properties (1) and (2) mentioned above.
* `OuterMeasure.toMeasure` is a way of obtaining a measure from an outer measure by showing that
  all measurable sets in the measurable space are Carathéodory measurable.

To prove that two measures are equal, there are multiple options:
* `ext`: two measures are equal if they are equal on all measurable sets.
* `ext_of_generateFrom_of_iUnion`: two measures are equal if they are equal on a π-system generating
  the measurable sets, if the π-system contains a spanning increasing sequence of sets where the
  measures take finite value (in particular the measures are σ-finite). This is a special case of
  the more general `ext_of_generateFrom_of_cover`
* `ext_of_generate_finite`: two finite measures are equal if they are equal on a π-system
  generating the measurable sets. This is a special case of `ext_of_generateFrom_of_iUnion` using
  `C ∪ {univ}`, but is easier to work with.

A `MeasureSpace` is a class that is a measurable space with a canonical measure.
The measure is denoted `volume`.

## References

* <https://en.wikipedia.org/wiki/Measure_(mathematics)>
* <https://en.wikipedia.org/wiki/Complete_measure>
* <https://en.wikipedia.org/wiki/Almost_everywhere>

## Tags

measure, almost everywhere, measure space, completion, null set, null measurable set
-/

@[expose] public section

noncomputable section

open Set

open Filter hiding map

open Function MeasurableSpace Topology Filter ENNReal NNReal Interval MeasureTheory
open scoped symmDiff

variable {α β γ δ ι R R' : Type*}

namespace MeasureTheory

section

variable {m : MeasurableSpace α} {μ μ₁ μ₂ : Measure α} {s s₁ s₂ t : Set α}

/-
**MeasureTheory.ae_isMeasurablyGenerated** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y`。
形式化陈述：ae_isMeasurablyGenerated : IsMeasurablyGenerated (ae μ)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.exists_measurable_superset_of_null`：exists_measurable_supe
rset_of_null (h : μ s = 0) : exists t, s subseteq t ∧ MeasurableSet t ∧ μ t = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.compl_mem_ae_iff`：compl_mem_ae_iff {s : Set α} : sᶜ in ae 
μ ↔ μ s = 0
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
-/
instance ae_isMeasurablyGenerated : IsMeasurablyGenerated (ae μ) :=
  ⟨fun _s hs =>
    let ⟨t, hst, htm, htμ⟩ := exists_measurable_superset_of_null hs
    ⟨tᶜ, compl_mem_ae_iff.2 htμ, htm.compl, compl_subset_comm.1 hst⟩⟩

/-- See also `MeasureTheory.ae_restrict_uIoc_iff`. -/
/-
**MeasureTheory.ae_uIoc_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_uIoc_iff [LinearOrder α] {a b : α} {P : α -> Prop} : (forallᵐ x ∂μ, x i
n Ι a b -> P x) ↔ (forallᵐ x ∂μ, x in Ioc a b -> P x) ∧ forallᵐ x ∂μ, x in Ioc b
 a -> P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Set.uIoc_eq_union`：uIoc_eq_union : Ι a b = Ioc a b union Ioc b a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
See also `MeasureTheory.ae_restrict_uIoc_iff`.
-/
theorem ae_uIoc_iff [LinearOrder α] {a b : α} {P : α → Prop} :
    (∀ᵐ x ∂μ, x ∈ Ι a b → P x) ↔ (∀ᵐ x ∂μ, x ∈ Ioc a b → P x) ∧ ∀ᵐ x ∂μ, x ∈ Ioc b a → P x := by
  simp only [uIoc_eq_union, mem_union, or_imp, eventually_and]
/-
**MeasureTheory.measure_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ union s
₂) = μ s₁ + μ s₂
参数：hd : Disjoint s₁ s₂；h : MeasurableSet s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_union₀`：measure_union₀ (ht : NullMeasurableSet t μ
) (hd : AEDisjoint μ s t) : μ (s union t) = μ s + μ t
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
theorem measure_union (hd : Disjoint s₁ s₂) (h : MeasurableSet s₂) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀ h.nullMeasurableSet hd.aedisjoint
/-
**MeasureTheory.measure_union'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁) : μ (s₁ union 
s₂) = μ s₁ + μ s₂
参数：hd : Disjoint s₁ s₂；h : MeasurableSet s₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_union₀'`：measure_union₀' (hs : NullMeasurableSet s
 μ) (hd : AEDisjoint μ s t) : μ (s union t) = μ s + μ t
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
theorem measure_union' (hd : Disjoint s₁ s₂) (h : MeasurableSet s₁) : μ (s₁ ∪ s₂) = μ s₁ + μ s₂ :=
  measure_union₀' h.nullMeasurableSet hd.aedisjoint
/-
**MeasureTheory.measure_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_inter_add_sdiff (s : Set α) (ht : MeasurableSet t) : μ (s inter t)
 + μ (s \ t) = μ s
参数：s : Set α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_inter_add_sdiff₀`：measure_inter_add_sdiff₀ (s : Se
t α) (ht : NullMeasurableSet t μ) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measure_inter_add_sdiff (s : Set α) (ht : MeasurableSet t) : μ (s ∩ t) + μ (s \ t) = μ s :=
  measure_inter_add_sdiff₀ _ ht.nullMeasurableSet

@[deprecated (since := "2026-06-03")] alias measure_inter_add_diff := measure_inter_add_sdiff
/-
**MeasureTheory.measure_sdiff_add_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_sdiff_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s \ t) + μ
 (s inter t) = μ s
参数：s : Set α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
-/
theorem measure_sdiff_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s \ t) + μ (s ∩ t) = μ s :=
  (add_comm _ _).trans (measure_inter_add_sdiff s ht)

@[deprecated (since := "2026-06-03")] alias measure_diff_add_inter := measure_sdiff_add_inter
/-
**MeasureTheory.measure_sdiff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_sdiff_eq_top (hs : μ s = ∞) (ht : μ t != ∞) : μ (s \ t) = ∞
参数：hs : μ s = ∞；ht : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_sdiff_union`：subset_sdiff_union (s t : Set α) : s subseteq s 
\ t union t
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.add_lt_top`：∀ {a b : ENNReal}, a + b < ⊤ ↔ a < ⊤ ∧ b < ⊤
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
-/
theorem measure_sdiff_eq_top (hs : μ s = ∞) (ht : μ t ≠ ∞) : μ (s \ t) = ∞ := by
  contrapose! hs
  exact ((measure_mono (subset_sdiff_union s t)).trans_lt
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hs.lt_top, ht.lt_top⟩))).ne

@[deprecated (since := "2026-06-03")] alias measure_diff_eq_top := measure_sdiff_eq_top
/-
**MeasureTheory.measure_union_add_inter** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_union_add_inter (s : Set α) (ht : MeasurableSet t) : μ (s union t)
 + μ (s inter t) = μ s + μ t
参数：s : Set α；ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `Set.union_inter_cancel_right`：union_inter_cancel_right {s t : Set α} : (
s union t) inter t = t
· 使用定理 `Set.union_sdiff_right`：union_sdiff_right {s t : Set α} : (s union t) \ t
 = s \ t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `AddSemigroup.to_isAssociative`：∀ {α : Type u_1} [inst : AddSemigroup α],
 Std.Associative fun x1 x2 => x1 + x2
· 使用定理 `IsAddCommutative.is_comm`：∀ {M : Type u_2} {inst : Add M} [self : IsAddC
ommutative M], Std.Commutative fun x1 x2 => x1 + x2
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem measure_union_add_inter (s : Set α) (ht : MeasurableSet t) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [← measure_inter_add_sdiff (s ∪ t) ht, Set.union_inter_cancel_right, union_sdiff_right, ←
    measure_inter_add_sdiff s ht]
  ac_rfl
/-
**MeasureTheory.measure_union_add_inter'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：measure_union_add_inter' (hs : MeasurableSet s) (t : Set α) : μ (s union t
) + μ (s inter t) = μ s + μ t
参数：hs : MeasurableSet s；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.measure_union_add_inter`：measure_union_add_inter (s : Set 
α) (ht : MeasurableSet t) : μ (s union t) + μ (s inter t) = μ s + μ t
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem measure_union_add_inter' (hs : MeasurableSet s) (t : Set α) :
    μ (s ∪ t) + μ (s ∩ t) = μ s + μ t := by
  rw [union_comm, inter_comm, measure_union_add_inter t hs, add_comm]
/-
**MeasureTheory.measure_symmDiff_eq** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_symmDiff_eq (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t
 μ) : μ (s ∆ t) = μ (s \ t) + μ (t \ s)
参数：hs : NullMeasurableSet s μ；ht : NullMeasurableSet t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_union₀`：measure_union₀ (ht : NullMeasurableSet t μ
) (hd : AEDisjoint μ s t) : μ (s union t) = μ s + μ t
· 使用定理 `MeasureTheory.NullMeasurableSet.diff`：∀ {α : Type u_2} {m0 : MeasurableS
pace α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasura
bleSet s μ → MeasureTheory…
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `disjoint_sdiff_sdiff`：disjoint_sdiff_sdiff : Disjoint (x \ y) (y \ x)
-/
lemma measure_symmDiff_eq (hs : NullMeasurableSet s μ) (ht : NullMeasurableSet t μ) :
    μ (s ∆ t) = μ (s \ t) + μ (t \ s) := by
  simpa only [symmDiff_def, sup_eq_union]
    using measure_union₀ (ht.diff hs) disjoint_sdiff_sdiff.aedisjoint
/-
**MeasureTheory.measure_symmDiff_le** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_symmDiff_le (s t u : Set α) : μ (s ∆ u) <= μ (s ∆ t) + μ (t ∆ u)
参数：s t u : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.OuterMeasure.mono`：∀ {α : Type u_2} (self : MeasureTheory.
OuterMeasure α) {s₁ s₂ : Set α}, s₁ ⊆ s₂ → self.measureOf s₁ ≤ self.measureOf s₂
· 使用定理 `symmDiff_triangle`：symmDiff_triangle : a ∆ c <= a ∆ b ⊔ b ∆ c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma measure_symmDiff_le (s t u : Set α) :
    μ (s ∆ u) ≤ μ (s ∆ t) + μ (t ∆ u) :=
  le_trans (μ.mono <| symmDiff_triangle s t u) (measure_union_le (s ∆ t) (t ∆ u))
/-
**MeasureTheory.measure_symmDiff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_symmDiff_eq_top (hs : μ s != ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞
参数：hs : μ s != ∞；ht : μ t = ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono_top`：measure_mono_top (h : s₁ subseteq s₂) (h
₁ : μ s₁ = ∞) : μ s₂ = ∞
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `MeasureTheory.measure_sdiff_eq_top`：measure_sdiff_eq_top (hs : μ s = ∞) 
(ht : μ t != ∞) : μ (s \ t) = ∞
-/
theorem measure_symmDiff_eq_top (hs : μ s ≠ ∞) (ht : μ t = ∞) : μ (s ∆ t) = ∞ :=
  measure_mono_top subset_union_right (measure_sdiff_eq_top ht hs)
/-
**MeasureTheory.measure_add_measure_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：measure_add_measure_compl (h : MeasurableSet s) : μ s + μ sᶜ = μ univ
参数：h : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_add_measure_compl₀`：measure_add_measure_compl₀ {s 
: Set α} (hs : NullMeasurableSet s μ) : μ s + μ sᶜ = μ univ
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measure_add_measure_compl (h : MeasurableSet s) : μ s + μ sᶜ = μ univ :=
  measure_add_measure_compl₀ h.nullMeasurableSet
/-
**MeasureTheory.measure_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_biUnion {s : Set β} {f : β -> Set α} (hs : s.Countable) (hd : s.Pa
irwiseDisjoint f) (h : forall b in s, MeasurableSet (f b)) : μ (⋃ b in s, f b) =
 ∑' p : s, μ (f p)
参数：hs : s.Countable；hd : s.PairwiseDisjoint f；h : forall b in s, MeasurableSet (
f b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_biUnion₀`：measure_biUnion₀ {s : Set β} {f : β -> S
et α} (hs : s.Countable) (hd : s.Pairwise (AEDisjoint μ on f)) (h : forall b in 
s, NullMeasurableSet…
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measure_biUnion₀ {s : Set β} {f : β → Set α} (hs : s.Countable)
    (hd : s.Pairwise (AEDisjoint μ on f)) (h : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) := by
  have := hs.toEncodable
  rw [biUnion_eq_iUnion]
  exact measure_iUnion₀ (hd.on_injective Subtype.coe_injective fun x => x.2) fun x => h x x.2
/-
**MeasureTheory.measure_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_biUnion {s : Set β} {f : β -> Set α} (hs : s.Countable) (hd : s.Pa
irwiseDisjoint f) (h : forall b in s, MeasurableSet (f b)) : μ (⋃ b in s, f b) =
 ∑' p : s, μ (f p)
参数：hs : s.Countable；hd : s.PairwiseDisjoint f；h : forall b in s, MeasurableSet (
f b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_biUnion₀`：measure_biUnion₀ {s : Set β} {f : β -> S
et α} (hs : s.Countable) (hd : s.Pairwise (AEDisjoint μ on f)) (h : forall b in 
s, NullMeasurableSet…
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measure_biUnion {s : Set β} {f : β → Set α} (hs : s.Countable) (hd : s.PairwiseDisjoint f)
    (h : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑' p : s, μ (f p) :=
  measure_biUnion₀ hs hd.aedisjoint fun b hb => (h b hb).nullMeasurableSet
/-
**MeasureTheory.measure_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_sUnion {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjo
int) (h : forall s in S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s
参数：Set α；hs : S.Countable；hd : S.Pairwise Disjoint；h : forall s in S, Measurable
Set s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `MeasureTheory.measure_biUnion`：measure_biUnion {s : Set β} {f : β -> Set
 α} (hs : s.Countable) (hd : s.PairwiseDisjoint f) (h : forall b in s, Measurabl
eSet (f b)) : μ (⋃ …
-/
theorem measure_sUnion₀ {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise (AEDisjoint μ))
    (h : ∀ s ∈ S, NullMeasurableSet s μ) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion₀ hs hd h]
/-
**MeasureTheory.measure_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_sUnion {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjo
int) (h : forall s in S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s
参数：Set α；hs : S.Countable；hd : S.Pairwise Disjoint；h : forall s in S, Measurable
Set s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_biUnion`：sUnion_eq_biUnion {s : Set (Set α)} : ⋃₀ s = ⋃ (i
 : Set α) (_ : i in s), i
· 使用定理 `MeasureTheory.measure_biUnion`：measure_biUnion {s : Set β} {f : β -> Set
 α} (hs : s.Countable) (hd : s.PairwiseDisjoint f) (h : forall b in s, Measurabl
eSet (f b)) : μ (⋃ …
-/
theorem measure_sUnion {S : Set (Set α)} (hs : S.Countable) (hd : S.Pairwise Disjoint)
    (h : ∀ s ∈ S, MeasurableSet s) : μ (⋃₀ S) = ∑' s : S, μ s := by
  rw [sUnion_eq_biUnion, measure_biUnion hs hd h]
/-
**MeasureTheory.measure_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_biUnion_finset {s : Finset ι} {f : ι -> Set α} (hd : PairwiseDisjo
int (↑s) f) (hm : forall b in s, MeasurableSet (f b)) : μ (⋃ b in s, f b) = ∑ p 
in s, μ (f p)
参数：hd : PairwiseDisjoint (↑s) f；hm : forall b in s, MeasurableSet (f b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_biUnion_finset₀`：measure_biUnion_finset₀ {s : Fins
et ι} {f : ι -> Set α} (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : forall
 b in s, NullMeasurableSet …
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measure_biUnion_finset₀ {s : Finset ι} {f : ι → Set α}
    (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : ∀ b ∈ s, NullMeasurableSet (f b) μ) :
    μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) := by
  rw [← Finset.sum_attach, Finset.attach_eq_univ, ← tsum_fintype (L := .unconditional s)]
  exact measure_biUnion₀ s.countable_toSet hd hm
/-
**MeasureTheory.measure_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：measure_biUnion_finset {s : Finset ι} {f : ι -> Set α} (hd : PairwiseDisjo
int (↑s) f) (hm : forall b in s, MeasurableSet (f b)) : μ (⋃ b in s, f b) = ∑ p 
in s, μ (f p)
参数：hd : PairwiseDisjoint (↑s) f；hm : forall b in s, MeasurableSet (f b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_biUnion_finset₀`：measure_biUnion_finset₀ {s : Fins
et ι} {f : ι -> Set α} (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : forall
 b in s, NullMeasurableSet …
· 使用定理 `Set.PairwiseDisjoint.aedisjoint`：∀ {ι : Type u_1} {α : Type u_2} {m : Me
asurableSpace α} {μ : MeasureTheory.Measure α} {f : ι → Set α} {s : Set ι},   s.
PairwiseDisjoint f → …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measure_biUnion_finset {s : Finset ι} {f : ι → Set α} (hd : PairwiseDisjoint (↑s) f)
    (hm : ∀ b ∈ s, MeasurableSet (f b)) : μ (⋃ b ∈ s, f b) = ∑ p ∈ s, μ (f p) :=
  measure_biUnion_finset₀ hd.aedisjoint fun b hb => (hm b hb).nullMeasurableSet

/-- The measure of an a.e. disjoint union (even uncountable) of null-measurable sets is at least
the sum of the measures of the sets. -/
/-
**MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：tsum_meas_le_meas_iUnion_of_disjoint {ι : Type*} {_ : MeasurableSpace α} (
μ : Measure α) {As : ι -> Set α} (As_mble : forall i : ι, MeasurableSet (As i)) 
(As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) <= μ (⋃ i, As i)
参数：μ : Measure α；As_mble : forall i : ι, MeasurableSet (As i)；As_disj : Pairwise
 (Disjoint on As)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint₀`：tsum_meas_le_meas_i
Union_of_disjoint₀ {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α) {As : ι -
> Set α} (As_mble : forall i : ι, NullMea…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t

--- 原说明 ---
The measure of an a.e. disjoint union (even uncountable) of null-measurable sets
 is at least
the sum of the measures of the sets.
-/
theorem tsum_meas_le_meas_iUnion_of_disjoint₀ {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, NullMeasurableSet (As i) μ)
    (As_disj : Pairwise (AEDisjoint μ on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) := by
  rw [ENNReal.tsum_eq_iSup_sum, iSup_le_iff]
  intro s
  simp only [← measure_biUnion_finset₀ (fun _i _hi _j _hj hij => As_disj hij) fun i _ => As_mble i]
  gcongr
  exact iUnion_subset fun _ ↦ Subset.rfl

/-- The measure of a disjoint union (even uncountable) of measurable sets is at least the sum of
the measures of the sets. -/
/-
**MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：tsum_meas_le_meas_iUnion_of_disjoint {ι : Type*} {_ : MeasurableSpace α} (
μ : Measure α) {As : ι -> Set α} (As_mble : forall i : ι, MeasurableSet (As i)) 
(As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) <= μ (⋃ i, As i)
参数：μ : Measure α；As_mble : forall i : ι, MeasurableSet (As i)；As_disj : Pairwise
 (Disjoint on As)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tsum_meas_le_meas_iUnion_of_disjoint₀`：tsum_meas_le_meas_i
Union_of_disjoint₀ {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α) {As : ι -
> Set α} (As_mble : forall i : ι, NullMea…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t

--- 原说明 ---
The measure of a disjoint union (even uncountable) of measurable sets is at leas
t the sum of
the measures of the sets.
-/
theorem tsum_meas_le_meas_iUnion_of_disjoint {ι : Type*} {_ : MeasurableSpace α} (μ : Measure α)
    {As : ι → Set α} (As_mble : ∀ i : ι, MeasurableSet (As i))
    (As_disj : Pairwise (Disjoint on As)) : (∑' i, μ (As i)) ≤ μ (⋃ i, As i) :=
  tsum_meas_le_meas_iUnion_of_disjoint₀ μ (fun i ↦ (As_mble i).nullMeasurableSet)
    (fun _ _ h ↦ Disjoint.aedisjoint (As_disj h))

/-- If `s` is a countable set, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
/-
**MeasureTheory.tsum_measure_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：tsum_measure_preimage_singleton {s : Set β} (hs : s.Countable) {f : α -> β
} (hf : forall y in s, MeasurableSet (f ⁻¹' {y})) : (∑' b : s, μ (f ⁻¹' {↑b})) =
 μ (f ⁻¹' s)
参数：hs : s.Countable；hf : forall y in s, MeasurableSet (f ⁻¹' {y})。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_preimage_singleton`：biUnion_preimage_singleton (f : α -> β) 
(s : Set β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
· 使用定理 `MeasureTheory.measure_biUnion`：measure_biUnion {s : Set β} {f : β -> Set
 α} (hs : s.Countable) (hd : s.PairwiseDisjoint f) (h : forall b in s, Measurabl
eSet (f b)) : μ (⋃ …
· 使用定理 `Set.pairwiseDisjoint_fiber`：pairwiseDisjoint_fiber (f : ι -> α) (s : Set
 α) : s.PairwiseDisjoint fun a => f ⁻¹' {a}

--- 原说明 ---
If `s` is a countable set, then the measure of its preimage can be found as the 
sum of measures
of the fibers `f ⁻¹' {y}`.
-/
theorem tsum_measure_preimage_singleton {s : Set β} (hs : s.Countable) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑' b : s, μ (f ⁻¹' {↑b})) = μ (f ⁻¹' s) := by
  rw [← Set.biUnion_preimage_singleton, measure_biUnion hs (pairwiseDisjoint_fiber f s) hf]
/-
**MeasureTheory.measure_preimage_eq_zero_iff_of_countable** 是 Mathlib 中的一个引理，位于命
名空间 `MeasureTheory`。
形式化陈述：measure_preimage_eq_zero_iff_of_countable {s : Set β} {f : α -> β} (hs : s
.Countable) : μ (f ⁻¹' s) = 0 ↔ forall x in s, μ (f ⁻¹' {x}) = 0
参数：hs : s.Countable。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.biUnion_preimage_singleton`：biUnion_preimage_singleton (f : α -> β) 
(s : Set β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
· 使用定理 `MeasureTheory.measure_biUnion_null_iff`：measure_biUnion_null_iff {I : Se
t ι} (hI : I.Countable) {s : ι -> Set α} : μ (⋃ i in I, s i) = 0 ↔ forall i in I
, μ (s i) = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma measure_preimage_eq_zero_iff_of_countable {s : Set β} {f : α → β} (hs : s.Countable) :
    μ (f ⁻¹' s) = 0 ↔ ∀ x ∈ s, μ (f ⁻¹' {x}) = 0 := by
  rw [← biUnion_preimage_singleton, measure_biUnion_null_iff hs]

/-- If `s` is a `Finset`, then the measure of its preimage can be found as the sum of measures
of the fibers `f ⁻¹' {y}`. -/
/-
**MeasureTheory.sum_measure_preimage_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：sum_measure_preimage_singleton (s : Finset β) {f : α -> β} (hf : forall y 
in s, MeasurableSet (f ⁻¹' {y})) : (∑ b in s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s)
参数：s : Finset β；hf : forall y in s, MeasurableSet (f ⁻¹' {y})。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_biUnion_finset`：measure_biUnion_finset {s : Finset
 ι} {f : ι -> Set α} (hd : PairwiseDisjoint (↑s) f) (hm : forall b in s, Measura
bleSet (f b)) : μ (⋃ b in …
· 使用定理 `Set.pairwiseDisjoint_fiber`：pairwiseDisjoint_fiber (f : ι -> α) (s : Set
 α) : s.PairwiseDisjoint fun a => f ⁻¹' {a}
· 使用定理 `Finset.set_biUnion_preimage_singleton`：set_biUnion_preimage_singleton (f
 : α -> β) (s : Finset β) : ⋃ y in s, f ⁻¹' {y} = f ⁻¹' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `s` is a `Finset`, then the measure of its preimage can be found as the sum o
f measures
of the fibers `f ⁻¹' {y}`.
-/
theorem sum_measure_preimage_singleton (s : Finset β) {f : α → β}
    (hf : ∀ y ∈ s, MeasurableSet (f ⁻¹' {y})) : (∑ b ∈ s, μ (f ⁻¹' {b})) = μ (f ⁻¹' ↑s) := by
  simp only [← measure_biUnion_finset (pairwiseDisjoint_fiber f s) hf,
    Finset.set_biUnion_preimage_singleton]
/-
**MeasureTheory.sum_measure_singleton** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {s 
: Finset α} [MeasurableSingletonClass α],   ∑ x ∈ s, μ {x} = μ ↑s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.sum_measure_preimage_singleton`：sum_measure_preimage_singl
eton (s : Finset β) {f : α -> β} (hf : forall y in s, MeasurableSet (f ⁻¹' {y}))
 : (∑ b in s, μ (f ⁻¹' {b})) = μ (…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma sum_measure_singleton {s : Finset α} [MeasurableSingletonClass α] :
    ∑ x ∈ s, μ {x} = μ s := by
  trans ∑ x ∈ s, μ (id ⁻¹' {x})
  · simp
  rw [sum_measure_preimage_singleton]
  · simp
  · simp
/-
**MeasureTheory.measure_sdiff_null'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_sdiff_null' (h : μ (s₁ inter s₂) = 0) : μ (s₁ \ s₂) = μ s₁
参数：h : μ (s₁ inter s₂) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.sdiff_ae_eq_self`：sdiff_ae_eq_self : (s \ t : Set α) =ᵐ[μ]
 s ↔ μ (s inter t) = 0
-/
theorem measure_sdiff_null' (h : μ (s₁ ∩ s₂) = 0) : μ (s₁ \ s₂) = μ s₁ :=
  measure_congr <| sdiff_ae_eq_self.2 h

@[deprecated (since := "2026-06-03")] alias measure_diff_null' := measure_sdiff_null'
/-
**MeasureTheory.measure_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_add_sdiff (hs : NullMeasurableSet s μ) (t : Set α) : μ s + μ (t \ 
s) = μ (s union t)
参数：hs : NullMeasurableSet s μ；t : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_union₀'`：measure_union₀' (hs : NullMeasurableSet s
 μ) (hd : AEDisjoint μ s t) : μ (s union t) = μ s + μ t
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
-/
theorem measure_add_sdiff (hs : NullMeasurableSet s μ) (t : Set α) :
    μ s + μ (t \ s) = μ (s ∪ t) := by
  rw [← measure_union₀' hs disjoint_sdiff_right.aedisjoint, union_sdiff_self]

@[deprecated (since := "2026-06-03")] alias measure_add_diff := measure_add_sdiff
/-
**MeasureTheory.measure_sdiff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_sdiff' (s : Set α) (hm : NullMeasurableSet t μ) (h_fin : μ t != ∞)
 : μ (s \ t) = μ (s union t) - μ t
参数：s : Set α；hm : NullMeasurableSet t μ；h_fin : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ENNReal.eq_sub_of_add_eq`：∀ {a b c : ENNReal}, c ≠ ⊤ → a + c = b → a = b
 - c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.measure_add_sdiff`：measure_add_sdiff (hs : NullMeasurableS
et s μ) (t : Set α) : μ s + μ (t \ s) = μ (s union t)
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
-/
theorem measure_sdiff' (s : Set α) (hm : NullMeasurableSet t μ) (h_fin : μ t ≠ ∞) :
    μ (s \ t) = μ (s ∪ t) - μ t :=
  ENNReal.eq_sub_of_add_eq h_fin <| by rw [add_comm, measure_add_sdiff hm, union_comm]

@[deprecated (since := "2026-06-03")] alias measure_diff' := measure_sdiff'
/-
**MeasureTheory.measure_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_sdiff (h : s₂ subseteq s₁) (h₂ : NullMeasurableSet s₂ μ) (h_fin : 
μ s₂ != ∞) : μ (s₁ \ s₂) = μ s₁ - μ s₂
参数：h : s₂ subseteq s₁；h₂ : NullMeasurableSet s₂ μ；h_fin : μ s₂ != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_sdiff'`：measure_sdiff' (s : Set α) (hm : NullMeasu
rableSet t μ) (h_fin : μ t != ∞) : μ (s \ t) = μ (s union t) - μ t
· 使用定理 `Set.union_eq_self_of_subset_right`：union_eq_self_of_subset_right {s t : 
Set α} (h : t subseteq s) : s union t = s
-/
theorem measure_sdiff (h : s₂ ⊆ s₁) (h₂ : NullMeasurableSet s₂ μ) (h_fin : μ s₂ ≠ ∞) :
    μ (s₁ \ s₂) = μ s₁ - μ s₂ := by rw [measure_sdiff' _ h₂ h_fin, union_eq_self_of_subset_right h]

@[deprecated (since := "2026-06-03")] alias measure_diff := measure_sdiff
/-
**MeasureTheory.le_measure_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：le_measure_sdiff : μ s₁ - μ s₂ <= μ (s₁ \ s₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_le_inter_add_sdiff`：measure_le_inter_add_sdiff (μ 
: F) (s t : Set α) : μ s <= μ (s inter t) + μ (s \ t)
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
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem le_measure_sdiff : μ s₁ - μ s₂ ≤ μ (s₁ \ s₂) :=
  tsub_le_iff_left.2 <| (measure_le_inter_add_sdiff μ s₁ s₂).trans <| by
    gcongr; apply inter_subset_right

@[deprecated (since := "2026-06-03")] alias le_measure_diff := le_measure_sdiff
/-
**MeasureTheory.le_measure_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：le_measure_symmDiff : μ s₁ - μ s₂ <= μ (s₁ ∆ s₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.le_measure_sdiff`：le_measure_sdiff : μ s₁ - μ s₂ <= μ (s₁ 
\ s₂)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem le_measure_symmDiff : μ s₁ - μ s₂ ≤ μ (s₁ ∆ s₂) :=
  le_trans le_measure_sdiff (measure_mono <| by simp [symmDiff_def])

/-- If the measure of the symmetric difference of two sets is finite,
then one has infinite measure if and only if the other one does. -/
/-
**MeasureTheory.measure_eq_top_iff_of_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measure_eq_top_iff_of_symmDiff (hμst : μ (s ∆ t) != ∞) : μ s = ∞ ↔ μ t = ∞
参数：hμst : μ (s ∆ t) != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.symmDiff_def`：∀ {α : Type u} (s t : Set α), symmDiff s t = s \ t ∪ t
 \ s
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ENNReal.sub_eq_top_iff`：∀ {a b : ENNReal}, a - b = ⊤ ↔ a = ⊤ ∧ b ≠ ⊤
· 使用定理 `MeasureTheory.le_measure_sdiff`：le_measure_sdiff : μ s₁ - μ s₂ <= μ (s₁ 
\ s₂)
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `symmDiff_comm`：symmDiff_comm : a ∆ b = b ∆ a

--- 原说明 ---
If the measure of the symmetric difference of two sets is finite,
then one has infinite measure if and only if the other one does.
-/
theorem measure_eq_top_iff_of_symmDiff (hμst : μ (s ∆ t) ≠ ∞) : μ s = ∞ ↔ μ t = ∞ := by
  suffices h : ∀ u v, μ (u ∆ v) ≠ ∞ → μ u = ∞ → μ v = ∞
    from ⟨h s t hμst, h t s (symmDiff_comm s t ▸ hμst)⟩
  intro u v hμuv hμu
  by_contra! hμv
  apply hμuv
  rw [Set.symmDiff_def, eq_top_iff]
  calc
    ∞ = μ u - μ v := by rw [ENNReal.sub_eq_top_iff.2 ⟨hμu, hμv⟩]
    _ ≤ μ (u \ v) := le_measure_sdiff
    _ ≤ μ (u \ v ∪ v \ u) := measure_mono subset_union_left

/-- If the measure of the symmetric difference of two sets is finite,
then one has finite measure if and only if the other one does. -/
/-
**MeasureTheory.measure_ne_top_iff_of_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measure_ne_top_iff_of_symmDiff (hμst : μ (s ∆ t) != ∞) : μ s != ∞ ↔ μ t !=
 ∞
参数：hμst : μ (s ∆ t) != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `MeasureTheory.measure_eq_top_iff_of_symmDiff`：measure_eq_top_iff_of_symm
Diff (hμst : μ (s ∆ t) != ∞) : μ s = ∞ ↔ μ t = ∞

--- 原说明 ---
If the measure of the symmetric difference of two sets is finite,
then one has finite measure if and only if the other one does.
-/
theorem measure_ne_top_iff_of_symmDiff (hμst : μ (s ∆ t) ≠ ∞) : μ s ≠ ∞ ↔ μ t ≠ ∞ :=
    (measure_eq_top_iff_of_symmDiff hμst).ne
/-
**MeasureTheory.measure_sdiff_lt_of_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measure_sdiff_lt_of_lt_add (hs : NullMeasurableSet s μ) (hst : s subseteq 
t) (hs' : μ s != ∞) {ε : Real>=0∞} (h : μ t < μ s + ε) : μ (t \ s) < ε
参数：hs : NullMeasurableSet s μ；hst : s subseteq t；hs' : μ s != ∞；h : μ t < μ s + 
ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_sdiff`：measure_sdiff (h : s₂ subseteq s₁) (h₂ : Nu
llMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞) : μ (s₁ \ s₂) = μ s₁ - μ s₂
· 使用定理 `ENNReal.sub_lt_of_lt_add`：∀ {a b c : ENNReal}, c ≤ a → a < b + c → a - c
 < b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem measure_sdiff_lt_of_lt_add (hs : NullMeasurableSet s μ) (hst : s ⊆ t) (hs' : μ s ≠ ∞)
    {ε : ℝ≥0∞} (h : μ t < μ s + ε) : μ (t \ s) < ε := by
  rw [measure_sdiff hst hs hs']; rw [add_comm] at h
  exact ENNReal.sub_lt_of_lt_add (measure_mono hst) h

@[deprecated (since := "2026-06-03")] alias measure_diff_lt_of_lt_add := measure_sdiff_lt_of_lt_add
/-
**MeasureTheory.measure_sdiff_le_iff_le_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measure_sdiff_le_iff_le_add (hs : NullMeasurableSet s μ) (hst : s subseteq
 t) (hs' : μ s != ∞) {ε : Real>=0∞} : μ (t \ s) <= ε ↔ μ t <= μ s + ε
参数：hs : NullMeasurableSet s μ；hst : s subseteq t；hs' : μ s != ∞。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_sdiff`：measure_sdiff (h : s₂ subseteq s₁) (h₂ : Nu
llMeasurableSet s₂ μ) (h_fin : μ s₂ != ∞) : μ (s₁ \ s₂) = μ s₁ - μ s₂
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measure_sdiff_le_iff_le_add (hs : NullMeasurableSet s μ) (hst : s ⊆ t) (hs' : μ s ≠ ∞)
    {ε : ℝ≥0∞} : μ (t \ s) ≤ ε ↔ μ t ≤ μ s + ε := by
  rw [measure_sdiff hst hs hs', tsub_le_iff_left]

@[deprecated (since := "2026-06-03")]
alias measure_diff_le_iff_le_add := measure_sdiff_le_iff_le_add
/-
**MeasureTheory.measure_eq_measure_of_null_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：measure_eq_measure_of_null_sdiff {s t : Set α} (hst : s subseteq t) (h_nul
lsdiff : μ (t \ s) = 0) : μ s = μ t
参数：hst : s subseteq t；h_nullsdiff : μ (t \ s) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_le_set`：ae_le_set : s <=ᵐ[μ] t ↔ μ (s \ t) = 0
-/
theorem measure_eq_measure_of_null_sdiff {s t : Set α} (hst : s ⊆ t) (h_nullsdiff : μ (t \ s) = 0) :
    μ s = μ t := measure_congr <|
      EventuallyLE.antisymm (LE.le.eventuallyLE hst) (ae_le_set.mpr h_nullsdiff)

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_of_null_diff := measure_eq_measure_of_null_sdiff
/-
**MeasureTheory.measure_eq_measure_of_between_null_sdiff** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：measure_eq_measure_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : s₁ subs
eteq s₂) (h23 : s₂ subseteq s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ ∧ 
μ s₂ = μ s₃
参数：h12 : s₁ subseteq s₂；h23 : s₂ subseteq s₃；h_nullsdiff : μ (s₃ \ s₁) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_union_le`：measure_union_le (s t : Set α) : μ (s un
ion t) <= μ s + μ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
-/
theorem measure_eq_measure_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂) (h23 : s₂ ⊆ s₃)
    (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ ∧ μ s₂ = μ s₃ := by
  have le12 : μ s₁ ≤ μ s₂ := measure_mono h12
  have le23 : μ s₂ ≤ μ s₃ := measure_mono h23
  have key : μ s₃ ≤ μ s₁ :=
    calc
      μ s₃ = μ (s₃ \ s₁ ∪ s₁) := by rw [sdiff_union_of_subset (h12.trans h23)]
      _ ≤ μ (s₃ \ s₁) + μ s₁ := measure_union_le _ _
      _ = μ s₁ := by simp only [h_nullsdiff, zero_add]
  exact ⟨le12.antisymm (le23.trans key), le23.antisymm (key.trans le12)⟩

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_of_between_null_diff := measure_eq_measure_of_between_null_sdiff
/-
**MeasureTheory.measure_eq_measure_smaller_of_between_null_sdiff** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_measure_smaller_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 :
 s₁ subseteq s₂) (h23 : s₂ subseteq s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₁ =
 μ s₂
参数：h12 : s₁ subseteq s₂；h23 : s₂ subseteq s₃；h_nullsdiff : μ (s₃ \ s₁) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.measure_eq_measure_of_between_null_sdiff`：measure_eq_measu
re_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : s₁ subseteq s₂) (h23 : s₂ sub
seteq s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : …
-/
theorem measure_eq_measure_smaller_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₁ = μ s₂ :=
  (measure_eq_measure_of_between_null_sdiff h12 h23 h_nullsdiff).1

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_smaller_of_between_null_diff :=
  measure_eq_measure_smaller_of_between_null_sdiff
/-
**MeasureTheory.measure_eq_measure_larger_of_between_null_sdiff** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_eq_measure_larger_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : 
s₁ subseteq s₂) (h23 : s₂ subseteq s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₂ = 
μ s₃
参数：h12 : s₁ subseteq s₂；h23 : s₂ subseteq s₃；h_nullsdiff : μ (s₃ \ s₁) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.measure_eq_measure_of_between_null_sdiff`：measure_eq_measu
re_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : s₁ subseteq s₂) (h23 : s₂ sub
seteq s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : …
-/
theorem measure_eq_measure_larger_of_between_null_sdiff {s₁ s₂ s₃ : Set α} (h12 : s₁ ⊆ s₂)
    (h23 : s₂ ⊆ s₃) (h_nullsdiff : μ (s₃ \ s₁) = 0) : μ s₂ = μ s₃ :=
  (measure_eq_measure_of_between_null_sdiff h12 h23 h_nullsdiff).2

@[deprecated (since := "2026-06-03")]
alias measure_eq_measure_larger_of_between_null_diff :=
  measure_eq_measure_larger_of_between_null_sdiff
/-
**MeasureTheory.measure_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_compl (h₁ : MeasurableSet s) (h_fin : μ s != ∞) : μ sᶜ = μ univ - 
μ s
参数：h₁ : MeasurableSet s；h_fin : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measure_compl₀`：measure_compl₀ (h : NullMeasurableSet s μ)
 (hs : μ s != ∞) : μ sᶜ = μ Set.univ - μ s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
lemma measure_compl₀ (h : NullMeasurableSet s μ) (hs : μ s ≠ ∞) :
    μ sᶜ = μ Set.univ - μ s := by
  rw [← measure_add_measure_compl₀ h, ENNReal.add_sub_cancel_left hs]
/-
**MeasureTheory.measure_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_compl (h₁ : MeasurableSet s) (h_fin : μ s != ∞) : μ sᶜ = μ univ - 
μ s
参数：h₁ : MeasurableSet s；h_fin : μ s != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.measure_compl₀`：measure_compl₀ (h : NullMeasurableSet s μ)
 (hs : μ s != ∞) : μ sᶜ = μ Set.univ - μ s
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem measure_compl (h₁ : MeasurableSet s) (h_fin : μ s ≠ ∞) : μ sᶜ = μ univ - μ s :=
  measure_compl₀ h₁.nullMeasurableSet h_fin
/-
**MeasureTheory.measure_inter_conull'** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_inter_conull' (ht : μ (s \ t) = 0) : μ (s inter t) = μ s
参数：ht : μ (s \ t) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_compl`：sdiff_compl : s \ tᶜ = s inter t
· 使用定理 `MeasureTheory.measure_sdiff_null'`：measure_sdiff_null' (h : μ (s₁ inter 
s₂) = 0) : μ (s₁ \ s₂) = μ s₁
· 使用定理 `Set.sdiff_eq`：sdiff_eq (s t : Set α) : s \ t = s inter tᶜ
-/
lemma measure_inter_conull' (ht : μ (s \ t) = 0) : μ (s ∩ t) = μ s := by
  rw [← sdiff_compl, measure_sdiff_null']; rwa [← sdiff_eq]
/-
**MeasureTheory.measure_inter_conull** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_inter_conull (ht : μ tᶜ = 0) : μ (s inter t) = μ s
参数：ht : μ tᶜ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_compl`：sdiff_compl : s \ tᶜ = s inter t
· 使用定理 `MeasureTheory.measure_sdiff_null`：measure_sdiff_null (ht : μ t = 0) : μ 
(s \ t) = μ s
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma measure_inter_conull (ht : μ tᶜ = 0) : μ (s ∩ t) = μ s := by
  rw [← sdiff_compl, measure_sdiff_null ht]

@[simp]
/-
**MeasureTheory.union_ae_eq_left_iff_ae_subset** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：union_ae_eq_left_iff_ae_subset : (s union t : Set α) =ᵐ[μ] s ↔ t <=ᵐ[μ] s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_le_set`：ae_le_set : s <=ᵐ[μ] t ↔ μ (s \ t) = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_sdiff_left`：union_sdiff_left {s t : Set α} : (s union t) \ s =
 t \ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MeasureTheory.ae_eq_set`：ae_eq_set {s t : Set α} : s =ᵐ[μ] t ↔ μ (s \ t)
 = 0 ∧ μ (t \ s) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyLE_antisymm_iff`：eventuallyLE_antisymm_iff [PartialOrde
r β] {l : Filter α} {f g : α -> β} : f =ᶠ[l] g ↔ f <=ᶠ[l] g ∧ g <=ᶠ[l] f
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
-/
theorem union_ae_eq_left_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] s ↔ t ≤ᵐ[μ] s := by
  rw [ae_le_set]
  refine
    ⟨fun h => by simpa only [union_sdiff_left] using (ae_eq_set.mp h).1, fun h =>
      eventuallyLE_antisymm_iff.mpr
        ⟨by rwa [ae_le_set, union_sdiff_left],
          LE.le.eventuallyLE subset_union_left⟩⟩

@[simp]
/-
**MeasureTheory.union_ae_eq_right_iff_ae_subset** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：union_ae_eq_right_iff_ae_subset : (s union t : Set α) =ᵐ[μ] t ↔ s <=ᵐ[μ] t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `MeasureTheory.union_ae_eq_left_iff_ae_subset`：union_ae_eq_left_iff_ae_su
bset : (s union t : Set α) =ᵐ[μ] s ↔ t <=ᵐ[μ] s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem union_ae_eq_right_iff_ae_subset : (s ∪ t : Set α) =ᵐ[μ] t ↔ s ≤ᵐ[μ] t := by
  rw [union_comm, union_ae_eq_left_iff_ae_subset]
/-
**MeasureTheory.ae_eq_of_ae_subset_of_measure_ge** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：ae_eq_of_ae_subset_of_measure_ge (h₁ : s <=ᵐ[μ] t) (h₂ : μ t <= μ s) (hsm 
: NullMeasurableSet s μ) (ht : μ t != ∞) : s =ᵐ[μ] t
参数：h₁ : s <=ᵐ[μ] t；h₂ : μ t <= μ s；hsm : NullMeasurableSet s μ；ht : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyLE_antisymm_iff`：eventuallyLE_antisymm_iff [PartialOrde
r β] {l : Filter α} {f g : α -> β} : f =ᶠ[l] g ↔ f <=ᶠ[l] g ∧ g <=ᶠ[l] f
· 使用定理 `MeasureTheory.ae_le_set`：ae_le_set : s <=ᵐ[μ] t ↔ μ (s \ t) = 0
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `MeasureTheory.measure_mono_ae`：measure_mono_ae (H : s <=ᵐ[μ] t) : μ s <=
 μ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_sdiff'`：measure_sdiff' (s : Set α) (hm : NullMeasu
rableSet t μ) (h_fin : μ t != ∞) : μ (s \ t) = μ (s union t) - μ t
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `MeasureTheory.union_ae_eq_left_iff_ae_subset`：union_ae_eq_left_iff_ae_su
bset : (s union t : Set α) =ᵐ[μ] s ↔ t <=ᵐ[μ] s
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `ENNReal.instOrderedSub`：OrderedSub ENNReal
-/
theorem ae_eq_of_ae_subset_of_measure_ge (h₁ : s ≤ᵐ[μ] t) (h₂ : μ t ≤ μ s)
    (hsm : NullMeasurableSet s μ) (ht : μ t ≠ ∞) : s =ᵐ[μ] t := by
  refine eventuallyLE_antisymm_iff.mpr ⟨h₁, ae_le_set.mpr ?_⟩
  replace h₂ : μ t = μ s := h₂.antisymm (measure_mono_ae h₁)
  replace ht : μ s ≠ ∞ := h₂ ▸ ht
  rw [measure_sdiff' t hsm ht, measure_congr (union_ae_eq_left_iff_ae_subset.mpr h₁), h₂, tsub_self]

/-- If `s ⊆ t`, `μ t ≤ μ s`, `μ t ≠ ∞`, and `s` is measurable, then `s =ᵐ[μ] t`. -/
/-
**MeasureTheory.ae_eq_of_subset_of_measure_ge** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：ae_eq_of_subset_of_measure_ge (h₁ : s subseteq t) (h₂ : μ t <= μ s) (hsm :
 NullMeasurableSet s μ) (ht : μ t != ∞) : s =ᵐ[μ] t
参数：h₁ : s subseteq t；h₂ : μ t <= μ s；hsm : NullMeasurableSet s μ；ht : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_eq_of_ae_subset_of_measure_ge`：ae_eq_of_ae_subset_of_me
asure_ge (h₁ : s <=ᵐ[μ] t) (h₂ : μ t <= μ s) (hsm : NullMeasurableSet s μ) (ht :
 μ t != ∞) : s =ᵐ[μ] t
· 使用定理 `LE.le.eventuallyLE`：LE.le.eventuallyLE {α} {l : Filter α} {s t : Set α} 
(h : s subseteq t) : s <=ᶠ[l] t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
If `s ⊆ t`, `μ t ≤ μ s`, `μ t ≠ ∞`, and `s` is measurable, then `s =ᵐ[μ] t`.
-/
theorem ae_eq_of_subset_of_measure_ge (h₁ : s ⊆ t) (h₂ : μ t ≤ μ s) (hsm : NullMeasurableSet s μ)
    (ht : μ t ≠ ∞) : s =ᵐ[μ] t :=
  ae_eq_of_ae_subset_of_measure_ge h₁.eventuallyLE h₂ hsm ht
/-
**MeasureTheory.measure_iUnion_congr_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：measure_iUnion_congr_of_subset {ι : Sort*} [Countable ι] {s : ι -> Set α} 
{t : ι -> Set α} (hsub : forall i, s i subseteq t i) (h_le : forall i, μ (t i) <
= μ (s i)) : μ (⋃ i, s i) = μ (⋃ i, t i)
参数：hsub : forall i, s i subseteq t i；h_le : forall i, μ (t i) <= μ (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.iUnion_mono''`：iUnion_mono'' {s t : ι -> Set α} (h : forall i, s i s
ubseteq t i) : iUnion s subseteq iUnion t
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `MeasureTheory.ae_eq_of_subset_of_measure_ge`：ae_eq_of_subset_of_measure_
ge (h₁ : s subseteq t) (h₂ : μ t <= μ s) (hsm : NullMeasurableSet s μ) (ht : μ t
 != ∞) : s =ᵐ[μ] t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.countable_iUnion`：∀ {ι : Sort u_1} {α : Type u_2} {l
 : Filter α} [CountableInterFilter l] [Countable ι] {s t : ι → Set α},   (∀ (i :
 ι), s i =ᶠ[l] t i) → ⋃ i,…
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem measure_iUnion_congr_of_subset {ι : Sort*} [Countable ι] {s : ι → Set α} {t : ι → Set α}
    (hsub : ∀ i, s i ⊆ t i) (h_le : ∀ i, μ (t i) ≤ μ (s i)) : μ (⋃ i, s i) = μ (⋃ i, t i) := by
  refine le_antisymm (by gcongr; apply hsub) ?_
  by_cases! htop : ∃ i, μ (t i) = ∞
  · rcases htop with ⟨i, hi⟩
    calc
      μ (⋃ i, t i) ≤ ∞ := le_top
      _ ≤ μ (s i) := hi ▸ h_le i
      _ ≤ μ (⋃ i, s i) := measure_mono <| subset_iUnion _ _
  set M := toMeasurable μ
  have H : ∀ b, (M (t b) ∩ M (⋃ b, s b) : Set α) =ᵐ[μ] M (t b) := by
    refine fun b => ae_eq_of_subset_of_measure_ge inter_subset_left ?_ ?_ ?_
    · calc
        μ (M (t b)) = μ (t b) := measure_toMeasurable _
        _ ≤ μ (s b) := h_le b
        _ ≤ μ (M (t b) ∩ M (⋃ b, s b)) :=
          measure_mono <|
            subset_inter ((hsub b).trans <| subset_toMeasurable _ _)
              ((subset_iUnion _ _).trans <| subset_toMeasurable _ _)
    · measurability
    · rw [measure_toMeasurable]
      exact htop b
  calc
    μ (⋃ b, t b) ≤ μ (⋃ b, M (t b)) := measure_mono (iUnion_mono fun b => subset_toMeasurable _ _)
    _ = μ (⋃ b, M (t b) ∩ M (⋃ b, s b)) :=
      measure_congr (Filter.EventuallyEq.countable_iUnion H).symm
    _ ≤ μ (M (⋃ b, s b)) := measure_mono (iUnion_subset fun b => inter_subset_right)
    _ = μ (⋃ b, s b) := measure_toMeasurable _
/-
**MeasureTheory.measure_union_congr_of_subset** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measure_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ subseteq s₂) (hsμ :
 μ s₂ <= μ s₁) (ht : t₁ subseteq t₂) (htμ : μ t₂ <= μ t₁) : μ (s₁ union t₁) = μ 
(s₂ union t₂)
参数：hs : s₁ subseteq s₂；hsμ : μ s₂ <= μ s₁；ht : t₁ subseteq t₂；htμ : μ t₂ <= μ t₁
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_eq_iUnion`：union_eq_iUnion {s₁ s₂ : Set α} : s₁ union s₂ = ⋃ b
 : Bool, cond b s₁ s₂
· 使用定理 `MeasureTheory.measure_iUnion_congr_of_subset`：measure_iUnion_congr_of_su
bset {ι : Sort*} [Countable ι] {s : ι -> Set α} {t : ι -> Set α} (hsub : forall 
i, s i subseteq t i) (h_le : foral…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bool.forall_bool`：∀ {p : Bool → Prop}, (∀ (b : Bool), p b) ↔ p false ∧ p
 true
-/
theorem measure_union_congr_of_subset {t₁ t₂ : Set α} (hs : s₁ ⊆ s₂) (hsμ : μ s₂ ≤ μ s₁)
    (ht : t₁ ⊆ t₂) (htμ : μ t₂ ≤ μ t₁) : μ (s₁ ∪ t₁) = μ (s₂ ∪ t₂) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  exact measure_iUnion_congr_of_subset (Bool.forall_bool.2 ⟨ht, hs⟩) (Bool.forall_bool.2 ⟨htμ, hsμ⟩)

@[simp]
/-
**MeasureTheory.measure_iUnion_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：measure_iUnion_toMeasurable {ι : Sort*} [Countable ι] (s : ι -> Set α) : μ
 (⋃ i, toMeasurable μ (s i)) = μ (⋃ i, s i)
参数：s : ι -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_iUnion_congr_of_subset`：measure_iUnion_congr_of_su
bset {ι : Sort*} [Countable ι] {s : ι -> Set α} {t : ι -> Set α} (hsub : forall 
i, s i subseteq t i) (h_le : foral…
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
-/
theorem measure_iUnion_toMeasurable {ι : Sort*} [Countable ι] (s : ι → Set α) :
    μ (⋃ i, toMeasurable μ (s i)) = μ (⋃ i, s i) :=
  Eq.symm <| measure_iUnion_congr_of_subset (fun _i => subset_toMeasurable _ _) fun _i ↦
    (measure_toMeasurable _).le
/-
**MeasureTheory.measure_biUnion_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：measure_biUnion_toMeasurable {I : Set β} (hc : I.Countable) (s : β -> Set 
α) : μ (⋃ b in I, toMeasurable μ (s b)) = μ (⋃ b in I, s b)
参数：hc : I.Countable；s : β -> Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `MeasureTheory.measure_iUnion_toMeasurable`：measure_iUnion_toMeasurable {
ι : Sort*} [Countable ι] (s : ι -> Set α) : μ (⋃ i, toMeasurable μ (s i)) = μ (⋃
 i, s i)
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem measure_biUnion_toMeasurable {I : Set β} (hc : I.Countable) (s : β → Set α) :
    μ (⋃ b ∈ I, toMeasurable μ (s b)) = μ (⋃ b ∈ I, s b) := by
  have := hc.toEncodable
  simp only [biUnion_eq_iUnion, measure_iUnion_toMeasurable]

@[simp]
/-
**MeasureTheory.measure_toMeasurable_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measure_toMeasurable_union : μ (toMeasurable μ s union t) = μ (s union t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_union_congr_of_subset`：measure_union_congr_of_subs
et {t₁ t₂ : Set α} (hs : s₁ subseteq s₂) (hsμ : μ s₂ <= μ s₁) (ht : t₁ subseteq 
t₂) (htμ : μ t₂ <= μ t₁) : μ (s₁ …
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem measure_toMeasurable_union : μ (toMeasurable μ s ∪ t) = μ (s ∪ t) :=
  Eq.symm <|
    measure_union_congr_of_subset (subset_toMeasurable _ _) (measure_toMeasurable _).le Subset.rfl
      le_rfl

@[simp]
/-
**MeasureTheory.measure_union_toMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：measure_union_toMeasurable : μ (s union toMeasurable μ t) = μ (s union t)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_union_congr_of_subset`：measure_union_congr_of_subs
et {t₁ t₂ : Set α} (hs : s₁ subseteq s₂) (hsμ : μ s₂ <= μ s₁) (ht : t₁ subseteq 
t₂) (htμ : μ t₂ <= μ t₁) : μ (s₁ …
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
-/
theorem measure_union_toMeasurable : μ (s ∪ toMeasurable μ t) = μ (s ∪ t) :=
  Eq.symm <|
    measure_union_congr_of_subset Subset.rfl le_rfl (subset_toMeasurable _ _)
      (measure_toMeasurable _).le
/-
**MeasureTheory.sum_measure_le_measure_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory`。
形式化陈述：sum_measure_le_measure_univ {s : Finset ι} {t : ι -> Set α} (h : forall i 
in s, NullMeasurableSet (t i) μ) (H : Set.Pairwise s (AEDisjoint μ on t)) : (∑ i
 in s, μ (t i)) <= μ (univ : Set α)
参数：h : forall i in s, NullMeasurableSet (t i) μ；H : Set.Pairwise s (AEDisjoint μ
 on t)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_biUnion_finset₀`：measure_biUnion_finset₀ {s : Fins
et ι} {f : ι -> Set α} (hd : Set.Pairwise (↑s) (AEDisjoint μ on f)) (hm : forall
 b in s, NullMeasurableSet …
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem sum_measure_le_measure_univ {s : Finset ι} {t : ι → Set α}
    (h : ∀ i ∈ s, NullMeasurableSet (t i) μ) (H : Set.Pairwise s (AEDisjoint μ on t)) :
    (∑ i ∈ s, μ (t i)) ≤ μ (univ : Set α) := by
  rw [← measure_biUnion_finset₀ H h]
  exact measure_mono (subset_univ _)
/-
**MeasureTheory.tsum_measure_le_measure_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：tsum_measure_le_measure_univ {s : ι -> Set α} (hs : forall i, NullMeasurab
leSet (s i) μ) (H : Pairwise (AEDisjoint μ on s)) : ∑' i, μ (s i) <= μ (univ : S
et α)
参数：hs : forall i, NullMeasurableSet (s i) μ；H : Pairwise (AEDisjoint μ on s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tsum_eq_iSup_sum`：∀ {α : Type u_1} {f : α → ENNReal}, ∑' (a : α)
, f a = ⨆ s, ∑ a ∈ s, f a
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `MeasureTheory.sum_measure_le_measure_univ`：sum_measure_le_measure_univ {
s : Finset ι} {t : ι -> Set α} (h : forall i in s, NullMeasurableSet (t i) μ) (H
 : Set.Pairwise s (AEDisjoint μ…
-/
theorem tsum_measure_le_measure_univ {s : ι → Set α} (hs : ∀ i, NullMeasurableSet (s i) μ)
    (H : Pairwise (AEDisjoint μ on s)) : ∑' i, μ (s i) ≤ μ (univ : Set α) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  exact iSup_le fun s =>
    sum_measure_le_measure_univ (fun i _hi => hs i) fun i _hi j _hj hij => H hij

/-- Pigeonhole principle for measure spaces: if `∑' i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty. -/
/-
**MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_tsum_measure** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_nonempty_inter_of_measure_univ_lt_tsum_measure {m : MeasurableSpace
 α} (μ : Measure α) {s : ι -> Set α} (hs : forall i, NullMeasurableSet (s i) μ) 
(H : μ (univ : Set α) < ∑' i, μ (s i)) : exists i j, i != j ∧ (s i inter s j).No
nempty
参数：μ : Measure α；hs : forall i, NullMeasurableSet (s i) μ；H : μ (univ : Set α) <
 ∑' i, μ (s i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `MeasureTheory.tsum_measure_le_measure_univ`：tsum_measure_le_measure_univ
 {s : ι -> Set α} (hs : forall i, NullMeasurableSet (s i) μ) (H : Pairwise (AEDi
sjoint μ on s)) : ∑' i, μ (s i) …
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅

--- 原说明 ---
Pigeonhole principle for measure spaces: if `∑' i, μ (s i) > μ univ`, then
one of the intersections `s i ∩ s j` is not empty.
-/
theorem exists_nonempty_inter_of_measure_univ_lt_tsum_measure {m : MeasurableSpace α}
    (μ : Measure α) {s : ι → Set α} (hs : ∀ i, NullMeasurableSet (s i) μ)
    (H : μ (univ : Set α) < ∑' i, μ (s i)) : ∃ i j, i ≠ j ∧ (s i ∩ s j).Nonempty := by
  contrapose! H
  apply tsum_measure_le_measure_univ hs
  intro i j hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i j hij)).aedisjoint

/-- Pigeonhole principle for measure spaces: if `s` is a `Finset` and
`∑ i ∈ s, μ (t i) > μ univ`, then one of the intersections `t i ∩ t j` is not empty. -/
/-
**MeasureTheory.exists_nonempty_inter_of_measure_univ_lt_sum_measure** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：exists_nonempty_inter_of_measure_univ_lt_sum_measure {m : MeasurableSpace 
α} (μ : Measure α) {s : Finset ι} {t : ι -> Set α} (h : forall i in s, NullMeasu
rableSet (t i) μ) (H : μ (univ : Set α) < ∑ i in s, μ (t i)) : exists i in s, ex
ists j in s, exists _h : i != j, (t i inter t j).Nonempty
参数：μ : Measure α；h : forall i in s, NullMeasurableSet (t i) μ；H : μ (univ : Set 
α) < ∑ i in s, μ (t i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `MeasureTheory.sum_measure_le_measure_univ`：sum_measure_le_measure_univ {
s : Finset ι} {t : ι -> Set α} (h : forall i in s, NullMeasurableSet (t i) μ) (H
 : Set.Pairwise s (AEDisjoint μ…
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_iff_inter_eq_empty`：disjoint_iff_inter_eq_empty : Disjoint 
s t ↔ s inter t = ∅

--- 原说明 ---
Pigeonhole principle for measure spaces: if `s` is a `Finset` and
`∑ i ∈ s, μ (t i) > μ univ`, then one of the intersections `t i ∩ t j` is not em
pty.
-/
theorem exists_nonempty_inter_of_measure_univ_lt_sum_measure {m : MeasurableSpace α} (μ : Measure α)
    {s : Finset ι} {t : ι → Set α} (h : ∀ i ∈ s, NullMeasurableSet (t i) μ)
    (H : μ (univ : Set α) < ∑ i ∈ s, μ (t i)) :
    ∃ i ∈ s, ∃ j ∈ s, ∃ _h : i ≠ j, (t i ∩ t j).Nonempty := by
  contrapose! H
  apply sum_measure_le_measure_univ h
  intro i hi j hj hij
  exact (disjoint_iff_inter_eq_empty.mpr (H i hi j hj hij)).aedisjoint

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `t` is measurable. -/
/-
**MeasureTheory.nonempty_inter_of_measure_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：nonempty_inter_of_measure_lt_add {m : MeasurableSpace α} (μ : Measure α) {
s t u : Set α} (ht : MeasurableSet t) (h's : s subseteq u) (h't : t subseteq u) 
(h : μ u < μ s + μ t) : (s inter t).Nonempty
参数：μ : Measure α；ht : MeasurableSet t；h's : s subseteq u；h't : t subseteq u；h : 
μ u < μ s + μ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.measure_union`：measure_union (hd : Disjoint s₁ s₂) (h : Me
asurableSet s₂) : μ (s₁ union s₂) = μ s₁ + μ s₂
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r

--- 原说明 ---
If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `t` is measurable.
-/
theorem nonempty_inter_of_measure_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (ht : MeasurableSet t) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) :
    (s ∩ t).Nonempty := by
  rw [← Set.not_disjoint_iff_nonempty_inter]
  contrapose! h
  calc
    μ s + μ t = μ (s ∪ t) := (measure_union h ht).symm
    _ ≤ μ u := measure_mono (union_subset h's h't)

/-- If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `s` is measurable. -/
/-
**MeasureTheory.nonempty_inter_of_measure_lt_add'** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：nonempty_inter_of_measure_lt_add' {m : MeasurableSpace α} (μ : Measure α) 
{s t u : Set α} (hs : MeasurableSet s) (h's : s subseteq u) (h't : t subseteq u)
 (h : μ u < μ s + μ t) : (s inter t).Nonempty
参数：μ : Measure α；hs : MeasurableSet s；h's : s subseteq u；h't : t subseteq u；h : 
μ u < μ s + μ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `MeasureTheory.nonempty_inter_of_measure_lt_add`：nonempty_inter_of_measur
e_lt_add {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α} (ht : Measurabl
eSet t) (h's : s subseteq u) (h't : …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
If two sets `s` and `t` are included in a set `u`, and `μ s + μ t > μ u`,
then `s` intersects `t`. Version assuming that `s` is measurable.
-/
theorem nonempty_inter_of_measure_lt_add' {m : MeasurableSpace α} (μ : Measure α) {s t u : Set α}
    (hs : MeasurableSet s) (h's : s ⊆ u) (h't : t ⊆ u) (h : μ u < μ s + μ t) :
    (s ∩ t).Nonempty := by
  rw [add_comm] at h
  rw [inter_comm]
  exact nonempty_inter_of_measure_lt_add μ hs h't h's h

/-- Continuity from below:
the measure of the union of a directed sequence of (not necessarily measurable) sets
is the supremum of the measures. -/
/-
**MeasureTheory._root_.Directed.measure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuity from below:
the measure of the union of a directed sequence of (not necessarily measurable) 
sets
is the supremum of the measures.
-/
theorem _root_.Directed.measure_iUnion [Countable ι] {s : ι → Set α} (hd : Directed (· ⊆ ·) s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) := by
  -- WLOG, `ι = ℕ`
  rcases Countable.exists_injective_nat ι with ⟨e, he⟩
  generalize ht : Function.extend e s ⊥ = t
  replace hd : Directed (· ⊆ ·) t := ht ▸ hd.extend_bot he
  suffices μ (⋃ n, t n) = ⨆ n, μ (t n) by
    simp only [← ht, Function.apply_extend μ, ← iSup_eq_iUnion, iSup_extend_bot he,
      Function.comp_def, Pi.bot_apply, bot_eq_empty, measure_empty] at this
    exact this.trans (iSup_extend_bot he _)
  clear! ι
  -- The `≥` inequality is trivial
  refine le_antisymm ?_ (iSup_le fun i ↦ measure_mono <| subset_iUnion _ _)
  -- Choose `T n ⊇ t n` of the same measure, put `Td n = disjointed T`
  set T : ℕ → Set α := fun n => toMeasurable μ (t n)
  set Td : ℕ → Set α := disjointed T
  have hm : ∀ n, MeasurableSet (Td n) := .disjointed fun n ↦ measurableSet_toMeasurable _ _
  calc
    μ (⋃ n, t n) = μ (⋃ n, Td n) := by rw [iUnion_disjointed, measure_iUnion_toMeasurable]
    _ ≤ ∑' n, μ (Td n) := measure_iUnion_le _
    _ = ⨆ I : Finset ℕ, ∑ n ∈ I, μ (Td n) := ENNReal.tsum_eq_iSup_sum
    _ ≤ ⨆ n, μ (t n) := iSup_le fun I => by
      rcases hd.finset_le I with ⟨N, hN⟩
      calc
        (∑ n ∈ I, μ (Td n)) = μ (⋃ n ∈ I, Td n) :=
          (measure_biUnion_finset ((disjoint_disjointed T).set_pairwise I) fun n _ => hm n).symm
        _ ≤ μ (⋃ n ∈ I, T n) := measure_mono (iUnion₂_mono fun n _hn => disjointed_subset _ _)
        _ = μ (⋃ n ∈ I, t n) := measure_biUnion_toMeasurable I.countable_toSet _
        _ ≤ μ (t N) := measure_mono (iUnion₂_subset hN)
        _ ≤ ⨆ n, μ (t n) := le_iSup (μ ∘ t) N

/-- Continuity from below:
the measure of the union of a monotone family of sets is equal to the supremum of their measures.
The theorem assumes that the `atTop` filter on the index set is countably generated,
so it works for a family indexed by a countable type, as well as `ℝ`. -/
/-
**MeasureTheory._root_.Monotone.measure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuity from below:
the measure of the union of a monotone family of sets is equal to the supremum o
f their measures.
The theorem assumes that the `atTop` filter on the index set is countably genera
ted,
so it works for a family indexed by a countable type, as well as `ℝ`.
-/
theorem _root_.Monotone.measure_iUnion [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι → Set α} (hs : Monotone s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) := by
  cases isEmpty_or_nonempty ι with
  | inl _ => simp
  | inr _ =>
    rcases exists_seq_monotone_tendsto_atTop_atTop ι with ⟨x, hxm, hx⟩
    rw [← hs.iUnion_comp_tendsto_atTop hx, ← Monotone.iSup_comp_tendsto_atTop _ hx]
    exacts [(hs.comp hxm).directed_le.measure_iUnion, fun _ _ h ↦ measure_mono (hs h)]
/-
**MeasureTheory._root_.Antitone.measure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Antitone.measure_iUnion [Preorder ι] [IsCodirectedOrder ι]
    [(atBot : Filter ι).IsCountablyGenerated] {s : ι → Set α} (hs : Antitone s) :
    μ (⋃ i, s i) = ⨆ i, μ (s i) :=
  hs.dual_left.measure_iUnion

/-- Continuity from below: the measure of the union of a sequence of
(not necessarily measurable) sets is the supremum of the measures of the partial unions. -/
/-
**MeasureTheory.measure_iUnion_eq_iSup_accumulate** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：measure_iUnion_eq_iSup_accumulate [Preorder ι] [IsDirectedOrder ι] [(atTop
 : Filter ι).IsCountablyGenerated] {f : ι -> Set α} : μ (⋃ i, f i) = ⨆ i, μ (acc
umulate f i)
参数：atTop : Filter ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_accumulate`：iUnion_accumulate [Preorder α] : ⋃ x, accumulate 
s x = ⋃ x, s x
· 使用定理 `Monotone.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsDirectedOrder ι]
 [Filter.atTo…
· 使用定理 `Set.monotone_accumulate`：monotone_accumulate [Preorder α] : Monotone (ac
cumulate s)

--- 原说明 ---
Continuity from below: the measure of the union of a sequence of
(not necessarily measurable) sets is the supremum of the measures of the partial
 unions.
-/
theorem measure_iUnion_eq_iSup_accumulate [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {f : ι → Set α} :
    μ (⋃ i, f i) = ⨆ i, μ (accumulate f i) := by
  rw [← iUnion_accumulate]
  exact monotone_accumulate.measure_iUnion
/-
**MeasureTheory.measure_biUnion_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：measure_biUnion_eq_iSup {s : ι -> Set α} {t : Set ι} (ht : t.Countable) (h
d : DirectedOn ((· subseteq ·) on s) t) : μ (⋃ i in t, s i) = ⨆ i in t, μ (s i)
参数：ht : t.Countable；hd : DirectedOn ((· subseteq ·) on s) t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Countable.to_subtype`：∀ {α : Type u} {s : Set α}, s.Countable → Coun
table ↑s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Directed.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [Countable ι] {s : ι → Set α},   Directed
 (fun x1 x2 =…
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_subtype''`：iSup_subtype'' {ι} (s : Set ι) (f : ι -> α) : ⨆ i : s, f
 i = ⨆ (t : ι) (_ : t in s), f t
-/
theorem measure_biUnion_eq_iSup {s : ι → Set α} {t : Set ι} (ht : t.Countable)
    (hd : DirectedOn ((· ⊆ ·) on s) t) : μ (⋃ i ∈ t, s i) = ⨆ i ∈ t, μ (s i) := by
  have := ht.to_subtype
  rw [biUnion_eq_iUnion, hd.directed_val.measure_iUnion, ← iSup_subtype'']

/-- **Continuity from above**:
the measure of the intersection of a directed downwards countable family of measurable sets
is the infimum of the measures. -/
/-
**MeasureTheory._root_.Directed.measure_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Continuity from above**:
the measure of the intersection of a directed downwards countable family of meas
urable sets
is the infimum of the measures.
-/
theorem _root_.Directed.measure_iInter [Countable ι] {s : ι → Set α}
    (h : ∀ i, NullMeasurableSet (s i) μ) (hd : Directed (· ⊇ ·) s) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  rcases hfin with ⟨k, hk⟩
  have : ∀ t ⊆ s k, μ t ≠ ∞ := fun t ht => ne_top_of_le_ne_top hk (measure_mono ht)
  rw [← ENNReal.sub_sub_cancel hk (iInf_le (fun i => μ (s i)) k), ENNReal.sub_iInf, ←
    ENNReal.sub_sub_cancel hk (measure_mono (iInter_subset _ k)), ←
    measure_sdiff (iInter_subset _ k) (.iInter h) (this _ (iInter_subset _ k)),
    sdiff_iInter, Directed.measure_iUnion]
  · congr 1
    refine le_antisymm (iSup_mono' fun i => ?_) (iSup_mono fun i => le_measure_sdiff)
    rcases hd i k with ⟨j, hji, hjk⟩
    use j
    rw [← measure_sdiff hjk (h _) (this _ hjk)]
    gcongr
  · exact hd.mono_comp _ fun _ _ => sdiff_subset_sdiff_right

/-- **Continuity from above**:
the measure of the intersection of a monotone family of measurable sets
indexed by a type with countably generated `atBot` filter
is equal to the infimum of the measures. -/
/-
**MeasureTheory._root_.Monotone.measure_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Continuity from above**:
the measure of the intersection of a monotone family of measurable sets
indexed by a type with countably generated `atBot` filter
is equal to the infimum of the measures.
-/
theorem _root_.Monotone.measure_iInter [Preorder ι] [IsCodirectedOrder ι]
    [(atBot : Filter ι).IsCountablyGenerated] {s : ι → Set α} (hs : Monotone s)
    (hsm : ∀ i, NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  refine le_antisymm (le_iInf fun i ↦ measure_mono <| iInter_subset _ _) ?_
  have := hfin.nonempty
  rcases exists_seq_antitone_tendsto_atTop_atBot ι with ⟨x, hxm, hx⟩
  calc
    ⨅ i, μ (s i) ≤ ⨅ n, μ (s (x n)) := le_iInf_comp (μ ∘ s) x
    _ = μ (⋂ n, s (x n)) := by
      refine .symm <| (hs.comp_antitone hxm).directed_ge.measure_iInter (fun n ↦ hsm _) ?_
      rcases hfin with ⟨k, hk⟩
      rcases (hx.eventually_le_atBot k).exists with ⟨n, hn⟩
      exact ⟨n, ne_top_of_le_ne_top hk <| measure_mono <| hs hn⟩
    _ ≤ μ (⋂ i, s i) := by
      refine measure_mono <| iInter_mono' fun i ↦ ?_
      rcases (hx.eventually_le_atBot i).exists with ⟨n, hn⟩
      exact ⟨n, hs hn⟩

/-- Continuity from above (a.e. version):
the measure of the intersection of a family of sets that is almost everywhere monotone
is equal to the infimum of the measures. -/
/-
**MeasureTheory.measure_iInter_of_ae_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：measure_iInter_of_ae_monotone [Preorder ι] [IsCodirectedOrder ι] [(atBot :
 Filter ι).IsCountablyGenerated] {s : ι -> Set α} (hs : forallᵐ ω ∂μ, Monotone (
ω in s ·)) (hsm : forall i, NullMeasurableSet (s i) μ) (hfin : exists i, μ (s i)
 != ∞) : μ (⋂ i, s i) = ⨅ i, μ (s i)
参数：atBot : Filter ι；hs : forallᵐ ω ∂μ, Monotone (ω in s ·)；hsm : forall i, NullM
easurableSet (s i) μ；hfin : exists i, μ (s i) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `iInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι →
 α}, (∀ (i : ι), f i = g i) → ⨅ i, f i = ⨅ i, g i
· 使用定理 `MeasureTheory.measure_congr`：measure_congr (H : s =ᵐ[μ] t) : μ s = μ t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.measure_iInter`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsCodirectedOrder 
ι] [Filter.at…
· 使用定理 `MeasureTheory.NullMeasurableSet.congr`：∀ {α : Type u_2} {m0 : Measurable
Space α} {μ : MeasureTheory.Measure α} {s t : Set α},   MeasureTheory.NullMeasur
ableSet s μ → s =ᵐ[μ] t → M…
· 使用定理 `Set.iInter_inter`：iInter_inter [Nonempty ι] (s : Set β) (t : ι -> Set β)
 : (⋂ i, t i) inter s = ⋂ i, t i inter s
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `MeasureTheory.ae_eq_set_inter`：ae_eq_set_inter {s' t' : Set α} (h : s =ᵐ
[μ] t) (h' : s' =ᵐ[μ] t') : (s inter s' : Set α) =ᵐ[μ] (t inter t' : Set α)
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_eq_univ`：ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0

--- 原说明 ---
Continuity from above (a.e. version):
the measure of the intersection of a family of sets that is almost everywhere mo
notone
is equal to the infimum of the measures.
-/
theorem measure_iInter_of_ae_monotone [Preorder ι] [IsCodirectedOrder ι]
    [(atBot : Filter ι).IsCountablyGenerated] {s : ι → Set α} (hs : ∀ᵐ ω ∂μ, Monotone (ω ∈ s ·))
    (hsm : ∀ i, NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  obtain ⟨i, hi⟩ := hfin
  have : Nonempty ι := ⟨i⟩
  let t : ι → Set α := fun i ↦ s i ∩ {ω | Monotone (ω ∈ s ·)}
  have hst (i : ι) : s i =ᵐ[μ] t i := by
    filter_upwards [hs] with ω hω
    suffices ω ∈ s i ↔ ω ∈ t i from propext this
    simpa [t] using fun _ ↦ hω
  have hMono : Monotone t := fun i j hij ω hω ↦ ⟨hω.2 hij hω.1, hω.2⟩
  rw [iInf_congr <| fun i ↦ measure_congr <| hst i,
    ← hMono.measure_iInter (fun i ↦ (hsm i).congr (hst i)) ⟨i, by rwa [← measure_congr (hst i)]⟩]
  refine measure_congr ?_
  nth_rw 1 [← iInter_inter, ← inter_univ (⋂ i, s i)]
  exact ae_eq_set_inter (by rfl) (ae_eq_univ.2 hs).symm

/-- **Continuity from above**:
the measure of the intersection of an antitone family of measurable sets
indexed by a type with countably generated `atTop` filter
is equal to the infimum of the measures. -/
/-
**MeasureTheory._root_.Antitone.measure_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Continuity from above**:
the measure of the intersection of an antitone family of measurable sets
indexed by a type with countably generated `atTop` filter
is equal to the infimum of the measures.
-/
theorem _root_.Antitone.measure_iInter [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι → Set α} (hs : Antitone s)
    (hsm : ∀ i, NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) :=
  hs.dual_left.measure_iInter hsm hfin

/-- Continuity from above (a.e. version):
the measure of the intersection of a family of sets that is almost everywhere antitone
is equal to the infimum of the measures. -/
/-
**MeasureTheory.measure_iInter_of_ae_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Measure
Theory`。
形式化陈述：measure_iInter_of_ae_antitone [Preorder ι] [IsDirectedOrder ι] [(atTop : F
ilter ι).IsCountablyGenerated] {s : ι -> Set α} (hs : forallᵐ ω ∂μ, Antitone (ω 
in s ·)) (hsm : forall (i : ι), NullMeasurableSet (s i) μ) (hfin : exists i, μ (
s i) != ∞) : μ (⋂ i, s i) = ⨅ i, μ (s i)
参数：atTop : Filter ι；hs : forallᵐ ω ∂μ, Antitone (ω in s ·)；hsm : forall (i : ι),
 NullMeasurableSet (s i) μ；hfin : exists i, μ (s i) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.measure_iInter_of_ae_monotone`：measure_iInter_of_ae_monoto
ne [Preorder ι] [IsCodirectedOrder ι] [(atBot : Filter ι).IsCountablyGenerated] 
{s : ι -> Set α} (hs : forallᵐ ω …
· 使用定理 `OrderDual.instIsCountablyGeneratedAtBot`：∀ {α : Type u_1} [inst : Preord
er α] [Filter.atTop.IsCountablyGenerated], Filter.atBot.IsCountablyGenerated
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)

--- 原说明 ---
Continuity from above (a.e. version):
the measure of the intersection of a family of sets that is almost everywhere an
titone
is equal to the infimum of the measures.
-/
lemma measure_iInter_of_ae_antitone [Preorder ι] [IsDirectedOrder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι → Set α} (hs : ∀ᵐ ω ∂μ, Antitone (ω ∈ s ·))
    (hsm : ∀ (i : ι), NullMeasurableSet (s i) μ) (hfin : ∃ i, μ (s i) ≠ ∞) :
    μ (⋂ i, s i) = ⨅ i, μ (s i) := by
  refine measure_iInter_of_ae_monotone (ι := ιᵒᵈ) ?_ hsm hfin
  filter_upwards [hs] with ω hω using hω.dual_left

/-- Continuity from above: the measure of the intersection of a sequence of
measurable sets is the infimum of the measures of the partial intersections. -/
/-
**MeasureTheory.measure_iInter_eq_iInf_measure_iInter_le** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：measure_iInter_eq_iInf_measure_iInter_le {α ι : Type*} {_ : MeasurableSpac
e α} {μ : Measure α} [Countable ι] [Preorder ι] [IsDirectedOrder ι] {f : ι -> Se
t α} (h : forall i, NullMeasurableSet (f i) μ) (hfin : exists i, μ (f i) != ∞) :
 μ (⋂ i, f i) = ⨅ i, μ (⋂ j <= i, f j)
参数：h : forall i, NullMeasurableSet (f i) μ；hfin : exists i, μ (f i) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Antitone.measure_iInter`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsDirectedOrder ι]
 [Filter.atTo…
· 使用定理 `Filter.atTop.isCountablyGenerated`：∀ {α : Type u_1} [inst : Preorder α] 
[Countable α], Filter.atTop.IsCountablyGenerated
· 使用定理 `Set.biInter_mono`：biInter_mono {s s' : Set α} {t t' : α -> Set β} (hs : 
s subseteq s') (h : forall x in s, t x subseteq t' x) : ⋂ x in s', t x subseteq 
⋂ x in…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `MeasureTheory.NullMeasurableSet.biInter`：∀ {α : Type u_2} {β : Type u_3}
 {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : β → Set α} {s : Set
 β},   s.Countable → (∀ b ∈ s…
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.iInter_comm`：iInter_comm (s : ι -> ι' -> Set α) : ⋂ (i) (i'), s i i'
 = ⋂ (i') (i), s i i'
· 使用引理 `Set.iInter_congr`：iInter_congr {s t : ι -> Set α} (h : forall i, s i = t
 i) : ⋂ i, s i = ⋂ i, t i
· 使用定理 `biInf_const`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] 
{a : α} {s : Set β}, s.Nonempty → ⨅ i ∈ s, a = a
· 使用定理 `Set.nonempty_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set.Ici
 a).Nonempty

--- 原说明 ---
Continuity from above: the measure of the intersection of a sequence of
measurable sets is the infimum of the measures of the partial intersections.
-/
theorem measure_iInter_eq_iInf_measure_iInter_le {α ι : Type*} {_ : MeasurableSpace α}
    {μ : Measure α} [Countable ι] [Preorder ι] [IsDirectedOrder ι]
    {f : ι → Set α} (h : ∀ i, NullMeasurableSet (f i) μ) (hfin : ∃ i, μ (f i) ≠ ∞) :
    μ (⋂ i, f i) = ⨅ i, μ (⋂ j ≤ i, f j) := by
  rw [← Antitone.measure_iInter]
  · rw [iInter_comm]
    exact congrArg μ <| iInter_congr fun i ↦ (biInf_const nonempty_Ici).symm
  · exact fun i j h ↦ biInter_mono (Iic_subset_Iic.2 h) fun _ _ ↦ Set.Subset.rfl
  · exact fun i ↦ .biInter (to_countable _) fun _ _ ↦ h _
  · refine hfin.imp fun k hk ↦ ne_top_of_le_ne_top hk <| measure_mono <| iInter₂_subset k ?_
    rfl

/-- Continuity from below: the measure of the union of an increasing sequence of (not necessarily
measurable) sets is the limit of the measures. -/
/-
**MeasureTheory.tendsto_measure_iUnion_atTop** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：tendsto_measure_iUnion_atTop [Preorder ι] [IsCountablyGenerated (atTop : F
ilter ι)] {s : ι -> Set α} (hm : Monotone s) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n,
 s n)))
参数：atTop : Filter ι；hm : Monotone s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.of_neBot_imp`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {la : Filter α} {lb : Filter β},   (la.NeBot → Filter.Tendsto f la lb) → Filter
.Tendsto f la lb
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.atTop_neBot_iff`：atTop_neBot_iff {α : Type*} [Preorder α] : (atTo
p : Filter α).NeBot ↔ Nonempty α ∧ IsDirectedOrder α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monotone.measure_iUnion`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsDirectedOrder ι]
 [Filter.atTo…
· 使用定理 `tendsto_atTop_iSup`：tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f
 atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Continuity from below: the measure of the union of an increasing sequence of (no
t necessarily
measurable) sets is the limit of the measures.
-/
theorem tendsto_measure_iUnion_atTop [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    {s : ι → Set α} (hm : Monotone s) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋃ n, s n))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iUnion]
  exact tendsto_atTop_iSup fun n m hnm => measure_mono <| hm hnm
/-
**MeasureTheory.tendsto_measure_iUnion_atBot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：tendsto_measure_iUnion_atBot [Preorder ι] [IsCountablyGenerated (atBot : F
ilter ι)] {s : ι -> Set α} (hm : Antitone s) : Tendsto (μ ∘ s) atBot (𝓝 (μ (⋃ n,
 s n)))
参数：atBot : Filter ι；hm : Antitone s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_measure_iUnion_atTop`：tendsto_measure_iUnion_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hm : M
onotone s) : Tendsto (μ ∘ s) atT…
· 使用定理 `OrderDual.instIsCountablyGeneratedAtTop`：∀ {α : Type u_1} [inst : Preord
er α] [Filter.atBot.IsCountablyGenerated], Filter.atTop.IsCountablyGenerated
· 使用定理 `Antitone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Antitone f → Monotone (f ∘ ⇑OrderDual.ofDual)
-/
theorem tendsto_measure_iUnion_atBot [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)]
    {s : ι → Set α} (hm : Antitone s) : Tendsto (μ ∘ s) atBot (𝓝 (μ (⋃ n, s n))) :=
  tendsto_measure_iUnion_atTop (ι := ιᵒᵈ) hm.dual_left

/-- Continuity from below: the measure of the union of a sequence of (not necessarily measurable)
sets is the limit of the measures of the partial unions. -/
/-
**MeasureTheory.tendsto_measure_iUnion_accumulate** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：tendsto_measure_iUnion_accumulate {α ι : Type*} [Preorder ι] [IsCountablyG
enerated (atTop : Filter ι)] {_ : MeasurableSpace α} {μ : Measure α} {f : ι -> S
et α} : Tendsto (fun i => μ (accumulate f i)) atTop (𝓝 (μ (⋃ i, f i)))
参数：atTop : Filter ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.of_neBot_imp`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {la : Filter α} {lb : Filter β},   (la.NeBot → Filter.Tendsto f la lb) → Filter
.Tendsto f la lb
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.atTop_neBot_iff`：atTop_neBot_iff {α : Type*} [Preorder α] : (atTo
p : Filter α).NeBot ↔ Nonempty α ∧ IsDirectedOrder α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_iUnion_eq_iSup_accumulate`：measure_iUnion_eq_iSup_
accumulate [Preorder ι] [IsDirectedOrder ι] [(atTop : Filter ι).IsCountablyGener
ated] {f : ι -> Set α} : μ (⋃ i, f i)…
· 使用定理 `tendsto_atTop_iSup`：tendsto_atTop_iSup (h_mono : Monotone f) : Tendsto f
 atTop (𝓝 (⨆ i, f i))
· 使用定理 `LinearOrder.supConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], SupConvergenceClass α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.accumulate_subset_accumulate`：accumulate_subset_accumulate [Preorder
 α] {x y} (h : x <= y) : accumulate s x subseteq accumulate s y

--- 原说明 ---
Continuity from below: the measure of the union of a sequence of (not necessaril
y measurable)
sets is the limit of the measures of the partial unions.
-/
theorem tendsto_measure_iUnion_accumulate {α ι : Type*}
    [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)]
    {_ : MeasurableSpace α} {μ : Measure α} {f : ι → Set α} :
    Tendsto (fun i ↦ μ (accumulate f i)) atTop (𝓝 (μ (⋃ i, f i))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [measure_iUnion_eq_iSup_accumulate]
  exact tendsto_atTop_iSup fun i j hij ↦ by gcongr

/-- Continuity from above: the measure of the intersection of a decreasing sequence of measurable
sets is the limit of the measures. -/
/-
**MeasureTheory.tendsto_measure_iInter_atTop** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：tendsto_measure_iInter_atTop [Preorder ι] [IsCountablyGenerated (atTop : F
ilter ι)] {s : ι -> Set α} (hs : forall i, NullMeasurableSet (s i) μ) (hm : Anti
tone s) (hf : exists i, μ (s i) != ∞) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋂ n, s n)))
参数：atTop : Filter ι；hs : forall i, NullMeasurableSet (s i) μ；hm : Antitone s；hf 
: exists i, μ (s i) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.of_neBot_imp`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {la : Filter α} {lb : Filter β},   (la.NeBot → Filter.Tendsto f la lb) → Filter
.Tendsto f la lb
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.atTop_neBot_iff`：atTop_neBot_iff {α : Type*} [Preorder α] : (atTo
p : Filter α).NeBot ↔ Nonempty α ∧ IsDirectedOrder α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Antitone.measure_iInter`：∀ {α : Type u_1} {ι : Type u_5} {m : Measurable
Space α} {μ : MeasureTheory.Measure α} [inst : Preorder ι]   [IsDirectedOrder ι]
 [Filter.atTo…
· 使用定理 `tendsto_atTop_iInf`：tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f
 atTop (𝓝 (⨅ i, f i))
· 使用定理 `LinearOrder.infConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], InfConvergenceClass α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
Continuity from above: the measure of the intersection of a decreasing sequence 
of measurable
sets is the limit of the measures.
-/
theorem tendsto_measure_iInter_atTop [Preorder ι]
    [IsCountablyGenerated (atTop : Filter ι)] {s : ι → Set α}
    (hs : ∀ i, NullMeasurableSet (s i) μ) (hm : Antitone s) (hf : ∃ i, μ (s i) ≠ ∞) :
    Tendsto (μ ∘ s) atTop (𝓝 (μ (⋂ n, s n))) := by
  refine .of_neBot_imp fun h ↦ ?_
  have := (atTop_neBot_iff.1 h).2
  rw [hm.measure_iInter hs hf]
  exact tendsto_atTop_iInf fun n m hnm => measure_mono <| hm hnm

/-- Continuity from above: the measure of the intersection of an increasing sequence of measurable
sets is the limit of the measures. -/
/-
**MeasureTheory.tendsto_measure_iInter_atBot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：tendsto_measure_iInter_atBot [Preorder ι] [IsCountablyGenerated (atBot : F
ilter ι)] {s : ι -> Set α} (hs : forall i, NullMeasurableSet (s i) μ) (hm : Mono
tone s) (hf : exists i, μ (s i) != ∞) : Tendsto (μ ∘ s) atBot (𝓝 (μ (⋂ n, s n)))
参数：atBot : Filter ι；hs : forall i, NullMeasurableSet (s i) μ；hm : Monotone s；hf 
: exists i, μ (s i) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_measure_iInter_atTop`：tendsto_measure_iInter_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hs : f
orall i, NullMeasurableSet (s i)…
· 使用定理 `OrderDual.instIsCountablyGeneratedAtTop`：∀ {α : Type u_1} [inst : Preord
er α] [Filter.atBot.IsCountablyGenerated], Filter.atTop.IsCountablyGenerated
· 使用定理 `Monotone.dual_left`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [ins
t_1 : Preorder β] {f : α → β},   Monotone f → Antitone (f ∘ ⇑OrderDual.ofDual)

--- 原说明 ---
Continuity from above: the measure of the intersection of an increasing sequence
 of measurable
sets is the limit of the measures.
-/
theorem tendsto_measure_iInter_atBot [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)]
    {s : ι → Set α} (hs : ∀ i, NullMeasurableSet (s i) μ) (hm : Monotone s)
    (hf : ∃ i, μ (s i) ≠ ∞) : Tendsto (μ ∘ s) atBot (𝓝 (μ (⋂ n, s n))) :=
  tendsto_measure_iInter_atTop (ι := ιᵒᵈ) hs hm.dual_left hf

/-- Continuity from above: the measure of the intersection of a sequence of measurable
sets such that one has finite measure is the limit of the measures of the partial intersections. -/
/-
**MeasureTheory.tendsto_measure_iInter_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_measure_iInter_le {α ι : Type*} {_ : MeasurableSpace α} {μ : Measu
re α} [Countable ι] [Preorder ι] {f : ι -> Set α} (hm : forall i, NullMeasurable
Set (f i) μ) (hf : exists i, μ (f i) != ∞) : Tendsto (fun i => μ (⋂ j <= i, f j)
) atTop (𝓝 (μ (⋂ i, f i)))
参数：hm : forall i, NullMeasurableSet (f i) μ；hf : exists i, μ (f i) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.of_neBot_imp`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {la : Filter α} {lb : Filter β},   (la.NeBot → Filter.Tendsto f la lb) → Filter
.Tendsto f la lb
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.atTop_neBot_iff`：atTop_neBot_iff {α : Type*} [Preorder α] : (atTo
p : Filter α).NeBot ↔ Nonempty α ∧ IsDirectedOrder α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_iInter_eq_iInf_measure_iInter_le`：measure_iInter_e
q_iInf_measure_iInter_le {α ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} [
Countable ι] [Preorder ι] [IsDirectedOrder ι…
· 使用定理 `tendsto_atTop_iInf`：tendsto_atTop_iInf (h_anti : Antitone f) : Tendsto f
 atTop (𝓝 (⨅ i, f i))
· 使用定理 `LinearOrder.infConvergenceClass`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : LinearOrder α] [OrderTopology α], InfConvergenceClass α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.biInter_subset_biInter_left`：biInter_subset_biInter_left {s s' : Set
 α} {t : α -> Set β} (h : s' subseteq s) : ⋂ x in s, t x subseteq ⋂ x in s', t x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c

--- 原说明 ---
Continuity from above: the measure of the intersection of a sequence of measurab
le
sets such that one has finite measure is the limit of the measures of the partia
l intersections.
-/
theorem tendsto_measure_iInter_le {α ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [Countable ι] [Preorder ι] {f : ι → Set α} (hm : ∀ i, NullMeasurableSet (f i) μ)
    (hf : ∃ i, μ (f i) ≠ ∞) :
    Tendsto (fun i ↦ μ (⋂ j ≤ i, f j)) atTop (𝓝 (μ (⋂ i, f i))) := by
  refine .of_neBot_imp fun hne ↦ ?_
  cases atTop_neBot_iff.mp hne
  rw [measure_iInter_eq_iInf_measure_iInter_le hm hf]
  exact tendsto_atTop_iInf
    fun i j hij ↦ measure_mono <| biInter_subset_biInter_left fun k hki ↦ le_trans hki hij

/-- Some version of continuity of a measure in the empty set using the intersection along a set of
sets. -/
/-
**MeasureTheory.exists_measure_iInter_lt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：exists_measure_iInter_lt {α ι : Type*} {_ : MeasurableSpace α} {μ : Measur
e α} [SemilatticeSup ι] [Countable ι] {f : ι -> Set α} (hm : forall i, NullMeasu
rableSet (f i) μ) {ε : Real>=0∞} (hε : 0 < ε) (hfin : exists i, μ (f i) != ∞) (h
fem : ⋂ n, f n = ∅) : exists m, μ (⋂ n <= m, f n) < ε
参数：hm : forall i, NullMeasurableSet (f i) μ；hε : 0 < ε；hfin : exists i, μ (f i) 
!= ∞；hfem : ⋂ n, f n = ∅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.biInter_subset_biInter_left`：biInter_subset_biInter_left {s s' : Set
 α} {t : α -> Set β} (h : s' subseteq s) : ⋂ x in s, t x subseteq ⋂ x in s', t x
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.tendsto_measure_iInter_le`：tendsto_measure_iInter_le {α ι 
: Type*} {_ : MeasurableSpace α} {μ : Measure α} [Countable ι] [Preorder ι] {f :
 ι -> Set α} (hm : forall i, …
· 使用定理 `Exists.nonempty`：∀ {α : Sort u_1} {p : α → Prop}, (∃ x, p x) → Nonempty 
α
· 使用定理 `ENNReal.tendsto_atTop_zero_iff_lt_of_antitone`：tendsto_atTop_zero_iff_lt
_of_antitone {β : Type*} [Nonempty β] [SemilatticeSup β] {f : β -> Real>=0∞} (hf
 : Antitone f) : Filter.Tendsto f F…

--- 原说明 ---
Some version of continuity of a measure in the empty set using the intersection 
along a set of
sets.
-/
theorem exists_measure_iInter_lt {α ι : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [SemilatticeSup ι] [Countable ι] {f : ι → Set α}
    (hm : ∀ i, NullMeasurableSet (f i) μ) {ε : ℝ≥0∞} (hε : 0 < ε) (hfin : ∃ i, μ (f i) ≠ ∞)
    (hfem : ⋂ n, f n = ∅) : ∃ m, μ (⋂ n ≤ m, f n) < ε := by
  let F m := μ (⋂ n ≤ m, f n)
  have hFAnti : Antitone F :=
      fun i j hij => measure_mono (biInter_subset_biInter_left fun k hki => le_trans hki hij)
  suffices Filter.Tendsto F Filter.atTop (𝓝 0) by
    let _ := hfin.nonempty
    rw [ENNReal.tendsto_atTop_zero_iff_lt_of_antitone hFAnti] at this
    exact this ε hε
  have hzero : μ (⋂ n, f n) = 0 := by
    simp only [hfem, measure_empty]
  rw [← hzero]
  exact tendsto_measure_iInter_le hm hfin

/-- The measure of the intersection of a decreasing sequence of measurable
sets indexed by a linear order with first countable topology is the limit of the measures. -/
/-
**MeasureTheory.tendsto_measure_biInter_gt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：tendsto_measure_biInter_gt {ι : Type*} [LinearOrder ι] [TopologicalSpace ι
] [OrderTopology ι] [FirstCountableTopology ι] {s : ι -> Set α} {a : ι} (hs : fo
rall r > a, NullMeasurableSet (s r) μ) (hm : forall i j, a < i -> i <= j -> s i 
subseteq s j) (hf : exists r > a, μ (s r) != ∞) : Tendsto (μ ∘ s) (𝓝[Ioi a] a) (
𝓝 (μ (⋂ r > a, s r)))
参数：hs : forall r > a, NullMeasurableSet (s r) μ；hm : forall i j, a < i -> i <= j
 -> s i subseteq s j；hf : exists r > a, μ (s r) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `comap_coe_Ioi_nhdsGT`：comap_coe_Ioi_nhdsGT (a : X) (ha : IsPredPrelimit 
a
· 使用定理 `Filter.comap.isCountablyGenerated`：∀ {α : Type u_1} {β : Type u_2} (l : 
Filter β) [l.IsCountablyGenerated] (f : α → β),   (Filter.comap f l).IsCountably
Generated
· 使用定理 `FirstCountableTopology.nhds_generated_countable`：∀ {α : Type u} {t : Top
ologicalSpace α} [self : FirstCountableTopology α] (a : α), (nhds a).IsCountably
Generated
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_coe_Ioi_atBot`：map_coe_Ioi_atBot (a : X) (ha : IsPredPrelimit a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `MeasureTheory.tendsto_measure_iInter_atBot`：tendsto_measure_iInter_atBot
 [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)] {s : ι -> Set α} (hs : f
orall i, NullMeasurableSet (s i)…
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Order.not_isPredPrelimit_iff`：∀ {α : Type u_1} [inst : LT α] {a : α}, ¬O
rder.IsPredPrelimit a ↔ ∃ b, a ⋖ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CovBy.nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b ⋖ a → nhdsWithin b (Set.Ioi b) = 
⊥
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α

--- 原说明 ---
The measure of the intersection of a decreasing sequence of measurable
sets indexed by a linear order with first countable topology is the limit of the
 measures.
-/
theorem tendsto_measure_biInter_gt {ι : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderTopology ι] [FirstCountableTopology ι] {s : ι → Set α}
    {a : ι} (hs : ∀ r > a, NullMeasurableSet (s r) μ) (hm : ∀ i j, a < i → i ≤ j → s i ⊆ s j)
    (hf : ∃ r > a, μ (s r) ≠ ∞) : Tendsto (μ ∘ s) (𝓝[Ioi a] a) (𝓝 (μ (⋂ r > a, s r))) := by
  by_cases ha : Order.IsPredPrelimit a
  · have : (atBot : Filter (Ioi a)).IsCountablyGenerated := by
      rw [← comap_coe_Ioi_nhdsGT a ha]
      infer_instance
    simp_rw [← map_coe_Ioi_atBot a ha, tendsto_map'_iff, ← mem_Ioi, biInter_eq_iInter]
    apply tendsto_measure_iInter_atBot
    · rwa [Subtype.forall]
    · exact fun i j h ↦ hm i j i.2 h
    · simpa only [Subtype.exists, exists_prop]
  · rw [Order.not_isPredPrelimit_iff] at ha
    rcases ha with ⟨b, hab⟩
    simp [hab.nhdsGT]
/-
**MeasureTheory.measure_if** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：measure_if {x : β} {t : Set β} {s : Set α} [Decidable (x in t)] : μ (if x 
in t then s else ∅) = indicator t (fun _ => μ s) x
参数：x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem measure_if {x : β} {t : Set β} {s : Set α} [Decidable (x ∈ t)] :
    μ (if x ∈ t then s else ∅) = indicator t (fun _ => μ s) x := by split_ifs with h <;> simp [h]

/-- On a countable space, two measures are equal if they agree on measurable atoms. -/
/-
**MeasureTheory.ext_of_measurableAtoms** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`
。
形式化陈述：ext_of_measurableAtoms [Countable α] {μ ν : Measure α} (h : forall x, μ (m
easurableAtom x) = ν (measurableAtom x)) : μ = ν
参数：h : forall x, μ (measurableAtom x) = ν (measurableAtom x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mem_measurableAtom_self`：∀ {β : Type u_2} [inst : MeasurableSpace β] (x 
: β), x ∈ measurableAtom x
· 使用引理 `mem_of_mem_measurableAtom`：mem_of_mem_measurableAtom {x y : β} (h : y in
 measurableAtom x) {s : Set β} (hs : MeasurableSet s) (hxs : x in s) : y in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `Set.Countable.image`：∀ {α : Type u} {β : Type v} {s : Set α}, s.Countabl
e → ∀ (f : α → β), (f '' s).Countable
· 使用定理 `Set.to_countable`：to_countable (s : Set α) [Countable s] : s.Countable
· 使用定理 `SetCoe.countable`：∀ {α : Type u} [Countable α] (s : Set α), Countable ↑s
· 使用引理 `disjoint_measurableAtom_of_notMem`：disjoint_measurableAtom_of_notMem {x 
y : β} (hx : x ∉ measurableAtom y) : Disjoint (measurableAtom x) (measurableAtom
 y)
· 使用引理 `measurableAtom_eq_of_mem`：measurableAtom_eq_of_mem {x y : β} (hx : x in 
measurableAtom y) : measurableAtom x = measurableAtom y
· 使用引理 `MeasurableSet.measurableAtom_of_countable`：MeasurableSet.measurableAtom_
of_countable [Countable β] (x : β) : MeasurableSet (measurableAtom x)
· 使用定理 `MeasureTheory.measure_sUnion`：measure_sUnion {S : Set (Set α)} (hs : S.C
ountable) (hd : S.Pairwise Disjoint) (h : forall s in S, MeasurableSet s) : μ (⋃
₀ S) = ∑' s : S, μ…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
On a countable space, two measures are equal if they agree on measurable atoms.
-/
lemma ext_of_measurableAtoms [Countable α] {μ ν : Measure α}
    (h : ∀ x, μ (measurableAtom x) = ν (measurableAtom x)) : μ = ν := by
  ext s hs
  have h1 : s = ⋃ x ∈ s, measurableAtom x := by
    ext y
    simp only [mem_iUnion, exists_prop]
    refine ⟨fun hy ↦ ?_, fun ⟨x, hx, hy⟩ ↦ ?_⟩
    · exact ⟨y, hy, mem_measurableAtom_self y⟩
    · exact mem_of_mem_measurableAtom hy hs hx
  rw [← sUnion_image] at h1
  rw [h1]
  have h_count : (measurableAtom '' s).Countable := s.to_countable.image _
  have h_disj : (measurableAtom '' s).Pairwise Disjoint := by
    intro t ht t' ht' h_eq
    obtain ⟨y, hys, hy⟩ := ht
    obtain ⟨y', hy's, hy'⟩ := ht'
    rw [← hy, ← hy'] at h_eq ⊢
    refine disjoint_measurableAtom_of_notMem fun hyy' ↦ h_eq ?_
    exact measurableAtom_eq_of_mem hyy'
  have h_meas (t) (ht : t ∈ measurableAtom '' s) : MeasurableSet t := by
    obtain ⟨x, hxs, hx⟩ := ht
    rw [← hx]
    exact MeasurableSet.measurableAtom_of_countable x
  rw [measure_sUnion h_count h_disj h_meas, measure_sUnion h_count h_disj h_meas]
  congr with s'
  have hs' := s'.2
  obtain ⟨x, hxs, hx⟩ := hs'
  rw [← hx]
  exact h x

end

section OuterMeasure

variable [ms : MeasurableSpace α] {s t : Set α}

/-- Obtain a measure by giving an outer measure where all sets in the σ-algebra are
  Carathéodory measurable. -/
/-
**MeasureTheory.OuterMeasure.toMeasure** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.
OuterMeasure`。
形式化陈述：{α : Type u_1} →   [ms : MeasurableSpace α] → (m : MeasureTheory.OuterMeas
ure α) → ms ≤ m.caratheodory → MeasureTheory.Measure α
参数：m : MeasureTheory.OuterMeasure α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.empty`：∀ {α : Type u_2} (self : MeasureTheory
.OuterMeasure α), self.measureOf ∅ = 0

--- 原说明 ---
Obtain a measure by giving an outer measure where all sets in the σ-algebra are
  Carathéodory measurable.
-/
def OuterMeasure.toMeasure (m : OuterMeasure α) (h : ms ≤ m.caratheodory) : Measure α :=
  Measure.ofMeasurable (fun s _ => m s) m.empty fun _f hf hd =>
    m.iUnion_eq_of_caratheodory (fun i => h _ (hf i)) hd
/-
**MeasureTheory.le_toOuterMeasure_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：le_toOuterMeasure_caratheodory (μ : Measure α) : ms <= μ.toOuterMeasure.ca
ratheodory
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
-/
theorem le_toOuterMeasure_caratheodory (μ : Measure α) : ms ≤ μ.toOuterMeasure.caratheodory :=
  fun _s hs _t => (measure_inter_add_sdiff _ hs).symm

@[simp]
/-
**MeasureTheory.toMeasure_toOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：toMeasure_toOuterMeasure (m : OuterMeasure α) (h : ms <= m.caratheodory) :
 (m.toMeasure h).toOuterMeasure = m.trim
参数：m : OuterMeasure α；h : ms <= m.caratheodory。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMeasure_toOuterMeasure (m : OuterMeasure α) (h : ms ≤ m.caratheodory) :
    (m.toMeasure h).toOuterMeasure = m.trim :=
  rfl

@[simp]
/-
**MeasureTheory.toMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：toMeasure_apply (m : OuterMeasure α) (h : ms <= m.caratheodory) {s : Set α
} (hs : MeasurableSet s) : m.toMeasure h s = m s
参数：m : OuterMeasure α；h : ms <= m.caratheodory；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq`：trim_eq {s : Set α} (hs : Measurable
Set s) : m.trim s = m s
-/
theorem toMeasure_apply (m : OuterMeasure α) (h : ms ≤ m.caratheodory) {s : Set α}
    (hs : MeasurableSet s) : m.toMeasure h s = m s :=
  m.trim_eq hs
/-
**MeasureTheory.le_toMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：le_toMeasure_apply (m : OuterMeasure α) (h : ms <= m.caratheodory) (s : Se
t α) : m s <= m.toMeasure h s
参数：m : OuterMeasure α；h : ms <= m.caratheodory；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.le_trim`：le_trim : m <= m.trim
-/
theorem le_toMeasure_apply (m : OuterMeasure α) (h : ms ≤ m.caratheodory) (s : Set α) :
    m s ≤ m.toMeasure h s :=
  m.le_trim s
/-
**MeasureTheory.toMeasure_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：toMeasure_apply (m : OuterMeasure α) (h : ms <= m.caratheodory) {s : Set α
} (hs : MeasurableSet s) : m.toMeasure h s = m s
参数：m : OuterMeasure α；h : ms <= m.caratheodory；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq`：trim_eq {s : Set α} (hs : Measurable
Set s) : m.trim s = m s
-/
theorem toMeasure_apply₀ (m : OuterMeasure α) (h : ms ≤ m.caratheodory) {s : Set α}
    (hs : NullMeasurableSet s (m.toMeasure h)) : m.toMeasure h s = m s := by
  refine le_antisymm ?_ (le_toMeasure_apply _ _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, hts, htm, heq⟩
  calc
    m.toMeasure h s = m.toMeasure h t := measure_congr heq.symm
    _ = m t := toMeasure_apply m h htm
    _ ≤ m s := m.mono hts

@[simp]
/-
**MeasureTheory.toOuterMeasure_toMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：toOuterMeasure_toMeasure {μ : Measure α} : μ.toOuterMeasure.toMeasure (le_
toOuterMeasure_caratheodory _) = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `MeasureTheory.le_toOuterMeasure_caratheodory`：le_toOuterMeasure_caratheo
dory (μ : Measure α) : ms <= μ.toOuterMeasure.caratheodory
· 使用定理 `MeasureTheory.OuterMeasure.trim_eq`：trim_eq {s : Set α} (hs : Measurable
Set s) : m.trim s = m s
-/
theorem toOuterMeasure_toMeasure {μ : Measure α} :
    μ.toOuterMeasure.toMeasure (le_toOuterMeasure_caratheodory _) = μ :=
  Measure.ext fun _s => μ.toOuterMeasure.trim_eq

@[simp]
/-
**MeasureTheory.boundedBy_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：boundedBy_measure (μ : Measure α) : OuterMeasure.boundedBy μ = μ.toOuterMe
asure
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_eq_self`：boundedBy_eq_self (m : Out
erMeasure α) : boundedBy m = m
-/
theorem boundedBy_measure (μ : Measure α) : OuterMeasure.boundedBy μ = μ.toOuterMeasure :=
  μ.toOuterMeasure.boundedBy_eq_self

end OuterMeasure

section

variable {m0 : MeasurableSpace α} {mβ : MeasurableSpace β} [MeasurableSpace γ]
variable {μ μ₁ μ₂ μ₃ ν ν' ν₁ ν₂ : Measure α} {s s' t : Set α}
namespace Measure

/-- If `u` is a superset of `t` with the same (finite) measure (both sets possibly non-measurable),
then for any measurable set `s` one also has `μ (t ∩ s) = μ (u ∩ s)`. -/
/-
**MeasureTheory.Measure.measure_inter_eq_of_measure_eq** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.Measure`。
形式化陈述：measure_inter_eq_of_measure_eq {s t u : Set α} (hs : MeasurableSet s) (h :
 μ t = μ u) (htu : t subseteq u) (ht_ne_top : μ t != ∞) : μ (t inter s) = μ (u i
nter s)
参数：hs : MeasurableSet s；h : μ t = μ u；htu : t subseteq u；ht_ne_top : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `sdiff_le_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] 
{a b c d : α}, d ≤ c → b ≤ a → d \ a ≤ c \ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.le_of_add_le_add_right`：∀ {a b c : ENNReal}, a ≠ ⊤ → b + a ≤ c +
 a → b ≤ c

--- 原说明 ---
If `u` is a superset of `t` with the same (finite) measure (both sets possibly n
on-measurable),
then for any measurable set `s` one also has `μ (t ∩ s) = μ (u ∩ s)`.
-/
theorem measure_inter_eq_of_measure_eq {s t u : Set α} (hs : MeasurableSet s) (h : μ t = μ u)
    (htu : t ⊆ u) (ht_ne_top : μ t ≠ ∞) : μ (t ∩ s) = μ (u ∩ s) := by
  rw [h] at ht_ne_top
  refine le_antisymm (by gcongr) ?_
  have A : μ (u ∩ s) + μ (u \ s) ≤ μ (t ∩ s) + μ (u \ s) :=
    calc
      μ (u ∩ s) + μ (u \ s) = μ u := measure_inter_add_sdiff _ hs
      _ = μ t := h.symm
      _ = μ (t ∩ s) + μ (t \ s) := (measure_inter_add_sdiff _ hs).symm
      _ ≤ μ (t ∩ s) + μ (u \ s) := by gcongr
  have B : μ (u \ s) ≠ ∞ := (lt_of_le_of_lt (measure_mono sdiff_subset) ht_ne_top.lt_top).ne
  exact ENNReal.le_of_add_le_add_right B A
/-
**MeasureTheory.Measure.measure_inter_eq_of_ae** 是 Mathlib 中的一个引理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：measure_inter_eq_of_ae {s t : Set α} (h : forallᵐ a ∂μ, a in t) : μ (t int
er s) = μ s
参数：h : forallᵐ a ∂μ, a in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Filter.EventuallyLE.measure_le`：∀ {α : Type u_1} {F : Type u_3} [inst : 
FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F α]   {μ :
 F} {s t : Set α}, s…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma measure_inter_eq_of_ae {s t : Set α} (h : ∀ᵐ a ∂μ, a ∈ t) :
    μ (t ∩ s) = μ s := by
  refine le_antisymm (measure_mono inter_subset_right) ?_
  apply EventuallyLE.measure_le
  filter_upwards [h] with x hx h'x using ⟨hx, h'x⟩

/-- The measurable superset `toMeasurable μ t` of `t` (which has the same measure as `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = μ (u ∩ s)`.
Here, we require that the measure of `t` is finite. The conclusion holds without this assumption
when the measure is s-finite (for example when it is σ-finite),
see `measure_toMeasurable_inter_of_sFinite`. -/
/-
**MeasureTheory.Measure.measure_toMeasurable_inter** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：measure_toMeasurable_inter {s t : Set α} (hs : MeasurableSet s) (ht : μ t 
!= ∞) : μ (toMeasurable μ t inter s) = μ (t inter s)
参数：hs : MeasurableSet s；ht : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_inter_eq_of_measure_eq`：measure_inter_eq_o
f_measure_eq {s t u : Set α} (hs : MeasurableSet s) (h : μ t = μ u) (htu : t sub
seteq u) (ht_ne_top : μ t != ∞) : μ (t int…
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s

--- 原说明 ---
The measurable superset `toMeasurable μ t` of `t` (which has the same measure as
 `t`)
satisfies, for any measurable set `s`, the equality `μ (toMeasurable μ t ∩ s) = 
μ (u ∩ s)`.
Here, we require that the measure of `t` is finite. The conclusion holds without
 this assumption
when the measure is s-finite (for example when it is σ-finite),
see `measure_toMeasurable_inter_of_sFinite`.
-/
theorem measure_toMeasurable_inter {s t : Set α} (hs : MeasurableSet s) (ht : μ t ≠ ∞) :
    μ (toMeasurable μ t ∩ s) = μ (t ∩ s) :=
  (measure_inter_eq_of_measure_eq hs (measure_toMeasurable t).symm (subset_toMeasurable μ t)
      ht).symm

/-! ### The `ℝ≥0∞`-module of measures -/

/-
**MeasureTheory.Measure.instZero** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：instZero {_ : MeasurableSpace α} : Zero (Measure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### The `ℝ≥0∞`-module of measures
-/
instance instZero {_ : MeasurableSpace α} : Zero (Measure α) :=
  ⟨{  toOuterMeasure := 0
      m_iUnion := fun _f _hf _hd => tsum_zero.symm
      trim_le := OuterMeasure.trim_zero.le }⟩

@[simp]
/-
**MeasureTheory.Measure.zero_toOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：zero_toOuterMeasure {_m : MeasurableSpace α} : (0 : Measure α).toOuterMeas
ure = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_toOuterMeasure {_m : MeasurableSpace α} : (0 : Measure α).toOuterMeasure = 0 :=
  rfl

@[simp, norm_cast]
/-
**MeasureTheory.Measure.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：coe_zero {_m : MeasurableSpace α} : ⇑(0 : Measure α) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero {_m : MeasurableSpace α} : ⇑(0 : Measure α) = 0 :=
  rfl
/-
**MeasureTheory.Measure._root_.MeasureTheory.OuterMeasure.toMeasure_zero** 是 Mat
hlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.MeasureTheory.OuterMeasure.toMeasure_zero
    [ms : MeasurableSpace α] (h : ms ≤ (0 : OuterMeasure α).caratheodory) :
    (0 : OuterMeasure α).toMeasure h = 0 := by
  ext s hs
  simp [hs]
/-
**MeasureTheory.Measure._root_.MeasureTheory.OuterMeasure.toMeasure_eq_zero** 是 
Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma _root_.MeasureTheory.OuterMeasure.toMeasure_eq_zero {ms : MeasurableSpace α}
    {μ : OuterMeasure α} (h : ms ≤ μ.caratheodory) : μ.toMeasure h = 0 ↔ μ = 0 where
  mp hμ := by ext s; exact le_bot_iff.1 <| (le_toMeasure_apply _ _ _).trans_eq congr($hμ s)
  mpr := by rintro rfl; simp

@[nontriviality]
/-
**MeasureTheory.Measure.apply_eq_zero_of_isEmpty** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.Measure`。
形式化陈述：apply_eq_zero_of_isEmpty [IsEmpty α] {_ : MeasurableSpace α} (μ : Measure 
α) (s : Set α) : μ s = 0
参数：μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
lemma apply_eq_zero_of_isEmpty [IsEmpty α] {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) :
    μ s = 0 := by
  rw [eq_empty_of_isEmpty s, measure_empty]
/-
**MeasureTheory.Measure.instSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：instSubsingleton [IsEmpty α] {m : MeasurableSpace α} : Subsingleton (Measu
re α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MeasureTheory.Measure.apply_eq_zero_of_isEmpty`：apply_eq_zero_of_isEmpty
 [IsEmpty α] {_ : MeasurableSpace α} (μ : Measure α) (s : Set α) : μ s = 0
-/
instance instSubsingleton [IsEmpty α] {m : MeasurableSpace α} : Subsingleton (Measure α) :=
  ⟨fun μ ν => by ext1 s _; rw [apply_eq_zero_of_isEmpty, apply_eq_zero_of_isEmpty]⟩
/-
**MeasureTheory.Measure.eq_zero_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：eq_zero_of_isEmpty [IsEmpty α] {_m : MeasurableSpace α} (μ : Measure α) : 
μ = 0
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem eq_zero_of_isEmpty [IsEmpty α] {_m : MeasurableSpace α} (μ : Measure α) : μ = 0 :=
  Subsingleton.elim μ 0

@[simp]
/-
**MeasureTheory.Measure.ofMeasurable_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：ofMeasurable_zero : ofMeasurable (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.inducedOuterMeasure_zero`：inducedOuterMeasure_zero (Pu : P
 univ) : inducedOuterMeasure (fun _ _ => 0) P0 (by simp) = 0
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.mk.congr_simp`：∀ {α : Type u_6} [inst : Measurable
Space α] (toOuterMeasure toOuterMeasure_1 : MeasureTheory.OuterMeasure α)   (e_t
oOuterMeasure : toOuterMe…
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.OuterMeasure.instIsZeroApplySetENNReal`：∀ {α : Type u_1}, 
IsZeroApply (MeasureTheory.OuterMeasure α) (Set α) ENNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofMeasurable_zero : ofMeasurable (α := α) (fun _ _ => 0) rfl (by simp) = 0 := by
  ext s
  simp [ofMeasurable, ← toOuterMeasure_apply, inducedOuterMeasure_zero MeasurableSet.iUnion]
/-
**MeasureTheory.Measure.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：instInhabited {_ : MeasurableSpace α} : Inhabited (Measure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited {_ : MeasurableSpace α} : Inhabited (Measure α) :=
  ⟨0⟩
/-
**MeasureTheory.Measure.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：instAdd {_ : MeasurableSpace α} : Add (Measure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd {_ : MeasurableSpace α} : Add (Measure α) :=
  ⟨fun μ₁ μ₂ =>
    { toOuterMeasure := μ₁.toOuterMeasure + μ₂.toOuterMeasure
      m_iUnion := fun s hs hd =>
        show μ₁ (⋃ i, s i) + μ₂ (⋃ i, s i) = ∑' i, (μ₁ (s i) + μ₂ (s i)) by
          rw [ENNReal.tsum_add, measure_iUnion hd hs, measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_add, μ₁.trimmed, μ₂.trimmed] }⟩

@[simp]
/-
**MeasureTheory.Measure.add_toOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：add_toOuterMeasure {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) : (μ₁ + μ₂
).toOuterMeasure = μ₁.toOuterMeasure + μ₂.toOuterMeasure
参数：μ₁ μ₂ : Measure α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_toOuterMeasure {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) :
    (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure + μ₂.toOuterMeasure :=
  rfl

@[simp, norm_cast]
/-
**MeasureTheory.Measure.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：coe_add {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ
₂
参数：μ₁ μ₂ : Measure α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂ :=
  rfl
/-
**MeasureTheory.Measure.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：add_apply {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) : (μ₁ +
 μ₂) s = μ₁ s + μ₂ s
参数：μ₁ μ₂ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply {_m : MeasurableSpace α} (μ₁ μ₂ : Measure α) (s : Set α) :
    (μ₁ + μ₂) s = μ₁ s + μ₂ s :=
  rfl

section SMul

variable [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
variable [SMul R' ℝ≥0∞] [IsScalarTower R' ℝ≥0∞ ℝ≥0∞]

/-
**MeasureTheory.Measure.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：instSMul {_ : MeasurableSpace α} : SMul R (Measure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul {_ : MeasurableSpace α} : SMul R (Measure α) :=
  ⟨fun c μ =>
    { toOuterMeasure := c • μ.toOuterMeasure
      m_iUnion := fun s hs hd => by
        simp only [smul_apply, coe_toOuterMeasure, ENNReal.tsum_const_smul,
          measure_iUnion hd hs]
      trim_le := by rw [OuterMeasure.trim_smul, μ.trimmed] }⟩

@[simp]
/-
**MeasureTheory.Measure.smul_toOuterMeasure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：smul_toOuterMeasure {_m : MeasurableSpace α} (c : R) (μ : Measure α) : (c 
• μ).toOuterMeasure = c • μ.toOuterMeasure
参数：c : R；μ : Measure α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_toOuterMeasure {_m : MeasurableSpace α} (c : R) (μ : Measure α) :
    (c • μ).toOuterMeasure = c • μ.toOuterMeasure :=
  rfl

@[simp, norm_cast]
/-
**MeasureTheory.Measure.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：coe_smul {_m : MeasurableSpace α} (c : R) (μ : Measure α) : ⇑(c • μ) = c •
 ⇑μ
参数：c : R；μ : Measure α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul {_m : MeasurableSpace α} (c : R) (μ : Measure α) : ⇑(c • μ) = c • ⇑μ :=
  rfl

@[simp]
/-
**MeasureTheory.Measure.coe_nnreal_smul** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：coe_nnreal_smul (c : Real>=0) (μ : Measure α) : (c : Real>=0∞) • μ = c • μ
参数：c : Real>=0；μ : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma coe_nnreal_smul (c : ℝ≥0) (μ : Measure α) : (c : ℝ≥0∞) • μ = c • μ := rfl

@[simp]
/-
**MeasureTheory.Measure.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：smul_apply {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) : 
(c • μ) s = c • μ s
参数：c : R；μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply {_m : MeasurableSpace α} (c : R) (μ : Measure α) (s : Set α) :
    (c • μ) s = c • μ s :=
  rfl
/-
**MeasureTheory.Measure.instSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：instSMulCommClass [SMulCommClass R R' Real>=0∞] {_ : MeasurableSpace α} : 
SMulCommClass R R' (Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance instSMulCommClass [SMulCommClass R R' ℝ≥0∞] {_ : MeasurableSpace α} :
    SMulCommClass R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_comm _ _ _⟩
/-
**MeasureTheory.Measure.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：instIsScalarTower [SMul R R'] [IsScalarTower R R' Real>=0∞] {_ : Measurabl
eSpace α} : IsScalarTower R R' (Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance instIsScalarTower [SMul R R'] [IsScalarTower R R' ℝ≥0∞] {_ : MeasurableSpace α} :
    IsScalarTower R R' (Measure α) :=
  ⟨fun _ _ _ => ext fun _ _ => smul_assoc _ _ _⟩
/-
**MeasureTheory.Measure.instIsCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：instIsCentralScalar [SMul Rᵐᵒᵖ Real>=0∞] [IsCentralScalar R Real>=0∞] {_ :
 MeasurableSpace α} : IsCentralScalar R (Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.op_left`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [i
nst : SMul M α] [inst_1 : SMul Mᵐᵒᵖ α] [IsCentralScalar M α]   [inst_3 : SMul M 
N] [inst_4 …
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance instIsCentralScalar [SMul Rᵐᵒᵖ ℝ≥0∞] [IsCentralScalar R ℝ≥0∞] {_ : MeasurableSpace α} :
    IsCentralScalar R (Measure α) :=
  ⟨fun _ _ => ext fun _ _ => op_smul_eq_smul _ _⟩

end SMul

/-
**MeasureTheory.Measure.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：instMulAction [Monoid R] [MulAction R Real>=0∞] [IsScalarTower R Real>=0∞ 
Real>=0∞] {_ : MeasurableSpace α} : MulAction R (Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.toOuterMeasure_injective`：∀ {α : Type u_1} [inst :
 MeasurableSpace α], Function.Injective MeasureTheory.Measure.toOuterMeasure
-/
instance instMulAction [Monoid R] [MulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {_ : MeasurableSpace α} : MulAction R (Measure α) :=
  Injective.mulAction _ toOuterMeasure_injective smul_toOuterMeasure
/-
**MeasureTheory.Measure.instAddCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：instAddCommMonoid {_ : MeasurableSpace α} : AddCommMonoid (Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.toOuterMeasure_injective`：∀ {α : Type u_1} [inst :
 MeasurableSpace α], Function.Injective MeasureTheory.Measure.toOuterMeasure
· 使用定理 `MeasureTheory.Measure.zero_toOuterMeasure`：zero_toOuterMeasure {_m : Mea
surableSpace α} : (0 : Measure α).toOuterMeasure = 0
· 使用定理 `MeasureTheory.Measure.add_toOuterMeasure`：add_toOuterMeasure {_m : Measu
rableSpace α} (μ₁ μ₂ : Measure α) : (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure
 + μ₂.toOuterMeasure
-/
instance instAddCommMonoid {_ : MeasurableSpace α} : AddCommMonoid (Measure α) :=
  toOuterMeasure_injective.addCommMonoid toOuterMeasure zero_toOuterMeasure add_toOuterMeasure
    fun _ _ => smul_toOuterMeasure _ _

/-- Coercion to function as an additive monoid homomorphism. -/
/-
**MeasureTheory.Measure.coeAddHom** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：coeAddHom {_ : MeasurableSpace α} : Measure α ->+ Set α -> Real>=0∞ where 
toFun
该定义给出了一等式。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.coe_zero`：coe_zero {_m : MeasurableSpace α} : ⇑(0 
: Measure α) = 0
· 使用定理 `MeasureTheory.Measure.coe_add`：coe_add {_m : MeasurableSpace α} (μ₁ μ₂ :
 Measure α) : ⇑(μ₁ + μ₂) = μ₁ + μ₂

--- 原说明 ---
Coercion to function as an additive monoid homomorphism.
-/
def coeAddHom {_ : MeasurableSpace α} : Measure α →+ Set α → ℝ≥0∞ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
/-
**MeasureTheory.Measure.coeAddHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：coeAddHom_apply {_ : MeasurableSpace α} (μ : Measure α) : coeAddHom μ = ⇑μ
参数：μ : Measure α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeAddHom_apply {_ : MeasurableSpace α} (μ : Measure α) : coeAddHom μ = ⇑μ := rfl

@[simp]
/-
**MeasureTheory.Measure.coe_finsetSum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.M
easure`。
形式化陈述：coe_finsetSum {_m : MeasurableSpace α} (I : Finset ι) (μ : ι -> Measure α)
 : ⇑(∑ i in I, μ i) = ∑ i in I, ⇑(μ i)
参数：I : Finset ι；μ : ι -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem coe_finsetSum {_m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) :
    ⇑(∑ i ∈ I, μ i) = ∑ i ∈ I, ⇑(μ i) := map_sum coeAddHom μ I

@[deprecated (since := "2026-04-08")] alias coe_finset_sum := coe_finsetSum
/-
**MeasureTheory.Measure.finsetSum_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：finsetSum_apply {m : MeasurableSpace α} (I : Finset ι) (μ : ι -> Measure α
) (s : Set α) : (∑ i in I, μ i) s = ∑ i in I, μ i s
参数：I : Finset ι；μ : ι -> Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.coe_finsetSum`：coe_finsetSum {_m : MeasurableSpace
 α} (I : Finset ι) (μ : ι -> Measure α) : ⇑(∑ i in I, μ i) = ∑ i in I, ⇑(μ i)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
-/
theorem finsetSum_apply {m : MeasurableSpace α} (I : Finset ι) (μ : ι → Measure α) (s : Set α) :
    (∑ i ∈ I, μ i) s = ∑ i ∈ I, μ i s := by rw [coe_finsetSum, Finset.sum_apply]

@[deprecated (since := "2026-04-08")] alias finset_sum_apply := finsetSum_apply
/-
**MeasureTheory.Measure.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：instDistribMulAction [Monoid R] [DistribMulAction R Real>=0∞] [IsScalarTow
er R Real>=0∞ Real>=0∞] {_ : MeasurableSpace α} : DistribMulAction R (Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.zero_toOuterMeasure`：zero_toOuterMeasure {_m : Mea
surableSpace α} : (0 : Measure α).toOuterMeasure = 0
· 使用定理 `MeasureTheory.Measure.add_toOuterMeasure`：add_toOuterMeasure {_m : Measu
rableSpace α} (μ₁ μ₂ : Measure α) : (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure
 + μ₂.toOuterMeasure
· 使用定理 `MeasureTheory.Measure.toOuterMeasure_injective`：∀ {α : Type u_1} [inst :
 MeasurableSpace α], Function.Injective MeasureTheory.Measure.toOuterMeasure
-/
instance instDistribMulAction [Monoid R] [DistribMulAction R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {_ : MeasurableSpace α} : DistribMulAction R (Measure α) :=
  Injective.distribMulAction ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure
/-
**MeasureTheory.Measure.instModule** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：instModule [Semiring R] [Module R Real>=0∞] [IsScalarTower R Real>=0∞ Real
>=0∞] {_ : MeasurableSpace α} : Module R (Measure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.zero_toOuterMeasure`：zero_toOuterMeasure {_m : Mea
surableSpace α} : (0 : Measure α).toOuterMeasure = 0
· 使用定理 `MeasureTheory.Measure.add_toOuterMeasure`：add_toOuterMeasure {_m : Measu
rableSpace α} (μ₁ μ₂ : Measure α) : (μ₁ + μ₂).toOuterMeasure = μ₁.toOuterMeasure
 + μ₂.toOuterMeasure
· 使用定理 `MeasureTheory.Measure.toOuterMeasure_injective`：∀ {α : Type u_1} [inst :
 MeasurableSpace α], Function.Injective MeasureTheory.Measure.toOuterMeasure
-/
instance instModule [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    {_ : MeasurableSpace α} : Module R (Measure α) :=
  Injective.module R ⟨⟨toOuterMeasure, zero_toOuterMeasure⟩, add_toOuterMeasure⟩
    toOuterMeasure_injective smul_toOuterMeasure
/-
**MeasureTheory.Measure.instModuleIsTorsionFree** 是 Mathlib 中的一个实例，位于命名空间 `Measu
reTheory.Measure`。
形式化陈述：instModuleIsTorsionFree [Semiring R] [Module R Real>=0∞] [IsScalarTower R 
Real>=0∞ Real>=0∞] [Module.IsTorsionFree R Real>=0∞] : Module.IsTorsionFree R (M
easure α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Injective.moduleIsTorsionFree`：Function.Injective.moduleIsTorsi
onFree [IsTorsionFree R N] (f : M -> N) (hf : f.Injective) (smul : forall (r : R
) (m : M), f (r • m) = r • f…
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
instance instModuleIsTorsionFree [Semiring R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    [Module.IsTorsionFree R ℝ≥0∞] : Module.IsTorsionFree R (Measure α) :=
  DFunLike.coe_injective.moduleIsTorsionFree _ (by simp)
/-
**MeasureTheory.Measure.ennreal_smul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {c : ENNReal} {μ : MeasureTheory
.Measure α}, c • μ = 0 ↔ c = 0 ∨ μ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma ennreal_smul_eq_zero {c : ℝ≥0∞} {μ : Measure α} : c • μ = 0 ↔ c = 0 ∨ μ = 0 := by
  simp [Measure.ext_iff', forall_or_left]

@[simp]
/-
**MeasureTheory.Measure.coe_nnreal_smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：coe_nnreal_smul_apply {_m : MeasurableSpace α} (c : Real>=0) (μ : Measure 
α) (s : Set α) : (c • μ) s = c * μ s
参数：c : Real>=0；μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem coe_nnreal_smul_apply {_m : MeasurableSpace α} (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    (c • μ) s = c * μ s :=
  rfl

@[simp]
/-
**MeasureTheory.Measure.nnreal_smul_coe_apply** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.Measure`。
形式化陈述：nnreal_smul_coe_apply {_m : MeasurableSpace α} (c : Real>=0) (μ : Measure 
α) (s : Set α) : c • μ s = c * μ s
参数：c : Real>=0；μ : Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nnreal_smul_coe_apply {_m : MeasurableSpace α} (c : ℝ≥0) (μ : Measure α) (s : Set α) :
    c • μ s = c * μ s :=
  rfl
/-
**MeasureTheory.Measure.ae_smul_measure** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：ae_smul_measure {p : α -> Prop} [SMul R Real>=0∞] [IsScalarTower R Real>=0
∞ Real>=0∞] (h : forallᵐ x ∂μ, p x) (c : R) : forallᵐ x ∂c • μ, p x
参数：h : forallᵐ x ∂μ, p x；c : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.smul_apply`：smul_apply {_m : MeasurableSpace α} (c
 : R) (μ : Measure α) (s : Set α) : (c • μ) s = c • μ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem ae_smul_measure {p : α → Prop} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
    (h : ∀ᵐ x ∂μ, p x) (c : R) : ∀ᵐ x ∂c • μ, p x :=
  ae_iff.2 <| by rw [smul_apply, ae_iff.1 h, ← smul_one_smul ℝ≥0∞, smul_zero]
/-
**MeasureTheory.Measure.ae_smul_measure_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：ae_smul_measure_le [SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (
c : R) : ae (c • μ) <= ae μ
参数：c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.ae_smul_measure`：ae_smul_measure {p : α -> Prop} [
SMul R Real>=0∞] [IsScalarTower R Real>=0∞ Real>=0∞] (h : forallᵐ x ∂μ, p x) (c 
: R) : forallᵐ x ∂c • μ, p …
-/
theorem ae_smul_measure_le [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R) :
    ae (c • μ) ≤ ae μ := fun _ h ↦ ae_smul_measure h c

section Module

variable {R : Type*} [Semiring R] [IsDomain R] [Module R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  [Module.IsTorsionFree R ℝ≥0∞] {c : R} {p : α → Prop}

/-
**MeasureTheory.Measure.ae_smul_measure_iff** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：ae_smul_measure_iff (hc : c != 0) {μ : Measure α} : (forallᵐ x ∂c • μ, p x
) ↔ forallᵐ x ∂μ, p x
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ae_smul_measure_iff (hc : c ≠ 0) {μ : Measure α} : (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by
  simp [ae_iff, hc]
/-
**MeasureTheory.Measure.ae_smul_measure_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {R : Type u_8} [inst : Semiring 
R] [IsDomain R]   [inst_2 : _root_.Module R ENNReal] [inst_3 : IsScalarTower R E
NNReal ENNReal] [Module.IsTorsionFree R ENNReal]   {c : R}, c ≠ 0 → ∀ (μ : Measu
reTheory.Measure α), MeasureTheory.ae (c • μ) = MeasureTheory.ae μ
参数：μ : MeasureTheory.Measure α；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.Measure.ae_smul_measure_iff`：ae_smul_measure_iff (hc : c !
= 0) {μ : Measure α} : (forallᵐ x ∂c • μ, p x) ↔ forallᵐ x ∂μ, p x
-/
@[simp] lemma ae_smul_measure_eq (hc : c ≠ 0) (μ : Measure α) : ae (c • μ) = ae μ := by
  ext; exact ae_smul_measure_iff hc

end Module

/-
**MeasureTheory.Measure.ae_ennreal_smul_measure_iff** 是 Mathlib 中的一个引理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：ae_ennreal_smul_measure_iff {c : Real>=0∞} {p : α -> Prop} (hc : c != 0) {
μ : Measure α} : (forallᵐ x ∂c • μ, p x) ↔ forallᵐ x ∂μ, p x
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.instNoZeroDivisors`：NoZeroDivisors ENNReal
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ae_ennreal_smul_measure_iff {c : ℝ≥0∞} {p : α → Prop} (hc : c ≠ 0) {μ : Measure α} :
    (∀ᵐ x ∂c • μ, p x) ↔ ∀ᵐ x ∂μ, p x := by simp [ae_iff, hc]
/-
**MeasureTheory.Measure.ae_ennreal_smul_measure_eq** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {c : ENNReal},   c ≠ 0 → ∀ (μ : 
MeasureTheory.Measure α), MeasureTheory.ae (c • μ) = MeasureTheory.ae μ
参数：μ : MeasureTheory.Measure α；c • μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `MeasureTheory.Measure.ae_ennreal_smul_measure_iff`：ae_ennreal_smul_measu
re_iff {c : Real>=0∞} {p : α -> Prop} (hc : c != 0) {μ : Measure α} : (forallᵐ x
 ∂c • μ, p x) ↔ forallᵐ x ∂μ, p x
-/
@[simp] lemma ae_ennreal_smul_measure_eq {c : ℝ≥0∞} (hc : c ≠ 0) (μ : Measure α) :
    ae (c • μ) = ae μ := by ext; exact ae_ennreal_smul_measure_iff hc
/-
**MeasureTheory.Measure.measure_eq_left_of_subset_of_measure_add_eq** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_eq_left_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t !
= ∞) (h' : s subseteq t) (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t
参数：h : (μ + ν) t != ∞；h' : s subseteq t；h'' : (μ + ν) s = (μ + ν) t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `ENNReal.le_of_add_le_add_right`：∀ {a b c : ENNReal}, a ≠ ⊤ → b + a ≤ c +
 a → b ≤ c
· 使用定理 `ne_top_of_le_ne_top`：ne_top_of_le_ne_top (hb : b != ⊤) (hab : a <= b) : 
a != ⊤
· 使用定理 `le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canoni
callyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem measure_eq_left_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t := by
  refine le_antisymm (measure_mono h') ?_
  have : μ t + ν t ≤ μ s + ν t :=
    calc
      μ t + ν t = μ s + ν s := h''.symm
      _ ≤ μ s + ν t := by gcongr
  apply ENNReal.le_of_add_le_add_right _ this
  exact ne_top_of_le_ne_top h (le_add_left le_rfl)
/-
**MeasureTheory.Measure.measure_eq_right_of_subset_of_measure_add_eq** 是 Mathlib
 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_eq_right_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t 
!= ∞) (h' : s subseteq t) (h'' : (μ + ν) s = (μ + ν) t) : ν s = ν t
参数：h : (μ + ν) t != ∞；h' : s subseteq t；h'' : (μ + ν) s = (μ + ν) t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.measure_eq_left_of_subset_of_measure_add_eq`：measu
re_eq_left_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t != ∞) (h' : 
s subseteq t) (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem measure_eq_right_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t ≠ ∞) (h' : s ⊆ t)
    (h'' : (μ + ν) s = (μ + ν) t) : ν s = ν t := by
  rw [add_comm] at h'' h
  exact measure_eq_left_of_subset_of_measure_add_eq h h' h''
/-
**MeasureTheory.Measure.measure_toMeasurable_add_inter_left** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_toMeasurable_add_inter_left {s t : Set α} (hs : MeasurableSet s) (
ht : (μ + ν) t != ∞) : μ (toMeasurable (μ + ν) t inter s) = μ (t inter s)
参数：hs : MeasurableSet s；ht : (μ + ν) t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_inter_eq_of_measure_eq`：measure_inter_eq_o
f_measure_eq {s t u : Set α} (hs : MeasurableSet s) (h : μ t = μ u) (htu : t sub
seteq u) (ht_ne_top : μ t != ∞) : μ (t int…
· 使用定理 `MeasureTheory.Measure.measure_eq_left_of_subset_of_measure_add_eq`：measu
re_eq_left_of_subset_of_measure_add_eq {s t : Set α} (h : (μ + ν) t != ∞) (h' : 
s subseteq t) (h'' : (μ + ν) s = (μ + ν) t) : μ s = μ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem measure_toMeasurable_add_inter_left {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : μ (toMeasurable (μ + ν) t ∩ s) = μ (t ∩ s) := by
  refine (measure_inter_eq_of_measure_eq hs ?_ (subset_toMeasurable _ _) ?_).symm
  · refine
      measure_eq_left_of_subset_of_measure_add_eq ?_ (subset_toMeasurable _ _)
        (measure_toMeasurable t).symm
    rwa [measure_toMeasurable t]
  · simp only [not_or, ENNReal.add_eq_top, Pi.add_apply, Ne, coe_add] at ht
    exact ht.1
/-
**MeasureTheory.Measure.measure_toMeasurable_add_inter_right** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.Measure`。
形式化陈述：measure_toMeasurable_add_inter_right {s t : Set α} (hs : MeasurableSet s) 
(ht : (μ + ν) t != ∞) : ν (toMeasurable (μ + ν) t inter s) = ν (t inter s)
参数：hs : MeasurableSet s；ht : (μ + ν) t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.Measure.measure_toMeasurable_add_inter_left`：measure_toMea
surable_add_inter_left {s t : Set α} (hs : MeasurableSet s) (ht : (μ + ν) t != ∞
) : μ (toMeasurable (μ + ν) t inter s) = μ (t i…
-/
theorem measure_toMeasurable_add_inter_right {s t : Set α} (hs : MeasurableSet s)
    (ht : (μ + ν) t ≠ ∞) : ν (toMeasurable (μ + ν) t ∩ s) = ν (t ∩ s) := by
  rw [add_comm] at ht ⊢
  exact measure_toMeasurable_add_inter_left hs ht

/-! ### The complete lattice of measures -/


/-- Measures are partially ordered. -/
/-
**MeasureTheory.Measure.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：instPartialOrder {_ : MeasurableSpace α} : PartialOrder (Measure α) where 
le m₁ m₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Measures are partially ordered.
-/
instance instPartialOrder {_ : MeasurableSpace α} : PartialOrder (Measure α) where
  le m₁ m₂ := ∀ s, m₁ s ≤ m₂ s
  le_refl _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ s := le_trans (h₁ s) (h₂ s)
  le_antisymm _ _ h₁ h₂ := ext fun s _ => le_antisymm (h₁ s) (h₂ s)
/-
**MeasureTheory.Measure.toOuterMeasure_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：toOuterMeasure_le : μ₁.toOuterMeasure <= μ₂.toOuterMeasure ↔ μ₁ <= μ₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toOuterMeasure_le : μ₁.toOuterMeasure ≤ μ₂.toOuterMeasure ↔ μ₁ ≤ μ₂ := .rfl
/-
**MeasureTheory.Measure.le_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`
。
形式化陈述：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSet s -> μ₁ s <= μ₂ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.outerMeasure_le_iff`：outerMeasure_le_iff {m : Oute
rMeasure α} : m <= μ.1 ↔ forall s, MeasurableSet s -> m s <= μ s
-/
theorem le_iff : μ₁ ≤ μ₂ ↔ ∀ s, MeasurableSet s → μ₁ s ≤ μ₂ s := outerMeasure_le_iff
/-
**MeasureTheory.Measure.le_intro** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：le_intro (h : forall s, MeasurableSet s -> s.Nonempty -> μ₁ s <= μ₂ s) : μ
₁ <= μ₂
参数：h : forall s, MeasurableSet s -> s.Nonempty -> μ₁ s <= μ₂ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_intro (h : ∀ s, MeasurableSet s → s.Nonempty → μ₁ s ≤ μ₂ s) : μ₁ ≤ μ₂ :=
  le_iff.2 fun s hs ↦ s.eq_empty_or_nonempty.elim (by rintro rfl; simp) (h s hs)
/-
**MeasureTheory.Measure.le_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：le_iff' : μ₁ <= μ₂ ↔ forall s, μ₁ s <= μ₂ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_iff' : μ₁ ≤ μ₂ ↔ ∀ s, μ₁ s ≤ μ₂ s := .rfl
/-
**MeasureTheory.Measure.measure_mono_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν : MeasureTheory.Measure α},
 μ ≤ ν → ∀ (s : Set α), μ s ≤ ν s
参数：s : Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] theorem measure_mono_left (h : μ ≤ ν) (s : Set α) : μ s ≤ ν s := h s

@[gcongr]
/-
**MeasureTheory.Measure.measure_mono_both** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：measure_mono_both (h₁ : μ <= ν) (h₂ : s subseteq t) : μ s <= ν t
参数：h₁ : μ <= ν；h₂ : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem measure_mono_both (h₁ : μ ≤ ν) (h₂ : s ⊆ t) : μ s ≤ ν t :=
  (h₁ s).trans (measure_mono h₂)
/-
**MeasureTheory.Measure.lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`
。
形式化陈述：lt_iff : μ < ν ↔ μ <= ν ∧ exists s, MeasurableSet s ∧ μ s < ν s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_iff : μ < ν ↔ μ ≤ ν ∧ ∃ s, MeasurableSet s ∧ μ s < ν s :=
  lt_iff_le_not_ge.trans <|
    and_congr Iff.rfl <| by simp only [le_iff, not_forall, not_le, exists_prop]
/-
**MeasureTheory.Measure.lt_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：lt_iff' : μ < ν ↔ μ <= ν ∧ exists s, μ s < ν s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lt_iff' : μ < ν ↔ μ ≤ ν ∧ ∃ s, μ s < ν s :=
  lt_iff_le_not_ge.trans <| and_congr Iff.rfl <| by simp only [le_iff', not_forall, not_le]
/-
**MeasureTheory.Measure.instIsOrderedAddMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：instIsOrderedAddMonoid {_ : MeasurableSpace α} : IsOrderedAddMonoid (Measu
re α) where add_le_add_left _ _ h _ s
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
-/
instance instIsOrderedAddMonoid {_ : MeasurableSpace α} : IsOrderedAddMonoid (Measure α) where
  add_le_add_left _ _ h _ s := add_le_add_left (h s) _
/-
**MeasureTheory.Measure.le_add_left** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν ν' : MeasureTheory.Measure 
α}, μ ≤ ν → μ ≤ ν' + ν
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canoni
callyOrderedAdd α] {a b c : α}, a ≤ c → a ≤ b + c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
protected theorem le_add_left (h : μ ≤ ν) : μ ≤ ν' + ν := fun s => le_add_left (h s)
/-
**MeasureTheory.Measure.le_add_right** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ ν ν' : MeasureTheory.Measure 
α}, μ ≤ ν → μ ≤ ν + ν'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : Preorder α] [Canon
icallyOrderedAdd α] {a b c : α}, a ≤ b → a ≤ b + c
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
-/
protected theorem le_add_right (h : μ ≤ ν) : μ ≤ ν + ν' := fun s => le_add_right (h s)
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [CovariantClass R ℝ≥0∞ (· • ·) (· ≤ ·)] :
    CovariantClass R (Measure α) (· • ·) (· ≤ ·) where
  elim c μ ν hμν s := by
    simp only [smul_apply]
    gcongr
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul R ℝ≥0∞] [LE R] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] [IsOrderedSMul R ℝ≥0∞] :
    IsOrderedSMul R (Measure α) where
  smul_le_smul_left μ ν hμν a s := by gcongr
  smul_le_smul_right a b hab μ s := by
    simp only [smul_apply]
    gcongr

section sInf

variable {m : Set (Measure α)}

/-
**MeasureTheory.Measure.sInf_caratheodory** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：sInf_caratheodory (s : Set α) (hs : MeasurableSet s) : MeasurableSet[(sInf
 (toOuterMeasure '' m)).caratheodory] s
参数：s : Set α；hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.OuterMeasure.sInf_eq_boundedBy_sInfGen`：sInf_eq_boundedBy_
sInfGen (m : Set (OuterMeasure α)) : sInf m = OuterMeasure.boundedBy (sInfGen m)
· 使用定理 `MeasureTheory.OuterMeasure.boundedBy_caratheodory`：boundedBy_caratheodor
y {m : Set α -> Real>=0∞} {s : Set α} (hs : forall t, m (t inter s) + m (t \ s) 
<= m t) : MeasurableSet[(boundedBy m).c…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `MeasureTheory.measure_eq_iInf`：measure_eq_iInf (s : Set α) : μ s = ⨅ (t)
 (_ : s subseteq t) (_ : MeasurableSet t), μ t
· 使用定理 `MeasureTheory.OuterMeasure.sInfGen_def`：sInfGen_def (m : Set (OuterMeasu
re α)) (t : Set α) : sInfGen m t = ⨅ (μ : OuterMeasure α) (_ : μ in m), μ t
· 使用定理 `iInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
γ : Type u_8} {f : β → γ} {g : γ → α} {t : Set β},   ⨅ c ∈ f '' t, g c = ⨅ b ∈ t
…
· 使用定理 `iInf₂_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst
 : CompleteLattice α] {a : α} {f : (i : ι) → κ i → α} (i : ι)   (j : κ i), f i j
 ≤ a…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.OuterMeasure.instOuterMeasureClass`：∀ {α : Type u_1}, Meas
ureTheory.OuterMeasureClass (MeasureTheory.OuterMeasure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_inter_add_sdiff`：measure_inter_add_sdiff (s : Set 
α) (ht : MeasurableSet t) : μ (s inter t) + μ (s \ t) = μ s
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.sdiff_subset_sdiff_left`：sdiff_subset_sdiff_left {s₁ s₂ t : Set α} (
h : s₁ subseteq s₂) : s₁ \ t subseteq s₂ \ t
-/
theorem sInf_caratheodory (s : Set α) (hs : MeasurableSet s) :
    MeasurableSet[(sInf (toOuterMeasure '' m)).caratheodory] s := by
  rw [OuterMeasure.sInf_eq_boundedBy_sInfGen]
  refine OuterMeasure.boundedBy_caratheodory fun t => ?_
  simp only [OuterMeasure.sInfGen, le_iInf_iff, forall_mem_image, measure_eq_iInf t,
    coe_toOuterMeasure]
  intro μ hμ u htu _hu
  have hm : ∀ {s t}, s ⊆ t → OuterMeasure.sInfGen (toOuterMeasure '' m) s ≤ μ t := by
    intro s t hst
    rw [OuterMeasure.sInfGen_def, iInf_image]
    exact iInf₂_le_of_le μ hμ <| measure_mono hst
  rw [← measure_inter_add_sdiff u hs]
  exact add_le_add (hm <| inter_subset_inter_left _ htu) (hm <| sdiff_subset_sdiff_left htu)
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {_ : MeasurableSpace α} : InfSet (Measure α) :=
  ⟨fun m => (sInf (toOuterMeasure '' m)).toMeasure <| sInf_caratheodory⟩
/-
**MeasureTheory.Measure.sInf_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：sInf_apply (hs : MeasurableSet s) : sInf m s = sInf (toOuterMeasure '' m) 
s
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.toMeasure_apply`：toMeasure_apply (m : OuterMeasure α) (h :
 ms <= m.caratheodory) {s : Set α} (hs : MeasurableSet s) : m.toMeasure h s = m 
s
· 使用定理 `MeasureTheory.Measure.sInf_caratheodory`：sInf_caratheodory (s : Set α) (
hs : MeasurableSet s) : MeasurableSet[(sInf (toOuterMeasure '' m)).caratheodory]
 s
-/
theorem sInf_apply (hs : MeasurableSet s) : sInf m s = sInf (toOuterMeasure '' m) s :=
  toMeasure_apply _ _ hs
/-
**MeasureTheory.Measure.measure_sInf_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem measure_sInf_le (h : μ ∈ m) : sInf m ≤ μ :=
  have : sInf (toOuterMeasure '' m) ≤ μ.toOuterMeasure := sInf_le (mem_image_of_mem _ h)
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s
/-
**MeasureTheory.Measure.measure_le_sInf** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem measure_le_sInf (h : ∀ μ' ∈ m, μ ≤ μ') : μ ≤ sInf m :=
  have : μ.toOuterMeasure ≤ sInf (toOuterMeasure '' m) :=
    le_sInf <| forall_mem_image.2 fun _ hμ ↦ toOuterMeasure_le.2 <| h _ hμ
  le_iff.2 fun s hs => by rw [sInf_apply hs]; exact this s
/-
**MeasureTheory.Measure.instCompleteSemilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Me
asureTheory.Measure`。
形式化陈述：instCompleteSemilatticeInf {_ : MeasurableSpace α} : CompleteSemilatticeIn
f (Measure α) where isGLB_sInf _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompleteSemilatticeInf {_ : MeasurableSpace α} :
    CompleteSemilatticeInf (Measure α) where
  isGLB_sInf _ := private ⟨fun _ ↦ measure_sInf_le, fun _ ↦ measure_le_sInf⟩
/-
**MeasureTheory.Measure.instCompleteLattice** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：instCompleteLattice {_ : MeasurableSpace α} : CompleteLattice (Measure α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCompleteLattice {_ : MeasurableSpace α} : CompleteLattice (Measure α) :=
  { completeLatticeOfCompleteSemilatticeInf (Measure α) with
    top :=
      { toOuterMeasure := ⊤,
        m_iUnion := by
          intro f _ _
          refine (measure_iUnion_le _).antisymm ?_
          if hne : (⋃ i, f i).Nonempty then
            rw [OuterMeasure.top_apply hne]
            exact le_top
          else
            simp_all [Set.not_nonempty_iff_eq_empty]
        trim_le := le_top },
    le_top := fun _ => toOuterMeasure_le.mp le_top
    bot := 0
    bot_le := fun _a _s => bot_le }

end sInf

/-
**MeasureTheory.Measure.inf_apply** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：inf_apply {s : Set α} (hs : MeasurableSet s) : (μ ⊓ ν) s = sInf {m | exist
s t, m = μ (t inter s) + ν (tᶜ inter s)}
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_pair`：∀ {α : Type u_1} [inst : CompleteLattice α] {a b : α}, sInf {
a, b} = a ⊓ b
· 使用定理 `MeasureTheory.Measure.sInf_apply`：sInf_apply (hs : MeasurableSet s) : sI
nf m s = sInf (toOuterMeasure '' m) s
· 使用定理 `MeasureTheory.OuterMeasure.sInf_apply`：sInf_apply {m : Set (OuterMeasure
 α)} {s : Set α} (h : m.Nonempty) : sInf m s = ⨅ (t : Nat -> Set α) (_ : s subse
teq iUnion t), ∑' n, ⨅ (μ :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Set.insert_nonempty`：insert_nonempty (a : α) (s : Set α) : (insert a s).
Nonempty
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
γ : Type u_8} {f : β → γ} {g : γ → α} {t : Set β},   ⨅ c ∈ f '' t, g c = ⨅ b ∈ t
…
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iInf_pair`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {f
 : β → α} {a b : β}, ⨅ x ∈ {a, b}, f x = f a ⊓ f b
（共 79 条，此处仅展示前 30 条）
-/
lemma inf_apply {s : Set α} (hs : MeasurableSet s) :
    (μ ⊓ ν) s = sInf {m | ∃ t, m = μ (t ∩ s) + ν (tᶜ ∩ s)} := by
  -- `(μ ⊓ ν) s` is defined as `⊓ (t : ℕ → Set α) (ht : s ⊆ ⋃ n, t n), ∑' n, μ (t n) ⊓ ν (t n)`
  rw [← sInf_pair, Measure.sInf_apply hs, OuterMeasure.sInf_apply
    (image_nonempty.2 <| insert_nonempty μ {ν})]
  refine le_antisymm (le_sInf fun m ⟨t, ht₁⟩ ↦ ?_) (le_iInf₂ fun t' ht' ↦ ?_)
  · subst ht₁
    -- We first show `(μ ⊓ ν) s ≤ μ (t ∩ s) + ν (tᶜ ∩ s)` for any `t : Set α`
    -- For this, define the sequence `t' : ℕ → Set α` where `t' 0 = t ∩ s`, `t' 1 = tᶜ ∩ s` and
    -- `∅` otherwise. Then, we have by construction
    -- `(μ ⊓ ν) s ≤ ∑' n, μ (t' n) ⊓ ν (t' n) ≤ μ (t' 0) + ν (t' 1) = μ (t ∩ s) + ν (tᶜ ∩ s)`.
    set t' : ℕ → Set α := fun n ↦ if n = 0 then t ∩ s else if n = 1 then tᶜ ∩ s else ∅ with ht'
    refine (iInf₂_le t' fun x hx ↦ ?_).trans ?_
    · by_cases hxt : x ∈ t
      · refine mem_iUnion.2 ⟨0, ?_⟩
        simp [hx, hxt]
      · refine mem_iUnion.2 ⟨1, ?_⟩
        simp [hx, hxt]
    · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
      rw [tsum_eq_add_tsum_ite 0, tsum_eq_add_tsum_ite 1, if_neg zero_ne_one.symm,
        ENNReal.summable.tsum_eq_zero_iff.2 _, add_zero]
      · exact add_le_add (inf_le_left.trans <| by simp [ht']) (inf_le_right.trans <| by simp [ht'])
      · simp only [ite_eq_left_iff]
        intro n hn₁ hn₀
        simp only [ht', if_neg hn₀, if_neg hn₁, measure_empty, le_refl, inf_of_le_left]
  · simp only [iInf_image, coe_toOuterMeasure, iInf_pair]
    -- Conversely, fixing `t' : ℕ → Set α` such that `s ⊆ ⋃ n, t' n`, we construct `t : Set α`
    -- for which `μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n, μ (t' n) ⊓ ν (t' n)`.
    -- Denoting `I := {n | μ (t' n) ≤ ν (t' n)}`, we set `t = ⋃ n ∈ I, t' n`.
    -- Clearly `μ (t ∩ s) ≤ ∑' n ∈ I, μ (t' n)` and `ν (tᶜ ∩ s) ≤ ∑' n ∉ I, ν (t' n)`, so
    -- `μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n ∈ I, μ (t' n) + ∑' n ∉ I, ν (t' n)`
    -- where the RHS equals `∑' n, μ (t' n) ⊓ ν (t' n)` by the choice of `I`.
    set t := ⋃ n ∈ {k : ℕ | μ (t' k) ≤ ν (t' k)}, t' n with ht
    suffices hadd : μ (t ∩ s) + ν (tᶜ ∩ s) ≤ ∑' n, μ (t' n) ⊓ ν (t' n) by
      exact le_trans (sInf_le ⟨t, rfl⟩) hadd
    have hle₁ : μ (t ∩ s) ≤ ∑' (n : {k | μ (t' k) ≤ ν (t' k)}), μ (t' n) :=
      (measure_mono inter_subset_left).trans <| measure_biUnion_le _ (to_countable _) _
    have hcap : tᶜ ∩ s ⊆ ⋃ n ∈ {k | ν (t' k) < μ (t' k)}, t' n := by
      simp_rw [ht, compl_iUnion]
      refine fun x ⟨hx₁, hx₂⟩ ↦ mem_iUnion₂.2 ?_
      obtain ⟨i, hi⟩ := mem_iUnion.1 <| ht' hx₂
      refine ⟨i, ?_, hi⟩
      by_contra h
      simp only [mem_ofPred_eq, not_lt] at h
      exact mem_iInter₂.1 hx₁ i h hi
    have hle₂ : ν (tᶜ ∩ s) ≤ ∑' (n : {k | ν (t' k) < μ (t' k)}), ν (t' n) :=
      (measure_mono hcap).trans (measure_biUnion_le ν (to_countable {k | ν (t' k) < μ (t' k)}) _)
    refine (add_le_add hle₁ hle₂).trans ?_
    have heq : {k | μ (t' k) ≤ ν (t' k)} ∪ {k | ν (t' k) < μ (t' k)} = univ := by
      ext k; simp [le_or_gt]
    conv in ∑' (n : ℕ), μ (t' n) ⊓ ν (t' n) => rw [← tsum_univ, ← heq]
    rw [ENNReal.summable.tsum_union_disjoint (f := fun n ↦ μ (t' n) ⊓ ν (t' n)) ?_ ENNReal.summable]
    · refine add_le_add (tsum_congr ?_).le (tsum_congr ?_).le
      · rw [Subtype.forall]
        intro n hn; simpa
      · rw [Subtype.forall]
        intro n hn
        rw [mem_ofPred_eq] at hn
        simp [le_of_lt hn]
    · rw [Set.disjoint_iff]
      rintro k ⟨hk₁, hk₂⟩
      rw [mem_ofPred_eq] at hk₁ hk₂
      exact False.elim <| hk₂.not_ge hk₁

@[simp]
/-
**MeasureTheory.Measure._root_.MeasureTheory.OuterMeasure.toMeasure_top** 是 Math
lib 中的一个定理，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasureTheory.OuterMeasure.toMeasure_top :
    (⊤ : OuterMeasure α).toMeasure (by rw [OuterMeasure.top_caratheodory]; exact le_top) =
      (⊤ : Measure α) :=
  toOuterMeasure_toMeasure (μ := ⊤)

@[simp]
/-
**MeasureTheory.Measure.toOuterMeasure_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：toOuterMeasure_top {_ : MeasurableSpace α} : (⊤ : Measure α).toOuterMeasur
e = (⊤ : OuterMeasure α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOuterMeasure_top {_ : MeasurableSpace α} :
    (⊤ : Measure α).toOuterMeasure = (⊤ : OuterMeasure α) :=
  rfl

@[simp]
/-
**MeasureTheory.Measure.top_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：top_add : ⊤ + μ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `MeasureTheory.Measure.le_add_right`：∀ {α : Type u_1} {m0 : MeasurableSpa
ce α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν + ν'
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem top_add : ⊤ + μ = ⊤ :=
  top_unique <| Measure.le_add_right le_rfl

@[simp]
/-
**MeasureTheory.Measure.add_top** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：add_top : μ + ⊤ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `MeasureTheory.Measure.le_add_left`：∀ {α : Type u_1} {m0 : MeasurableSpac
e α} {μ ν ν' : MeasureTheory.Measure α}, μ ≤ ν → μ ≤ ν' + ν
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem add_top : μ + ⊤ = ⊤ :=
  top_unique <| Measure.le_add_left le_rfl
/-
**MeasureTheory.Measure.zero_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：∀ {α : Type u_1} {_m0 : MeasurableSpace α} (μ : MeasureTheory.Measure α), 
0 ≤ μ
参数：μ : MeasureTheory.Measure α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
protected theorem zero_le {_m0 : MeasurableSpace α} (μ : Measure α) : 0 ≤ μ :=
  bot_le
/-
**MeasureTheory.Measure.nonpos_iff_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：nonpos_iff_eq_zero' : μ <= 0 ↔ μ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.ge_iff_eq'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, b 
≤ a → (a ≤ b ↔ a = b)
· 使用定理 `MeasureTheory.Measure.zero_le`：∀ {α : Type u_1} {_m0 : MeasurableSpace α
} (μ : MeasureTheory.Measure α), 0 ≤ μ
-/
theorem nonpos_iff_eq_zero' : μ ≤ 0 ↔ μ = 0 :=
  μ.zero_le.ge_iff_eq'

@[simp]
/-
**MeasureTheory.Measure.measure_univ_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：measure_univ_eq_zero : μ univ = 0 ↔ μ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem measure_univ_eq_zero : μ univ = 0 ↔ μ = 0 :=
  ⟨fun h => bot_unique fun s => (h ▸ measure_mono (subset_univ s) : μ s ≤ 0), fun h =>
    h.symm ▸ rfl⟩
/-
**MeasureTheory.Measure.measure_univ_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.Measure`。
形式化陈述：measure_univ_ne_zero : μ univ != 0 ↔ μ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
-/
theorem measure_univ_ne_zero : μ univ ≠ 0 ↔ μ ≠ 0 :=
  measure_univ_eq_zero.not
/-
**MeasureTheory.Measure.** 是 Mathlib 中的一个实例，位于命名空间 `MeasureTheory.Measure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NeZero μ] : NeZero (μ univ) := ⟨measure_univ_ne_zero.2 <| NeZero.ne μ⟩

@[simp]
/-
**MeasureTheory.Measure.measure_univ_pos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.Measure`。
形式化陈述：measure_univ_pos : 0 < μ univ ↔ μ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.Measure.measure_univ_ne_zero`：measure_univ_ne_zero : μ uni
v != 0 ↔ μ != 0
-/
theorem measure_univ_pos : 0 < μ univ ↔ μ ≠ 0 :=
  pos_iff_ne_zero.trans measure_univ_ne_zero
/-
**MeasureTheory.Measure.nonempty_of_neZero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：nonempty_of_neZero (μ : Measure α) [NeZero μ] : Nonempty α
参数：μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.eq_empty_of_isEmpty`：eq_empty_of_isEmpty (s : Set α) [IsEmpty s] : s
 = ∅
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `MeasureTheory.measure_empty`：measure_empty : μ ∅ = 0
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `MeasureTheory.Measure.instNeZeroENNRealCoeSetUniv`：∀ {α : Type u_1} {m0 
: MeasurableSpace α} {μ : MeasureTheory.Measure α} [NeZero μ], NeZero (μ Set.uni
v)
-/
lemma nonempty_of_neZero (μ : Measure α) [NeZero μ] : Nonempty α :=
  (isEmpty_or_nonempty α).resolve_left fun h ↦ by
    simpa [eq_empty_of_isEmpty] using NeZero.ne (μ univ)
/-
**MeasureTheory.Measure.measure_support_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.Measure`。
形式化陈述：measure_support_eq_zero_iff {E : Type*} [Zero E] (μ : Measure α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem measure_support_eq_zero_iff {E : Type*} [Zero E] (μ : Measure α := by volume_tac)
    {f : α → E} : μ f.support = 0 ↔ f =ᵐ[μ] 0 := by
  rfl

section Sum
variable {f : ι → Measure α}

/-- Sum of an indexed family of measures. -/
/-
**MeasureTheory.Measure.sum** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measure`。
形式化陈述：sum (f : ι -> Measure α) : Measure α
参数：f : ι -> Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sum of an indexed family of measures.
-/
noncomputable def sum (f : ι → Measure α) : Measure α :=
  (OuterMeasure.sum fun i => (f i).toOuterMeasure).toMeasure <|
    le_trans (le_iInf fun _ => le_toOuterMeasure_caratheodory _)
      (OuterMeasure.le_sum_caratheodory _)
/-
**MeasureTheory.Measure.le_sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：le_sum_apply (f : ι -> Measure α) (s : Set α) : ∑' i, f i s <= sum f s
参数：f : ι -> Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.le_toMeasure_apply`：le_toMeasure_apply (m : OuterMeasure α
) (h : ms <= m.caratheodory) (s : Set α) : m s <= m.toMeasure h s
-/
theorem le_sum_apply (f : ι → Measure α) (s : Set α) : ∑' i, f i s ≤ sum f s :=
  le_toMeasure_apply _ _ _

@[simp]
/-
**MeasureTheory.Measure.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：sum_apply (f : ι -> Measure α) {s : Set α} (hs : MeasurableSet s) : sum f 
s = ∑' i, f i s
参数：f : ι -> Measure α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.toMeasure_apply`：toMeasure_apply (m : OuterMeasure α) (h :
 ms <= m.caratheodory) {s : Set α} (hs : MeasurableSet s) : m.toMeasure h s = m 
s
-/
theorem sum_apply (f : ι → Measure α) {s : Set α} (hs : MeasurableSet s) :
    sum f s = ∑' i, f i s :=
  toMeasure_apply _ _ hs
/-
**MeasureTheory.Measure.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：sum_apply (f : ι -> Measure α) {s : Set α} (hs : MeasurableSet s) : sum f 
s = ∑' i, f i s
参数：f : ι -> Measure α；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.toMeasure_apply`：toMeasure_apply (m : OuterMeasure α) (h :
 ms <= m.caratheodory) {s : Set α} (hs : MeasurableSet s) : m.toMeasure h s = m 
s
-/
theorem sum_apply₀ (f : ι → Measure α) {s : Set α} (hs : NullMeasurableSet s (sum f)) :
    sum f s = ∑' i, f i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases hs.exists_measurable_subset_ae_eq with ⟨t, ts, t_meas, ht⟩
  calc
  sum f s = sum f t := measure_congr ht.symm
  _ = ∑' i, f i t := sum_apply _ t_meas
  _ ≤ ∑' i, f i s := ENNReal.tsum_le_tsum fun i ↦ measure_mono ts

/-! For the next theorem, the countability assumption is necessary. For a counterexample, consider
an uncountable space, with a distinguished point `x₀`, and the sigma-algebra made of countable sets
not containing `x₀`, and their complements. All points but `x₀` are measurable.
Consider the sum of the Dirac masses at points different from `x₀`, and `s = {x₀}`. For any Dirac
mass `δ_x`, we have `δ_x (x₀) = 0`, so `∑' x, δ_x (x₀) = 0`. On the other hand, the measure
`sum δ_x` gives mass one to each point different from `x₀`, so it gives infinite mass to any
measurable set containing `x₀` (as such a set is uncountable), and by outer regularity one gets
`sum δ_x {x₀} = ∞`.
-/
/-
**MeasureTheory.Measure.sum_apply_of_countable** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Measure`。
形式化陈述：sum_apply_of_countable [Countable ι] (f : ι -> Measure α) (s : Set α) : su
m f s = ∑' i, f i s
参数：f : ι -> Measure α；s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MeasureTheory.exists_measurable_superset_forall_eq`：exists_measurable_su
perset_forall_eq [Countable ι] (μ : ι -> Measure α) (s : Set α) : exists t, s su
bseteq t ∧ MeasurableSet t ∧ forall i, μ…
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Measure.le_sum_apply`：le_sum_apply (f : ι -> Measure α) (s
 : Set α) : ∑' i, f i s <= sum f s

--- 原说明 ---
For the next theorem, the countability assumption is necessary. For a counterexa
mple, consider
an uncountable space, with a distinguished point `x₀`, and the sigma-algebra mad
e of countable sets
not containing `x₀`, and their complements. All points but `x₀` are measurable.
Consider the sum of the Dirac masses at points different from `x₀`, and `s = {x₀
}`. For any Dirac
mass `δ_x`, we have `δ_x (x₀) = 0`, so `∑' x, δ_x (x₀) = 0`. On the other hand, 
the measure
`sum δ_x` gives mass one to each point different from `x₀`, so it gives infinite
 mass to any
measurable set containing `x₀` (as such a set is uncountable), and by outer regu
larity one gets
`sum δ_x {x₀} = ∞`.
-/
theorem sum_apply_of_countable [Countable ι] (f : ι → Measure α) (s : Set α) :
    sum f s = ∑' i, f i s := by
  apply le_antisymm ?_ (le_sum_apply _ _)
  rcases exists_measurable_superset_forall_eq f s with ⟨t, hst, htm, ht⟩
  calc
  sum f s ≤ sum f t := measure_mono hst
  _ = ∑' i, f i t := sum_apply _ htm
  _ = ∑' i, f i s := by simp [ht]
/-
**MeasureTheory.Measure.le_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure`
。
形式化陈述：le_sum (μ : ι -> Measure α) (i : ι) : μ i <= sum μ
参数：μ : ι -> Measure α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.le_iff`：le_iff : μ₁ <= μ₂ ↔ forall s, MeasurableSe
t s -> μ₁ s <= μ₂ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `ENNReal.le_tsum`：∀ {α : Type u_1} {f : α → ENNReal} (a : α), f a ≤ ∑' (a
 : α), f a
-/
theorem le_sum (μ : ι → Measure α) (i : ι) : μ i ≤ sum μ :=
  le_iff.2 fun s hs ↦ by simpa only [sum_apply μ hs] using ENNReal.le_tsum i

@[simp]
/-
**MeasureTheory.Measure.sum_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：sum_apply_eq_zero [Countable ι] {μ : ι -> Measure α} {s : Set α} : sum μ s
 = 0 ↔ forall i, μ i s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply_of_countable`：sum_apply_of_countable [Co
untable ι] (f : ι -> Measure α) (s : Set α) : sum f s = ∑' i, f i s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sum_apply_eq_zero [Countable ι] {μ : ι → Measure α} {s : Set α} :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by
  simp [sum_apply_of_countable]
/-
**MeasureTheory.Measure.sum_apply_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：sum_apply_eq_zero' {μ : ι -> Measure α} {s : Set α} (hs : MeasurableSet s)
 : sum μ s = 0 ↔ forall i, μ i s = 0
参数：hs : MeasurableSet s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sum_apply_eq_zero' {μ : ι → Measure α} {s : Set α} (hs : MeasurableSet s) :
    sum μ s = 0 ↔ ∀ i, μ i s = 0 := by simp [hs]
/-
**MeasureTheory.Measure.sum_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_5} {m0 : MeasurableSpace α} {f : ι → MeasureT
heory.Measure α},   MeasureTheory.Measure.sum f = 0 ↔ ∀ (i : ι), f i = 0
参数：i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma sum_eq_zero : sum f = 0 ↔ ∀ i, f i = 0 := by
  simp +contextual [Measure.ext_iff, forall_comm (α := ι)]

@[simp]
/-
**MeasureTheory.Measure.sum_zero** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：sum_zero : Measure.sum (fun (_ : ι) => (0 : Measure α)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_zero : Measure.sum (fun (_ : ι) ↦ (0 : Measure α)) = 0 := by
  ext s hs
  simp [Measure.sum_apply _ hs]
/-
**MeasureTheory.Measure.sum_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measure
`。
形式化陈述：sum_sum {ι' : Type*} (μ : ι -> ι' -> Measure α) : (sum fun n => sum (μ n))
 = sum (fun (p : ι × ι') => μ p.1 p.2)
参数：μ : ι -> ι' -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.tsum_prod'`：∀ {α : Type u_1} {β : Type u_2} {f : α × β → ENNReal
}, ∑' (p : α × β), f p = ∑' (a : α) (b : β), f (a, b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_sum {ι' : Type*} (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum (fun (p : ι × ι') ↦ μ p.1 p.2) := by
  ext1 s hs
  simp [sum_apply _ hs, ENNReal.tsum_prod']
/-
**MeasureTheory.Measure.sum_comm** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：sum_comm {ι' : Type*} (μ : ι -> ι' -> Measure α) : (sum fun n => sum (μ n)
) = sum fun m => sum fun n => μ n m
参数：μ : ι -> ι' -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.tsum_comm`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → ENNReal}
, ∑' (a : α) (b : β), f a b = ∑' (b : β) (a : α), f a b
-/
theorem sum_comm {ι' : Type*} (μ : ι → ι' → Measure α) :
    (sum fun n => sum (μ n)) = sum fun m => sum fun n => μ n m := by
  ext1 s hs
  simp_rw [sum_apply _ hs]
  rw [ENNReal.tsum_comm]
/-
**MeasureTheory.Measure.ae_sum_iff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Meas
ure`。
形式化陈述：ae_sum_iff [Countable ι] {μ : ι -> Measure α} {p : α -> Prop} : (forallᵐ x
 ∂sum μ, p x) ↔ forall i, forallᵐ x ∂μ i, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.sum_apply_eq_zero`：sum_apply_eq_zero [Countable ι]
 {μ : ι -> Measure α} {s : Set α} : sum μ s = 0 ↔ forall i, μ i s = 0
-/
theorem ae_sum_iff [Countable ι] {μ : ι → Measure α} {p : α → Prop} :
    (∀ᵐ x ∂sum μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ i, p x :=
  sum_apply_eq_zero
/-
**MeasureTheory.Measure.ae_sum_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：ae_sum_iff' {μ : ι -> Measure α} {p : α -> Prop} (h : MeasurableSet { x | 
p x }) : (forallᵐ x ∂sum μ, p x) ↔ forall i, forallᵐ x ∂μ i, p x
参数：h : MeasurableSet { x | p x }。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.sum_apply_eq_zero'`：sum_apply_eq_zero' {μ : ι -> M
easure α} {s : Set α} (hs : MeasurableSet s) : sum μ s = 0 ↔ forall i, μ i s = 0
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
-/
theorem ae_sum_iff' {μ : ι → Measure α} {p : α → Prop} (h : MeasurableSet { x | p x }) :
    (∀ᵐ x ∂sum μ, p x) ↔ ∀ i, ∀ᵐ x ∂μ i, p x :=
  sum_apply_eq_zero' h.compl

@[simp]
/-
**MeasureTheory.Measure.sum_fintype** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：sum_fintype [Fintype ι] (μ : ι -> Measure α) : sum μ = ∑ i, μ i
参数：μ : ι -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `MeasureTheory.Measure.finsetSum_apply`：finsetSum_apply {m : MeasurableSp
ace α} (I : Finset ι) (μ : ι -> Measure α) (s : Set α) : (∑ i in I, μ i) s = ∑ i
 in I, μ i s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_fintype [Fintype ι] (μ : ι → Measure α) : sum μ = ∑ i, μ i := by
  ext1 s hs
  simp only [sum_apply, finsetSum_apply, hs, tsum_fintype]
/-
**MeasureTheory.Measure.sum_coe_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：sum_coe_finset (s : Finset ι) (μ : ι -> Measure α) : (sum fun i : s => μ i
) = ∑ i in s, μ i
参数：s : Finset ι；μ : ι -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_fintype`：sum_fintype [Fintype ι] (μ : ι -> Mea
sure α) : sum μ = ∑ i, μ i
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
-/
theorem sum_coe_finset (s : Finset ι) (μ : ι → Measure α) :
    (sum fun i : s => μ i) = ∑ i ∈ s, μ i := by rw [sum_fintype, Finset.sum_coe_sort s μ]

@[simp]
/-
**MeasureTheory.Measure.ae_sum_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：ae_sum_eq [Countable ι] (μ : ι -> Measure α) : ae (sum μ) = ⨆ i, ae (μ i)
参数：μ : ι -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ext`：∀ {α : Type u_1} {f g : Filter α}, (∀ (s : Set α), s ∈ f ↔ s
 ∈ g) → f = g
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.ae_sum_iff`：ae_sum_iff [Countable ι] {μ : ι -> Mea
sure α} {p : α -> Prop} : (forallᵐ x ∂sum μ, p x) ↔ forall i, forallᵐ x ∂μ i, p 
x
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.mem_iSup`：mem_iSup {x : Set α} {f : ι -> Filter α} : x in iSup f 
↔ forall i, x in f i
-/
theorem ae_sum_eq [Countable ι] (μ : ι → Measure α) : ae (sum μ) = ⨆ i, ae (μ i) :=
  Filter.ext fun _ => ae_sum_iff.trans mem_iSup.symm
/-
**MeasureTheory.Measure.sum_bool** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：sum_bool (f : Bool -> Measure α) : sum f = f true + f false
参数：f : Bool -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_fintype`：sum_fintype [Fintype ι] (μ : ι -> Mea
sure α) : sum μ = ∑ i, μ i
· 使用定理 `Fintype.sum_bool`：∀ {α : Type u_1} [inst : AddCommMonoid α] (f : Bool → 
α), ∑ b, f b = f true + f false
-/
theorem sum_bool (f : Bool → Measure α) : sum f = f true + f false := by
  rw [sum_fintype, Fintype.sum_bool]
/-
**MeasureTheory.Measure.sum_cond** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：sum_cond (μ ν : Measure α) : (sum fun b => cond b μ ν) = μ + ν
参数：μ ν : Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.sum_bool`：sum_bool (f : Bool -> Measure α) : sum f
 = f true + f false
-/
theorem sum_cond (μ ν : Measure α) : (sum fun b => cond b μ ν) = μ + ν :=
  sum_bool _

@[simp]
/-
**MeasureTheory.Measure.sum_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：sum_of_isEmpty [IsEmpty ι] (μ : ι -> Measure α) : sum μ = 0
参数：μ : ι -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `tsum_empty`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter β} [IsEmpty β], ∑'
…
-/
theorem sum_of_isEmpty [IsEmpty ι] (μ : ι → Measure α) : sum μ = 0 := by
  rw [← measure_univ_eq_zero, sum_apply _ MeasurableSet.univ, tsum_empty]
/-
**MeasureTheory.Measure.sum_add_sum_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Measure`。
形式化陈述：sum_add_sum_compl (s : Set ι) (μ : ι -> Measure α) : ((sum fun i : s => μ 
i) + sum fun i : ↥sᶜ => μ i) = sum μ
参数：s : Set ι；μ : ι -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `Summable.tsum_add_tsum_compl`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α} [T2Space α]   [Continuo
usAdd α] {s : Set …
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
-/
theorem sum_add_sum_compl (s : Set ι) (μ : ι → Measure α) :
    ((sum fun i : s => μ i) + sum fun i : ↥sᶜ => μ i) = sum μ := by
  ext1 t ht
  simp only [add_apply, sum_apply _ ht]
  exact ENNReal.summable.tsum_add_tsum_compl (f := fun i => μ i t) ENNReal.summable
/-
**MeasureTheory.Measure.sum_congr** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measu
re`。
形式化陈述：sum_congr {μ ν : Nat -> Measure α} (h : forall n, μ n = ν n) : sum μ = sum
 ν
参数：h : forall n, μ n = ν n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem sum_congr {μ ν : ℕ → Measure α} (h : ∀ n, μ n = ν n) : sum μ = sum ν :=
  congr_arg sum (funext h)
/-
**MeasureTheory.Measure.sum_add_sum** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Mea
sure`。
形式化陈述：sum_add_sum {ι : Type*} (μ ν : ι -> Measure α) : sum μ + sum ν = sum fun n
 => μ n + ν n
参数：μ ν : ι -> Measure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `Summable.tsum_add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid
 α] [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [T2Spa
ce α] […
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `ENNReal.instContinuousAdd`：ContinuousAdd ENNReal
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `ENNReal.summable`：∀ {α : Type u_1} {f : α → ENNReal}, Summable f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_add_sum {ι : Type*} (μ ν : ι → Measure α) : sum μ + sum ν = sum fun n => μ n + ν n := by
  ext1 s hs
  simp only [add_apply, sum_apply _ hs,
    ENNReal.summable.tsum_add ENNReal.summable]
/-
**MeasureTheory.Measure.sum_comp_equiv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {ι : Type u_8} {ι' : Type u_9} (
e : ι' ≃ ι) (m : ι → MeasureTheory.Measure α),   MeasureTheory.Measure.sum (m ∘ 
⇑e) = MeasureTheory.Measure.sum m
参数：e : ι' ≃ ι；m : ι → MeasureTheory.Measure α；m ∘ ⇑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
-/
@[simp] lemma sum_comp_equiv {ι ι' : Type*} (e : ι' ≃ ι) (m : ι → Measure α) :
    sum (m ∘ e) = sum m := by
  ext s hs
  simpa [hs, sum_apply] using e.tsum_eq (fun n ↦ m n s)
/-
**MeasureTheory.Measure.sum_extend_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.Measure`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {ι : Type u_8} {ι' : Type u_9} {
f : ι → ι'},   Function.Injective f →     ∀ (m : ι → MeasureTheory.Measure α), M
easureTheory.Measure.sum (Function.extend f m 0) = MeasureTheory.Measure.sum m
参数：m : ι → MeasureTheory.Measure α；Function.extend f m 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.sum_apply`：sum_apply (f : ι -> Measure α) {s : Set
 α} (hs : MeasurableSet s) : sum f s = ∑' i, f i s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Function.apply_extend`：apply_extend {δ} {g : α -> γ} (F : γ -> δ) (f : α
 -> β) (e' : β -> γ) (b : β) : F (extend f g e' b) = extend f (F ∘ g) (F ∘ e') b
· 使用定理 `tsum_extend_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid 
α] [inst_1 : TopologicalSpace α] {γ : Type u_4} {g : γ → β},   Function.Injectiv
e g → …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma sum_extend_zero {ι ι' : Type*} {f : ι → ι'} (hf : Injective f) (m : ι → Measure α) :
    sum (Function.extend f m 0) = sum m := by
  ext s hs
  simp [*, Function.apply_extend (fun μ : Measure α ↦ μ s)]
end Sum

/-! ### The `cofinite` filter -/

/-- The filter of sets `s` such that `sᶜ` has finite measure. -/
/-
**MeasureTheory.Measure.cofinite** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Measur
e`。
形式化陈述：cofinite {m0 : MeasurableSpace α} (μ : Measure α) : Filter α
参数：μ : Measure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The filter of sets `s` such that `sᶜ` has finite measure.
-/
def cofinite {m0 : MeasurableSpace α} (μ : Measure α) : Filter α :=
  comk (μ · < ∞) (by simp) (fun _ ht _ hs ↦ (measure_mono hs).trans_lt ht) fun s hs t ht ↦
    (measure_union_le s t).trans_lt <| ENNReal.add_lt_top.2 ⟨hs, ht⟩
/-
**MeasureTheory.Measure.mem_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Me
asure`。
形式化陈述：mem_cofinite : s in μ.cofinite ↔ μ sᶜ < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cofinite : s ∈ μ.cofinite ↔ μ sᶜ < ∞ :=
  Iff.rfl
/-
**MeasureTheory.Measure.compl_mem_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Measure`。
形式化陈述：compl_mem_cofinite : sᶜ in μ.cofinite ↔ μ s < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.mem_cofinite`：mem_cofinite : s in μ.cofinite ↔ μ s
ᶜ < ∞
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compl_mem_cofinite : sᶜ ∈ μ.cofinite ↔ μ s < ∞ := by rw [mem_cofinite, compl_compl]
/-
**MeasureTheory.Measure.eventually_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.Measure`。
形式化陈述：eventually_cofinite {p : α -> Prop} : (forallᶠ x in μ.cofinite, p x) ↔ μ {
 x | ¬p x } < ∞
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eventually_cofinite {p : α → Prop} : (∀ᶠ x in μ.cofinite, p x) ↔ μ { x | ¬p x } < ∞ :=
  Iff.rfl
/-
**MeasureTheory.Measure.cofinite.instIsMeasurablyGenerated** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.Measure.cofinite`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}, μ
.cofinite.IsMeasurablyGenerated
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.compl_mem_cofinite`：compl_mem_cofinite : sᶜ in μ.c
ofinite ↔ μ s < ∞
· 使用定理 `MeasureTheory.measure_toMeasurable`：measure_toMeasurable (s : Set α) : μ
 (toMeasurable μ s) = μ s
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.measurableSet_toMeasurable`：measurableSet_toMeasurable (μ 
: Measure α) (s : Set α) : MeasurableSet (toMeasurable μ s)
· 使用定理 `Set.compl_subset_comm`：compl_subset_comm : sᶜ subseteq t ↔ tᶜ subseteq s
· 使用定理 `MeasureTheory.subset_toMeasurable`：subset_toMeasurable (μ : Measure α) (
s : Set α) : s subseteq toMeasurable μ s
-/
instance cofinite.instIsMeasurablyGenerated : IsMeasurablyGenerated μ.cofinite where
  exists_measurable_subset s hs := by
    refine ⟨(toMeasurable μ sᶜ)ᶜ, ?_, (measurableSet_toMeasurable _ _).compl, ?_⟩
    · rwa [compl_mem_cofinite, measure_toMeasurable]
    · rw [compl_subset_comm]
      apply subset_toMeasurable
/-
**MeasureTheory.Measure.cofinite_le_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.
Measure`。
形式化陈述：cofinite_le_ae : μ.cofinite <= ae μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem cofinite_le_ae : μ.cofinite ≤ ae μ := by
  intro s hs
  simp_all [mem_cofinite, mem_ae_iff]

end Measure

open Measure

open MeasureTheory

/-
**MeasureTheory._root_.AEMeasurable.nullMeasurable** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.AEMeasurable.nullMeasurable {f : α → β} (h : AEMeasurable f μ) :
    NullMeasurable f μ :=
  let ⟨_g, hgm, hg⟩ := h; hgm.nullMeasurable.congr hg.symm
/-
**MeasureTheory._root_.AEMeasurable.nullMeasurableSet_preimage** 是 Mathlib 中的一个引
理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.AEMeasurable.nullMeasurableSet_preimage {f : α → β} {s : Set β}
    (hf : AEMeasurable f μ) (hs : MeasurableSet s) : NullMeasurableSet (f ⁻¹' s) μ :=
  hf.nullMeasurable hs

@[simp]
/-
**MeasureTheory.ae_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_bot : ae μ = ⊥ ↔ μ = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.empty_mem_iff_bot`：empty_mem_iff_bot {f : Filter α} : ∅ in f ↔ f 
= ⊥
· 使用定理 `MeasureTheory.mem_ae_iff`：mem_ae_iff {s : Set α} : s in ae μ ↔ μ sᶜ = 0
· 使用定理 `Set.compl_empty`：compl_empty : (∅ : Set α)ᶜ = univ
· 使用定理 `MeasureTheory.Measure.measure_univ_eq_zero`：measure_univ_eq_zero : μ uni
v = 0 ↔ μ = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ae_eq_bot : ae μ = ⊥ ↔ μ = 0 := by
  rw [← empty_mem_iff_bot, mem_ae_iff, compl_empty, measure_univ_eq_zero]

@[simp]
/-
**MeasureTheory.ae_neBot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_neBot : (ae μ).NeBot ↔ μ != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MeasureTheory.ae_eq_bot`：ae_eq_bot : ae μ = ⊥ ↔ μ = 0
-/
theorem ae_neBot : (ae μ).NeBot ↔ μ ≠ 0 :=
  neBot_iff.trans (not_congr ae_eq_bot)
/-
**MeasureTheory.Measure.ae.neBot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.Measur
e.ae`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [N
eZero μ], (MeasureTheory.ae μ).NeBot
参数：MeasureTheory.ae μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_neBot`：ae_neBot : (ae μ).NeBot ↔ μ != 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
instance Measure.ae.neBot [NeZero μ] : (ae μ).NeBot := ae_neBot.2 <| NeZero.ne μ

@[simp]
/-
**MeasureTheory.ae_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measure α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_bot`：ae_eq_bot : ae μ = ⊥ ↔ μ = 0
-/
theorem ae_zero {_m0 : MeasurableSpace α} : ae (0 : Measure α) = ⊥ :=
  ae_eq_bot.2 rfl

section Intervals

/-
**MeasureTheory.biSup_measure_Iic** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：biSup_measure_Iic [Preorder α] {s : Set α} (hsc : s.Countable) (hst : fora
ll x : α, exists y in s, x <= y) (hdir : DirectedOn (· <= ·) s) : ⨆ x in s, μ (I
ic x) = μ univ
参数：hsc : s.Countable；hst : forall x : α, exists y in s, x <= y；hdir : DirectedOn
 (· <= ·) s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_biUnion_eq_iSup`：measure_biUnion_eq_iSup {s : ι ->
 Set α} {t : Set ι} (ht : t.Countable) (hd : DirectedOn ((· subseteq ·) on s) t)
 : μ (⋃ i in t, s i) = ⨆ i …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `directedOn_iff_directed`：directedOn_iff_directed {s} : @DirectedOn α r s
 ↔ Directed r (Subtype.val : s -> α)
· 使用定理 `Directed.mono_comp`：Directed.mono_comp (r : α -> α -> Prop) {ι} {rb : β 
-> β -> Prop} {g : α -> β} {f : ι -> α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g
 y)) (hf…
· 使用定理 `Set.Iic_subset_Iic`：Iic_subset_Iic : Iic a subseteq Iic b ↔ a <= b
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.iUnion₂_eq_univ_iff`：iUnion₂_eq_univ_iff {s : forall i, κ i -> Set α
} : ⋃ (i) (j), s i j = univ ↔ forall a, exists i j, a in s i j
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem biSup_measure_Iic [Preorder α] {s : Set α} (hsc : s.Countable)
    (hst : ∀ x : α, ∃ y ∈ s, x ≤ y) (hdir : DirectedOn (· ≤ ·) s) :
    ⨆ x ∈ s, μ (Iic x) = μ univ := by
  rw [← measure_biUnion_eq_iSup hsc]
  · congr
    simp only [← bex_def] at hst
    exact iUnion₂_eq_univ_iff.2 hst
  · exact directedOn_iff_directed.2 (hdir.directed_val.mono_comp _ fun x y => Iic_subset_Iic.2)
/-
**MeasureTheory.tendsto_measure_Ico_atTop** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_measure_Ico_atTop [Preorder α] [NoMaxOrder α] [(atTop : Filter α).
IsCountablyGenerated] (μ : Measure α) (a : α) : Tendsto (fun x => μ (Ico a x)) a
tTop (𝓝 (μ (Ici a)))
参数：atTop : Filter α；μ : Measure α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_Ico_right`：iUnion_Ico_right [NoMaxOrder α] (a : α) : ⋃ b, Ico
 a b = Ici a
· 使用定理 `MeasureTheory.tendsto_measure_iUnion_atTop`：tendsto_measure_iUnion_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hm : M
onotone s) : Tendsto (μ ∘ s) atT…
· 使用定理 `Antitone.Ico`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f g : α → β},   Antitone f → Monotone g → Monotone fun x => Set
.I…
· 使用定理 `antitone_const`：antitone_const [Preorder α] [Preorder β] {c : β} : Antit
one fun _ : α => c
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
-/
theorem tendsto_measure_Ico_atTop [Preorder α] [NoMaxOrder α]
    [(atTop : Filter α).IsCountablyGenerated] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ico a x)) atTop (𝓝 (μ (Ici a))) := by
  rw [← iUnion_Ico_right]
  exact tendsto_measure_iUnion_atTop (antitone_const.Ico monotone_id)
/-
**MeasureTheory.tendsto_measure_Ioc_atBot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_measure_Ioc_atBot [Preorder α] [NoMinOrder α] [(atBot : Filter α).
IsCountablyGenerated] (μ : Measure α) (a : α) : Tendsto (fun x => μ (Ioc x a)) a
tBot (𝓝 (μ (Iic a)))
参数：atBot : Filter α；μ : Measure α；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_Ioc_left`：∀ {α : Type v} [inst : Preorder α] [NoMinOrder α] (
a : α), ⋃ b, Set.Ioc b a = Set.Iic a
· 使用定理 `MeasureTheory.tendsto_measure_iUnion_atBot`：tendsto_measure_iUnion_atBot
 [Preorder ι] [IsCountablyGenerated (atBot : Filter ι)] {s : ι -> Set α} (hm : A
ntitone s) : Tendsto (μ ∘ s) atB…
· 使用定理 `Monotone.Ioc`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] [inst_
1 : Preorder β] {f g : α → β},   Monotone f → Antitone g → Antitone fun x => Set
.I…
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)
· 使用定理 `antitone_const`：antitone_const [Preorder α] [Preorder β] {c : β} : Antit
one fun _ : α => c
-/
theorem tendsto_measure_Ioc_atBot [Preorder α] [NoMinOrder α]
    [(atBot : Filter α).IsCountablyGenerated] (μ : Measure α) (a : α) :
    Tendsto (fun x => μ (Ioc x a)) atBot (𝓝 (μ (Iic a))) := by
  rw [← iUnion_Ioc_left]
  exact tendsto_measure_iUnion_atBot (monotone_id.Ioc antitone_const)
/-
**MeasureTheory.tendsto_measure_Iic_atTop** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_measure_Iic_atTop [Preorder α] [(atTop : Filter α).IsCountablyGene
rated] (μ : Measure α) : Tendsto (fun x => μ (Iic x)) atTop (𝓝 (μ univ))
参数：atTop : Filter α；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_Iic`：iUnion_Iic : ⋃ a : α, Iic a = univ
· 使用定理 `MeasureTheory.tendsto_measure_iUnion_atTop`：tendsto_measure_iUnion_atTop
 [Preorder ι] [IsCountablyGenerated (atTop : Filter ι)] {s : ι -> Set α} (hm : M
onotone s) : Tendsto (μ ∘ s) atT…
· 使用定理 `monotone_Iic`：monotone_Iic : Monotone (Iic : α -> Set α)
-/
theorem tendsto_measure_Iic_atTop [Preorder α] [(atTop : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Iic x)) atTop (𝓝 (μ univ)) := by
  rw [← iUnion_Iic]
  exact tendsto_measure_iUnion_atTop monotone_Iic
/-
**MeasureTheory.tendsto_measure_Ici_atBot** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：tendsto_measure_Ici_atBot [Preorder α] [(atBot : Filter α).IsCountablyGene
rated] (μ : Measure α) : Tendsto (fun x => μ (Ici x)) atBot (𝓝 (μ univ))
参数：atBot : Filter α；μ : Measure α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_measure_Iic_atTop`：tendsto_measure_Iic_atTop [Preo
rder α] [(atTop : Filter α).IsCountablyGenerated] (μ : Measure α) : Tendsto (fun
 x => μ (Iic x)) atTop (𝓝 (μ …
· 使用定理 `OrderDual.instIsCountablyGeneratedAtTop`：∀ {α : Type u_1} [inst : Preord
er α] [Filter.atBot.IsCountablyGenerated], Filter.atTop.IsCountablyGenerated
-/
theorem tendsto_measure_Ici_atBot [Preorder α] [(atBot : Filter α).IsCountablyGenerated]
    (μ : Measure α) : Tendsto (fun x => μ (Ici x)) atBot (𝓝 (μ univ)) :=
  tendsto_measure_Iic_atTop (α := αᵒᵈ) μ

variable [PartialOrder α] {a b : α}
/-
**MeasureTheory.Iio_ae_eq_Iic'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ[μ] Iic a
参数：ha : μ {a} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iic_sdiff_right`：Iic_sdiff_right : Iic a \ {a} = Iio a
· 使用定理 `MeasureTheory.sdiff_ae_eq_self`：sdiff_ae_eq_self : (s \ t : Set α) =ᵐ[μ]
 s ↔ μ (s inter t) = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ[μ] Iic a := by
  rw [← Iic_sdiff_right, sdiff_ae_eq_self, measure_mono_null Set.inter_subset_right ha]
/-
**MeasureTheory.Ioi_ae_eq_Ici'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ[μ] Ici a
参数：ha : μ {a} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Iio_ae_eq_Iic'`：Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ
[μ] Iic a
-/
theorem Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ[μ] Ici a :=
  Iio_ae_eq_Iic' (α := αᵒᵈ) ha
/-
**MeasureTheory.Ioo_ae_eq_Ioc'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Ioc a b
参数：hb : μ {b} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
· 使用定理 `MeasureTheory.Iio_ae_eq_Iic'`：Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ
[μ] Iic a
-/
theorem Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Ioc a b :=
  (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)
/-
**MeasureTheory.Ioc_ae_eq_Icc'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b =ᵐ[μ] Icc a b
参数：ha : μ {a} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Ioi_ae_eq_Ici'`：Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ
[μ] Ici a
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)
/-
**MeasureTheory.Ioo_ae_eq_Ico'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b =ᵐ[μ] Ico a b
参数：ha : μ {a} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Ioi_ae_eq_Ici'`：Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ
[μ] Ici a
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
-/
theorem Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b =ᵐ[μ] Ico a b :=
  (Ioi_ae_eq_Ici' ha).inter (ae_eq_refl _)
/-
**MeasureTheory.Ioo_ae_eq_Icc'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Icc a b
参数：ha : μ {a} = 0；hb : μ {b} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Ioi_ae_eq_Ici'`：Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ
[μ] Ici a
· 使用定理 `MeasureTheory.Iio_ae_eq_Iic'`：Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ
[μ] Iic a
-/
theorem Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ioo a b =ᵐ[μ] Icc a b :=
  (Ioi_ae_eq_Ici' ha).inter (Iio_ae_eq_Iic' hb)
/-
**MeasureTheory.Ico_ae_eq_Icc'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ico_ae_eq_Icc' (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Icc a b
参数：hb : μ {b} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.inter`：∀ {α : Type u} {s t s' t' : Set α} {l : Filte
r α}, s =ᶠ[l] t → s' =ᶠ[l] t' → s ∩ s' =ᶠ[l] t ∩ t'
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.ae_eq_refl`：ae_eq_refl (f : α -> β) : f =ᵐ[μ] f
· 使用定理 `MeasureTheory.Iio_ae_eq_Iic'`：Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ
[μ] Iic a
-/
theorem Ico_ae_eq_Icc' (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Icc a b :=
  (ae_eq_refl _).inter (Iio_ae_eq_Iic' hb)
/-
**MeasureTheory.Ico_ae_eq_Ioc'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Ico_ae_eq_Ioc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Ioc a b
参数：ha : μ {a} = 0；hb : μ {b} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans`：∀ {α : Type u} {β : Type v} {l : Filter α} {f
 g h : α → β}, f =ᶠ[l] g → g =ᶠ[l] h → f =ᶠ[l] h
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ico'`：Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b 
=ᵐ[μ] Ico a b
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc'`：Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b 
=ᵐ[μ] Ioc a b
-/
theorem Ico_ae_eq_Ioc' (ha : μ {a} = 0) (hb : μ {b} = 0) : Ico a b =ᵐ[μ] Ioc a b :=
  (Ioo_ae_eq_Ico' ha).symm.trans (Ioo_ae_eq_Ioc' hb)

end Intervals

end

end MeasureTheory

end

set_option linter.style.longFile 1700

