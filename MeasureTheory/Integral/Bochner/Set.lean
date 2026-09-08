/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov
-/
module

public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.MetricSpace.ThickenedIndicator

/-!
# Set integral

In this file we prove some properties of `∫ x in s, f x ∂μ`. Recall that this notation
is defined as `∫ x, f x ∂(μ.restrict s)`. In `integral_indicator` we prove that for a measurable
function `f` and a measurable set `s` this definition coincides with another natural definition:
`∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ`, where `indicator s f x` is equal to `f x` for `x ∈ s`
and is zero otherwise.

Since `∫ x in s, f x ∂μ` is a notation, one can rewrite or apply any theorem about `∫ x, f x ∂μ`
directly. In this file we prove some theorems about dependence of `∫ x in s, f x ∂μ` on `s`, e.g.
`setIntegral_union`, `setIntegral_empty`, `setIntegral_univ`.

We use the property `IntegrableOn f s μ := Integrable f (μ.restrict s)`, defined in
`MeasureTheory.IntegrableOn`. We also defined in that same file a predicate
`IntegrableAtFilter (f : X → E) (l : Filter X) (μ : Measure X)` saying that `f` is integrable at
some set `s ∈ l`.

## Notation

We provide the following notations for expressing the integral of a function on a set :
* `∫ x in s, f x ∂μ` is `MeasureTheory.integral (μ.restrict s) f`
* `∫ x in s, f x` is `∫ x in s, f x ∂volume`

Note that the set notations are defined in the file
`Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`,
but we reference them here because all theorems about set integrals are in this file.
-/

@[expose] public section

assert_not_exists InnerProductSpace

open Filter Function MeasureTheory RCLike Set TopologicalSpace Topology
open scoped ENNReal NNReal Finset

variable {X Y E F : Type*}

namespace MeasureTheory

variable {mX : MeasurableSpace X}

section NormedAddCommGroup

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f g : X → E} {s t : Set X} {μ : Measure X}

/-
**MeasureTheory.setIntegral_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_congr_ae (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f
 x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : forallᵐ x ∂μ, x in s -> f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
-/
theorem setIntegral_congr_ae₀ (hs : NullMeasurableSet s μ) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  integral_congr_ae ((ae_restrict_iff'₀ hs).2 h)
/-
**MeasureTheory.setIntegral_congr_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_congr_ae (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s -> f
 x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : forallᵐ x ∂μ, x in s -> f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
-/
theorem setIntegral_congr_ae (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x = g x) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  integral_congr_ae ((ae_restrict_iff' hs).2 h)
/-
**MeasureTheory.setIntegral_congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_congr_fun (hs : MeasurableSet s) (h : EqOn f g s) : ∫ x in s, 
f x ∂μ = ∫ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem setIntegral_congr_fun₀ (hs : NullMeasurableSet s μ) (h : EqOn f g s) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_congr_ae₀ hs <| Eventually.of_forall h
/-
**MeasureTheory.setIntegral_congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_congr_fun (hs : MeasurableSet s) (h : EqOn f g s) : ∫ x in s, 
f x ∂μ = ∫ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : EqOn f g s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem setIntegral_congr_fun (hs : MeasurableSet s) (h : EqOn f g s) :
    ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ :=
  setIntegral_congr_ae hs <| Eventually.of_forall h
/-
**MeasureTheory.setIntegral_congr_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_congr_set (hst : s =ᵐ[μ] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x
 ∂μ
参数：hst : s =ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_congr_set`：restrict_congr_set (h : s =ᵐ[μ
] t) : μ.restrict s = μ.restrict t
-/
theorem setIntegral_congr_set (hst : s =ᵐ[μ] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ := by
  rw [Measure.restrict_congr_set hst]
/-
**MeasureTheory.setIntegral_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_union (hst : Disjoint s t) (ht : MeasurableSet t) (hfs : Integ
rableOn f s μ) (hft : IntegrableOn f t μ) : ∫ x in s union t, f x ∂μ = ∫ x in s,
 f x ∂μ + ∫ x in t, f x ∂μ
参数：hst : Disjoint s t；ht : MeasurableSet t；hfs : IntegrableOn f s μ；hft : Integr
ableOn f t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_union₀`：setIntegral_union₀ (hst : AEDisjoint μ
 s t) (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) (hft : IntegrableO
n f t μ) : ∫ x in s un…
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem setIntegral_union₀ (hst : AEDisjoint μ s t) (ht : NullMeasurableSet t μ)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ := by
  simp only [Measure.restrict_union₀ hst ht, integral_add_measure hfs hft]

@[deprecated (since := "2026-03-04")] alias integral_union_ae := setIntegral_union₀
/-
**MeasureTheory.setIntegral_union** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_union (hst : Disjoint s t) (ht : MeasurableSet t) (hfs : Integ
rableOn f s μ) (hft : IntegrableOn f t μ) : ∫ x in s union t, f x ∂μ = ∫ x in s,
 f x ∂μ + ∫ x in t, f x ∂μ
参数：hst : Disjoint s t；ht : MeasurableSet t；hfs : IntegrableOn f s μ；hft : Integr
ableOn f t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_union₀`：setIntegral_union₀ (hst : AEDisjoint μ
 s t) (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) (hft : IntegrableO
n f t μ) : ∫ x in s un…
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem setIntegral_union (hst : Disjoint s t) (ht : MeasurableSet t) (hfs : IntegrableOn f s μ)
    (hft : IntegrableOn f t μ) : ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ + ∫ x in t, f x ∂μ :=
  setIntegral_union₀ hst.aedisjoint ht.nullMeasurableSet hfs hft
/-
**MeasureTheory.setIntegral_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_sdiff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hts :
 t subseteq s) : ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ
参数：ht : MeasurableSet t；hfs : IntegrableOn f s μ；hts : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_sdiff₀`：setIntegral_sdiff₀ (ht : NullMeasurabl
eSet t μ) (hfs : IntegrableOn f s μ) (hts : t subseteq s) : ∫ x in s \ t, f x ∂μ
 = ∫ x in s, f x ∂μ - …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem setIntegral_sdiff₀ (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) (hts : t ⊆ s) :
    ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ := by
  rw [eq_sub_iff_add_eq, ← setIntegral_union₀, sdiff_union_of_subset hts]
  exacts [disjoint_sdiff_self_left.aedisjoint, ht, hfs.mono_set sdiff_subset, hfs.mono_set hts]

@[deprecated (since := "2026-06-03")] alias setIntegral_diff₀ := setIntegral_sdiff₀
/-
**MeasureTheory.setIntegral_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_sdiff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hts :
 t subseteq s) : ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ
参数：ht : MeasurableSet t；hfs : IntegrableOn f s μ；hts : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_sdiff₀`：setIntegral_sdiff₀ (ht : NullMeasurabl
eSet t μ) (hfs : IntegrableOn f s μ) (hts : t subseteq s) : ∫ x in s \ t, f x ∂μ
 = ∫ x in s, f x ∂μ - …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem setIntegral_sdiff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hts : t ⊆ s) :
    ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ - ∫ x in t, f x ∂μ :=
  setIntegral_sdiff₀ ht.nullMeasurableSet hfs hts

@[deprecated (since := "2026-06-03")] alias setIntegral_diff := setIntegral_sdiff

@[deprecated (since := "2026-03-04")] alias integral_diff := setIntegral_sdiff
/-
**MeasureTheory.integral_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integral_inter_add_sdiff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ)
 : ∫ x in s inter t, f x ∂μ + ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ
参数：ht : MeasurableSet t；hfs : IntegrableOn f s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_inter_add_sdiff₀`：integral_inter_add_sdiff₀ (ht :
 NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) : ∫ x in s inter t, f x ∂μ + 
∫ x in s \ t, f x ∂μ = ∫ x in…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem integral_inter_add_sdiff₀ (ht : NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) :
    ∫ x in s ∩ t, f x ∂μ + ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← Measure.restrict_inter_add_sdiff₀ s ht, integral_add_measure]
  · exact Integrable.mono_measure hfs (Measure.restrict_mono inter_subset_left le_rfl)
  · exact Integrable.mono_measure hfs (Measure.restrict_mono sdiff_subset le_rfl)

@[deprecated (since := "2026-06-03")] alias integral_inter_add_diff₀ := integral_inter_add_sdiff₀
/-
**MeasureTheory.integral_inter_add_sdiff** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integral_inter_add_sdiff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ)
 : ∫ x in s inter t, f x ∂μ + ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ
参数：ht : MeasurableSet t；hfs : IntegrableOn f s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_inter_add_sdiff₀`：integral_inter_add_sdiff₀ (ht :
 NullMeasurableSet t μ) (hfs : IntegrableOn f s μ) : ∫ x in s inter t, f x ∂μ + 
∫ x in s \ t, f x ∂μ = ∫ x in…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem integral_inter_add_sdiff (ht : MeasurableSet t) (hfs : IntegrableOn f s μ) :
    ∫ x in s ∩ t, f x ∂μ + ∫ x in s \ t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_inter_add_sdiff₀ ht.nullMeasurableSet hfs

@[deprecated (since := "2026-06-03")] alias integral_inter_add_diff := integral_inter_add_sdiff
/-
**MeasureTheory.integral_biUnion_finset** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：integral_biUnion_finset {ι : Type*} (t : Finset ι) {s : ι -> Set X} (hs : 
forall i in t, MeasurableSet (s i)) (h's : Set.Pairwise (↑t) (Disjoint on s)) (h
f : forall i in t, IntegrableOn f (s i) μ) : ∫ x in ⋃ i in t, s i, f x ∂μ = ∑ i 
in t, ∫ x in s i, f x ∂μ
参数：t : Finset ι；hs : forall i in t, MeasurableSet (s i)；h's : Set.Pairwise (↑t) 
(Disjoint on s)；hf : forall i in t, IntegrableOn f (s i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.set_biUnion_insert`：set_biUnion_insert (a : α) (s : Finset α) (t 
: α -> Set β) : ⋃ x in insert a s, t x = t a union ⋃ x in s, t x
· 使用定理 `MeasureTheory.setIntegral_union`：setIntegral_union (hst : Disjoint s t) 
(ht : MeasurableSet t) (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ) : ∫
 x in s union t, f x …
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
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.integrableOn_finset_iUnion`：integrableOn_finset_iUnion [Ps
eudoMetrizableSpace ε] {s : Finset β} {t : β -> Set α} : IntegrableOn f (⋃ i in 
s, t i) μ ↔ forall i in s, Int…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
-/
theorem integral_biUnion_finset {ι : Type*} (t : Finset ι) {s : ι → Set X}
    (hs : ∀ i ∈ t, MeasurableSet (s i)) (h's : Set.Pairwise (↑t) (Disjoint on s))
    (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ i ∈ t, ∫ x in s i, f x ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert _ _ hat IH =>
    simp only [Finset.coe_insert, Finset.forall_mem_insert, Set.pairwise_insert,
      Finset.set_biUnion_insert] at hs hf h's ⊢
    rw [setIntegral_union _ _ hf.1 (integrableOn_finset_iUnion.2 hf.2)]
    · rw [Finset.sum_insert hat, IH hs.2 h's.1 hf.2]
    · simp only [disjoint_iUnion_right]
      exact fun i hi => (h's.2 i hi (ne_of_mem_of_not_mem hi hat).symm).1
    · exact Finset.measurableSet_biUnion _ hs.2
/-
**MeasureTheory.integral_iUnion_fintype** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：integral_iUnion_fintype {ι : Type*} [Fintype ι] {s : ι -> Set X} (hs : for
all i, MeasurableSet (s i)) (h's : Pairwise (Disjoint on s)) (hf : forall i, Int
egrableOn f (s i) μ) : ∫ x in ⋃ i, s i, f x ∂μ = ∑ i, ∫ x in s i, f x ∂μ
参数：hs : forall i, MeasurableSet (s i)；h's : Pairwise (Disjoint on s)；hf : forall
 i, IntegrableOn f (s i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `MeasureTheory.integral_biUnion_finset`：integral_biUnion_finset {ι : Type
*} (t : Finset ι) {s : ι -> Set X} (hs : forall i in t, MeasurableSet (s i)) (h'
s : Set.Pairwise (↑t) (Disj…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem integral_iUnion_fintype {ι : Type*} [Fintype ι] {s : ι → Set X}
    (hs : ∀ i, MeasurableSet (s i)) (h's : Pairwise (Disjoint on s))
    (hf : ∀ i, IntegrableOn f (s i) μ) : ∫ x in ⋃ i, s i, f x ∂μ = ∑ i, ∫ x in s i, f x ∂μ := by
  convert! integral_biUnion_finset Finset.univ (fun i _ => hs i) _ fun i _ => hf i
  · simp
  · simp [pairwise_univ, h's]
/-
**MeasureTheory.setIntegral_empty** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_empty : ∫ x in ∅, f x ∂μ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_empty`：restrict_empty : μ.restrict ∅ = 0
· 使用定理 `MeasureTheory.integral_zero_measure`：integral_zero_measure {m : Measurab
leSpace α} (f : α -> G) : (∫ x, f x ∂(0 : Measure α)) = 0
-/
theorem setIntegral_empty : ∫ x in ∅, f x ∂μ = 0 := by
  rw [Measure.restrict_empty, integral_zero_measure]
/-
**MeasureTheory.setIntegral_univ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_univ : ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
-/
theorem setIntegral_univ : ∫ x in univ, f x ∂μ = ∫ x, f x ∂μ := by rw [Measure.restrict_univ]
/-
**MeasureTheory.integral_eq_setIntegral** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory
`。
形式化陈述：integral_eq_setIntegral (hs : forallᵐ x ∂μ, x in s) (f : X -> E) : ∫ x, f 
x ∂μ = ∫ x in s, f x ∂μ
参数：hs : forallᵐ x ∂μ, x in s；f : X -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `MeasureTheory.ae_eq_univ`：ae_eq_univ : s =ᵐ[μ] (univ : Set α) ↔ μ sᶜ = 0
-/
lemma integral_eq_setIntegral (hs : ∀ᵐ x ∂μ, x ∈ s) (f : X → E) :
    ∫ x, f x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← setIntegral_univ, ← setIntegral_congr_set]; rwa [ae_eq_univ]
/-
**MeasureTheory.integral_add_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_add_compl (hs : MeasurableSet s) (hfi : Integrable f μ) : ∫ x in 
s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
参数：hs : MeasurableSet s；hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_add_compl₀`：integral_add_compl₀ (hs : NullMeasura
bleSet s μ) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x,
 f x ∂μ
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem integral_add_compl₀ (hs : NullMeasurableSet s μ) (hfi : Integrable f μ) :
    ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ := by
  have := setIntegral_union₀ disjoint_compl_right.aedisjoint
    hs.compl hfi.integrableOn hfi.integrableOn
  rw [← this, union_compl_self, setIntegral_univ]
/-
**MeasureTheory.integral_add_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_add_compl (hs : MeasurableSet s) (hfi : Integrable f μ) : ∫ x in 
s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
参数：hs : MeasurableSet s；hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_add_compl₀`：integral_add_compl₀ (hs : NullMeasura
bleSet s μ) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x,
 f x ∂μ
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem integral_add_compl (hs : MeasurableSet s) (hfi : Integrable f μ) :
    ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ :=
  integral_add_compl₀ hs.nullMeasurableSet hfi
/-
**MeasureTheory.setIntegral_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_compl (hs : MeasurableSet s) (hfi : Integrable f μ) : ∫ x in s
ᶜ, f x ∂μ = ∫ x, f x ∂μ - ∫ x in s, f x ∂μ
参数：hs : MeasurableSet s；hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_compl₀`：setIntegral_compl₀ (hs : NullMeasurabl
eSet s μ) (hfi : Integrable f μ) : ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ - ∫ x in s, f
 x ∂μ
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem setIntegral_compl₀ (hs : NullMeasurableSet s μ) (hfi : Integrable f μ) :
    ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ - ∫ x in s, f x ∂μ := by
  rw [← integral_add_compl₀ (μ := μ) hs hfi, add_sub_cancel_left]
/-
**MeasureTheory.setIntegral_compl** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_compl (hs : MeasurableSet s) (hfi : Integrable f μ) : ∫ x in s
ᶜ, f x ∂μ = ∫ x, f x ∂μ - ∫ x in s, f x ∂μ
参数：hs : MeasurableSet s；hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_compl₀`：setIntegral_compl₀ (hs : NullMeasurabl
eSet s μ) (hfi : Integrable f μ) : ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ - ∫ x in s, f
 x ∂μ
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem setIntegral_compl (hs : MeasurableSet s) (hfi : Integrable f μ) :
    ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ - ∫ x in s, f x ∂μ :=
  setIntegral_compl₀ hs.nullMeasurableSet hfi

/-- For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ x in s, f x ∂μ` defined as `∫ x, f x ∂(μ.restrict s)`. -/
/-
**MeasureTheory.integral_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_indicator (hs : MeasurableSet s) : ∫ x, indicator s f x ∂μ = ∫ x 
in s, f x ∂μ
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add_compl`：integral_add_compl (hs : MeasurableSet
 s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.IntegrableOn.integrable_indicator`：∀ {α : Type u_1} {ε' : 
Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [
inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `indicator_ae_eq_restrict`：indicator_ae_eq_restrict (hs : MeasurableSet s
) : indicator s f =ᵐ[μ.restrict s] f
· 使用定理 `indicator_ae_eq_restrict_compl`：indicator_ae_eq_restrict_compl (hs : Mea
surableSet s) : indicator s f =ᵐ[μ.restrict sᶜ] 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ

--- 原说明 ---
For a function `f` and a measurable set `s`, the integral of `indicator s f`
over the whole space is equal to `∫ x in s, f x ∂μ` defined as `∫ x, f x ∂(μ.res
trict s)`.
-/
theorem integral_indicator (hs : MeasurableSet s) :
    ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ := by
  by_cases hfi : IntegrableOn f s μ; swap
  · rw [integral_undef hfi, integral_undef]
    rwa [integrable_indicator_iff hs]
  calc
    ∫ x, indicator s f x ∂μ = ∫ x in s, indicator s f x ∂μ + ∫ x in sᶜ, indicator s f x ∂μ :=
      (integral_add_compl hs (hfi.integrable_indicator hs)).symm
    _ = ∫ x in s, f x ∂μ + ∫ x in sᶜ, 0 ∂μ :=
      (congr_arg₂ (· + ·) (integral_congr_ae (indicator_ae_eq_restrict hs))
        (integral_congr_ae (indicator_ae_eq_restrict_compl hs)))
    _ = ∫ x in s, f x ∂μ := by simp
/-
**MeasureTheory.integral_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_indicator (hs : MeasurableSet s) : ∫ x, indicator s f x ∂μ = ∫ x 
in s, f x ∂μ
参数：hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add_compl`：integral_add_compl (hs : MeasurableSet
 s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.IntegrableOn.integrable_indicator`：∀ {α : Type u_1} {ε' : 
Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [
inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `indicator_ae_eq_restrict`：indicator_ae_eq_restrict (hs : MeasurableSet s
) : indicator s f =ᵐ[μ.restrict s] f
· 使用定理 `indicator_ae_eq_restrict_compl`：indicator_ae_eq_restrict_compl (hs : Mea
surableSet s) : indicator s f =ᵐ[μ.restrict sᶜ] 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_zero`：integral_zero : ∫ _ : α, (0 : G) ∂μ = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
-/
theorem integral_indicator₀ (hs : NullMeasurableSet s μ) :
    ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ := by
  rw [← integral_congr_ae (indicator_ae_eq_of_ae_eq_set hs.toMeasurable_ae_eq),
    integral_indicator (measurableSet_toMeasurable _ _),
    Measure.restrict_congr_set hs.toMeasurable_ae_eq]
/-
**MeasureTheory.integral_integral_indicator** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTh
eory`。
形式化陈述：integral_integral_indicator {mY : MeasurableSpace Y} {ν : Measure Y} (f : 
X -> Y -> E) {s : Set X} (hs : MeasurableSet s) : ∫ x, ∫ y, s.indicator (f · y) 
x ∂ν ∂μ = ∫ x in s, ∫ y, f x y ∂ν ∂μ
参数：f : X -> Y -> E；hs : MeasurableSet s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `MeasureTheory.integral_indicator₂`：integral_indicator₂ {β : Type*} (f : 
β -> α -> G) (s : Set β) (b : β) : ∫ y, s.indicator (f · y) b ∂μ = s.indicator (
fun x => ∫ y, f x y ∂μ)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma integral_integral_indicator {mY : MeasurableSpace Y} {ν : Measure Y} (f : X → Y → E)
    {s : Set X} (hs : MeasurableSet s) :
    ∫ x, ∫ y, s.indicator (f · y) x ∂ν ∂μ = ∫ x in s, ∫ y, f x y ∂ν ∂μ := by
  simp_rw [← integral_indicator hs, integral_indicator₂]
/-
**MeasureTheory.setIntegral_indicator** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_indicator (ht : MeasurableSet t) : ∫ x in s, t.indicator f x ∂
μ = ∫ x in s inter t, f x ∂μ
参数：ht : MeasurableSet t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem setIntegral_indicator (ht : MeasurableSet t) :
    ∫ x in s, t.indicator f x ∂μ = ∫ x in s ∩ t, f x ∂μ := by
  rw [integral_indicator ht, Measure.restrict_restrict ht, Set.inter_comm]

/-- **Inclusion-exclusion principle** for the integral of a function over a union.

The integral of a function `f` over the union of the `s i` over `i ∈ t` is the alternating sum of
the integrals of `f` over the intersections of the `s i`. -/
/-
**MeasureTheory.integral_biUnion_eq_sum_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：integral_biUnion_eq_sum_powerset {ι : Type*} {t : Finset ι} {s : ι -> Set 
X} (hs : forall i in t, MeasurableSet (s i)) (hf : forall i in t, IntegrableOn f
 (s i) μ) : ∫ x in ⋃ i in t, s i, f x ∂μ = ∑ u in t.powerset with u.Nonempty, (-
1 : Real) ^ (#u + 1) • ∫ x in ⋂ i in u, s i, f x ∂μ
参数：hs : forall i in t, MeasurableSet (s i)；hf : forall i in t, IntegrableOn f (s
 i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `Finset.measurableSet_biUnion`：Finset.measurableSet_biUnion {f : β -> Set
 α} (s : Finset β) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋃ b
 in s, f b)
· 使用定理 `Finset.measurableSet_biInter`：Finset.measurableSet_biInter {f : β -> Set
 α} (s : Finset β) (h : forall b in s, MeasurableSet (f b)) : MeasurableSet (⋂ b
 in s, f b)
· 使用定理 `MeasureTheory.integral_finsetSum`：integral_finsetSum {ι} (s : Finset ι) 
{f : ι -> α -> G} (hf : forall i in s, Integrable (f i) μ) : ∫ a, ∑ i in s, f i 
a ∂μ = ∑ i in s, ∫ a, …
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.biInter_subset_of_mem`：biInter_subset_of_mem {s : Set α} {t : α -> S
et β} {x : α} (xs : x in s) : ⋂ x in s, t x subseteq t x
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Set.indicator_smul_apply`：indicator_smul_apply (s : Set α) (r : α -> R) 
(f : α -> M) (a : α) : indicator s (fun a => r a • f a) a = r a • indicator s f 
a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用引理 `Finset.indicator_biUnion_eq_sum_powerset`：indicator_biUnion_eq_sum_power
set (s : Finset ι) (S : ι -> Set α) (f : α -> G) (a : α) : Set.indicator (⋃ i in
 s, S i) f a = ∑ t in s.powers…

--- 原说明 ---
**Inclusion-exclusion principle** for the integral of a function over a union.

The integral of a function `f` over the union of the `s i` over `i ∈ t` is the a
lternating sum of
the integrals of `f` over the intersections of the `s i`.
-/
theorem integral_biUnion_eq_sum_powerset {ι : Type*} {t : Finset ι} {s : ι → Set X}
    (hs : ∀ i ∈ t, MeasurableSet (s i)) (hf : ∀ i ∈ t, IntegrableOn f (s i) μ) :
    ∫ x in ⋃ i ∈ t, s i, f x ∂μ = ∑ u ∈ t.powerset with u.Nonempty,
      (-1 : ℝ) ^ (#u + 1) • ∫ x in ⋂ i ∈ u, s i, f x ∂μ := by
  simp_rw [← integral_smul, ← integral_indicator (Finset.measurableSet_biUnion _ hs)]
  have A (u) (hu : u ∈ t.powerset.filter (·.Nonempty)) : MeasurableSet (⋂ i ∈ u, s i) := by
    refine u.measurableSet_biInter fun i hi ↦ hs i ?_
    grind
  have : ∑ x ∈ t.powerset with x.Nonempty, ∫ (a : X) in ⋂ i ∈ x, s i, (-1 : ℝ) ^ (#x + 1) • f a ∂μ
      = ∑ x ∈ t.powerset with x.Nonempty, ∫ a, indicator (⋂ i ∈ x, s i)
        (fun a ↦ (-1 : ℝ) ^ (#x + 1) • f a) a ∂μ := by
    apply Finset.sum_congr rfl (fun x hx ↦ ?_)
    rw [← integral_indicator (A x hx)]
  rw [this, ← integral_finsetSum]; swap
  · intro u hu
    rw [integrable_indicator_iff (A u hu)]
    apply Integrable.smul
    simp only [Finset.mem_filter, Finset.mem_powerset] at hu
    rcases hu.2 with ⟨i, hi⟩
    exact (hf i (hu.1 hi)).mono (biInter_subset_of_mem hi) le_rfl
  congr with x
  convert! Finset.indicator_biUnion_eq_sum_powerset t s f x with u hu
  rw [indicator_smul_apply]
  norm_cast
/-
**MeasureTheory.ofReal_setIntegral_one_of_measure_ne_top** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：ofReal_setIntegral_one_of_measure_ne_top {X : Type*} {m : MeasurableSpace 
X} {μ : Measure X} {s : Set X} (hs : μ s != ∞
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ENNReal.ofReal_toReal`：ofReal_toReal {a : Real>=0∞} (h : a != ∞) : ENNRe
al.ofReal a.toReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MeasureTheory.setLIntegral_one`：setLIntegral_one (s) : ∫⁻ _ in s, 1 ∂μ =
 μ s
-/
theorem ofReal_setIntegral_one_of_measure_ne_top {X : Type*} {m : MeasurableSpace X}
    {μ : Measure X} {s : Set X} (hs : μ s ≠ ∞ := by finiteness) :
    ENNReal.ofReal (∫ _ in s, (1 : ℝ) ∂μ) = μ s :=
  calc
    ENNReal.ofReal (∫ _ in s, (1 : ℝ) ∂μ) = ENNReal.ofReal (∫ _ in s, ‖(1 : ℝ)‖ ∂μ) := by
      simp only [norm_one]
    _ = ∫⁻ _ in s, 1 ∂μ := by simp [measureReal_def, hs]
    _ = μ s := setLIntegral_one _
/-
**MeasureTheory.ofReal_setIntegral_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：ofReal_setIntegral_one {X : Type*} {_ : MeasurableSpace X} (μ : Measure X)
 [IsFiniteMeasure μ] (s : Set X) : ENNReal.ofReal (∫ _ in s, (1 : Real) ∂μ) = μ 
s
参数：μ : Measure X；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ofReal_setIntegral_one_of_measure_ne_top`：ofReal_setIntegr
al_one_of_measure_ne_top {X : Type*} {m : MeasurableSpace X} {μ : Measure X} {s 
: Set X} (hs : μ s != ∞
· 使用定理 `MeasureTheory.measure_ne_top`：measure_ne_top (μ : Measure α) [IsFiniteMe
asure μ] (s : Set α) : μ s != ∞
-/
theorem ofReal_setIntegral_one {X : Type*} {_ : MeasurableSpace X} (μ : Measure X)
    [IsFiniteMeasure μ] (s : Set X) : ENNReal.ofReal (∫ _ in s, (1 : ℝ) ∂μ) = μ s :=
  ofReal_setIntegral_one_of_measure_ne_top
/-
**MeasureTheory.setIntegral_one_eq_measureReal** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：setIntegral_one_eq_measureReal {X : Type*} {m : MeasurableSpace X} {μ : Me
asure X} {s : Set X} : ∫ _ in s, (1 : Real) ∂μ = μ.real s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem setIntegral_one_eq_measureReal {X : Type*} {m : MeasurableSpace X}
    {μ : Measure X} {s : Set X} :
    ∫ _ in s, (1 : ℝ) ∂μ = μ.real s := by simp

/-- **Inclusion-exclusion principle** for the measure of a union of sets of finite measure.

The measure of the union of the `s i` over `i ∈ t` is the alternating sum of the measures of the
intersections of the `s i`. -/
/-
**MeasureTheory.measureReal_biUnion_eq_sum_powerset** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory`。
形式化陈述：measureReal_biUnion_eq_sum_powerset {ι : Type*} {t : Finset ι} {s : ι -> S
et X} (hs : forall i in t, MeasurableSet (s i)) (hf : forall i in t, μ (s i) != 
∞
参数：hs : forall i in t, MeasurableSet (s i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MeasureTheory.integral_biUnion_eq_sum_powerset`：integral_biUnion_eq_sum_
powerset {ι : Type*} {t : Finset ι} {s : ι -> Set X} (hs : forall i in t, Measur
ableSet (s i)) (hf : forall i in t, …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `enorm_one`：∀ {G : Type u_1} [inst : SeminormedAddCommGroup G] [inst_1 : 
One G] [NormOneClass G], ‖1‖ₑ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ENNReal.instCharZero`：CharZero ENNReal
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤

--- 原说明 ---
**Inclusion-exclusion principle** for the measure of a union of sets of finite m
easure.

The measure of the union of the `s i` over `i ∈ t` is the alternating sum of the
 measures of the
intersections of the `s i`.
-/
theorem measureReal_biUnion_eq_sum_powerset {ι : Type*} {t : Finset ι} {s : ι → Set X}
    (hs : ∀ i ∈ t, MeasurableSet (s i)) (hf : ∀ i ∈ t, μ (s i) ≠ ∞ := by finiteness) :
    μ.real (⋃ i ∈ t, s i) = ∑ u ∈ t.powerset with u.Nonempty,
      (-1 : ℝ) ^ (#u + 1) * μ.real (⋂ i ∈ u, s i) := by
  simp_rw [← setIntegral_one_eq_measureReal]
  apply integral_biUnion_eq_sum_powerset hs
  intro i hi
  simpa using (hf i hi).lt_top
/-
**MeasureTheory.integral_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_piecewise [DecidablePred (· in s)] (hs : MeasurableSet s) (hf : I
ntegrableOn f s μ) (hg : IntegrableOn g sᶜ μ) : ∫ x, s.piecewise f g x ∂μ = ∫ x 
in s, f x ∂μ + ∫ x in sᶜ, g x ∂μ
参数：· in s；hs : MeasurableSet s；hf : IntegrableOn f s μ；hg : IntegrableOn g sᶜ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.indicator_add_compl_eq_piecewise`：∀ {α : Type u_1} {M : Type u_4} [i
nst : AddZeroClass M] {s : Set α} [inst_1 : DecidablePred fun x => x ∈ s]   (f g
 : α → M), s.indicator f +…
· 使用定理 `MeasureTheory.integral_add'`：integral_add' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f + g) a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.IntegrableOn.integrable_indicator`：∀ {α : Type u_1} {ε' : 
Type u_4} {mα : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [
inst : TopologicalSpace ε'] [inst_1 :…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
-/
theorem integral_piecewise [DecidablePred (· ∈ s)] (hs : MeasurableSet s) (hf : IntegrableOn f s μ)
    (hg : IntegrableOn g sᶜ μ) :
    ∫ x, s.piecewise f g x ∂μ = ∫ x in s, f x ∂μ + ∫ x in sᶜ, g x ∂μ := by
  rw [← Set.indicator_add_compl_eq_piecewise,
    integral_add' (hf.integrable_indicator hs) (hg.integrable_indicator hs.compl),
    integral_indicator hs, integral_indicator hs.compl]
/-
**MeasureTheory.tendsto_setIntegral_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：tendsto_setIntegral_of_monotone {ι : Type*} [Preorder ι] [(atTop : Filter 
ι).IsCountablyGenerated] {s : ι -> Set X} (hsm : forall i, MeasurableSet (s i)) 
(h_mono : Monotone s) (hfi : IntegrableOn f (⋃ n, s n) μ) : Tendsto (fun i => ∫ 
x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋃ n, s n, f x ∂μ))
参数：atTop : Filter ι；hsm : forall i, MeasurableSet (s i)；h_mono : Monotone s；hfi 
: IntegrableOn f (⋃ n, s n) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_setIntegral_of_monotone₀`：tendsto_setIntegral_of_m
onotone₀ {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] {s :
 ι -> Set X} (hsm : forall i, NullMe…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem tendsto_setIntegral_of_monotone₀
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated]
    {s : ι → Set X} (hsm : ∀ i, NullMeasurableSet (s i) μ) (h_mono : Monotone s)
    (hfi : IntegrableOn f (⋃ n, s n) μ) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋃ n, s n, f x ∂μ)) := by
  refine .of_neBot_imp fun hne ↦ ?_
  have := (atTop_neBot_iff.mp hne).2
  have hfi' : ∫⁻ x in ⋃ n, s n, ‖f x‖₊ ∂μ < ∞ := hfi.2
  set S := ⋃ i, s i
  have hSm : NullMeasurableSet S μ := MeasurableSet.iUnion_of_monotone h_mono hsm
  have hsub {i} : s i ⊆ S := subset_iUnion s i
  rw [← withDensity_apply₀ _ hSm] at hfi'
  set ν := μ.withDensity (‖f ·‖ₑ) with hν
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.2 fun ε ε0 => ?_
  lift ε to ℝ≥0 using ε0.le
  have : ∀ᶠ i in atTop, ν (s i) ∈ Icc (ν S - ε) (ν S + ε) :=
    tendsto_measure_iUnion_atTop h_mono (ENNReal.Icc_mem_nhds hfi'.ne (ENNReal.coe_pos.2 ε0).ne')
  filter_upwards [this] with i hi
  rw [mem_closedBall_iff_norm', ← setIntegral_sdiff₀ (hsm i) hfi hsub, ← coe_nnnorm,
    NNReal.coe_le_coe, ← ENNReal.coe_le_coe]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hsm' : NullMeasurableSet (s i) ν := (hsm i).mono_ac (withDensity_absolutelyContinuous ..)
  rw [← withDensity_apply₀ _ (hSm.diff (hsm _)), ← hν, measure_sdiff hsub hsm']
  exacts [tsub_le_iff_tsub_le.mp hi.1,
    (hi.2.trans_lt <| ENNReal.add_lt_top.2 ⟨hfi', ENNReal.coe_lt_top⟩).ne]
/-
**MeasureTheory.tendsto_setIntegral_of_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：tendsto_setIntegral_of_monotone {ι : Type*} [Preorder ι] [(atTop : Filter 
ι).IsCountablyGenerated] {s : ι -> Set X} (hsm : forall i, MeasurableSet (s i)) 
(h_mono : Monotone s) (hfi : IntegrableOn f (⋃ n, s n) μ) : Tendsto (fun i => ∫ 
x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋃ n, s n, f x ∂μ))
参数：atTop : Filter ι；hsm : forall i, MeasurableSet (s i)；h_mono : Monotone s；hfi 
: IntegrableOn f (⋃ n, s n) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.tendsto_setIntegral_of_monotone₀`：tendsto_setIntegral_of_m
onotone₀ {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] {s :
 ι -> Set X} (hsm : forall i, NullMe…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem tendsto_setIntegral_of_monotone
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated]
    {s : ι → Set X} (hsm : ∀ i, MeasurableSet (s i)) (h_mono : Monotone s)
    (hfi : IntegrableOn f (⋃ n, s n) μ) :
    Tendsto (fun i => ∫ x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋃ n, s n, f x ∂μ)) :=
  tendsto_setIntegral_of_monotone₀ (hsm · |>.nullMeasurableSet) h_mono hfi
/-
**MeasureTheory.tendsto_setIntegral_of_antitone** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：tendsto_setIntegral_of_antitone {ι : Type*} [Preorder ι] [(atTop : Filter 
ι).IsCountablyGenerated] {s : ι -> Set X} (hsm : forall i, MeasurableSet (s i)) 
(h_anti : Antitone s) (hfi : exists i, IntegrableOn f (s i) μ) : Tendsto (fun i 
=> ∫ x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋂ n, s n, f x ∂μ))
参数：atTop : Filter ι；hsm : forall i, MeasurableSet (s i)；h_anti : Antitone s；hfi 
: exists i, IntegrableOn f (s i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.of_neBot_imp`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}
 {la : Filter α} {lb : Filter β},   (la.NeBot → Filter.Tendsto f la lb) → Filter
.Tendsto f la lb
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.atTop_neBot_iff`：atTop_neBot_iff {α : Type*} [Preorder α] : (atTo
p : Filter α).NeBot ↔ Nonempty α ∧ IsDirectedOrder α
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `MeasureTheory.tendsto_setIntegral_of_monotone`：tendsto_setIntegral_of_mo
notone {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] {s : ι
 -> Set X} (hsm : forall i, Measura…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.sdiff_subset_sdiff_right`：sdiff_subset_sdiff_right {s t u : Set α} (
h : t subseteq u) : s \ u subseteq s \ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_iInter`：sdiff_iInter (s : Set β) (t : ι -> Set β) : (s \ ⋂ i, 
t i) = ⋃ i, s \ t i
· 使用定理 `MeasureTheory.IntegrableOn.mono_set`：∀ {α : Type u_1} {ε : Type u_3} {mα
 : MeasurableSpace α} {f : α → ε} {s t : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace …
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.setIntegral_sdiff`：setIntegral_sdiff (ht : MeasurableSet t
) (hfs : IntegrableOn f s μ) (hts : t subseteq s) : ∫ x in s \ t, f x ∂μ = ∫ x i
n s, f x ∂μ - ∫ x in …
· 使用定理 `MeasurableSet.iInter_of_antitone`：∀ {α : Type u_1} [inst : MeasurableSpa
ce α] {ι : Type u_5} [inst_1 : Preorder ι] [IsDirectedOrder ι]   [Filter.atTop.I
sCountablyGenerated] {…
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
-/
theorem tendsto_setIntegral_of_antitone
    {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated]
    {s : ι → Set X} (hsm : ∀ i, MeasurableSet (s i)) (h_anti : Antitone s)
    (hfi : ∃ i, IntegrableOn f (s i) μ) :
    Tendsto (fun i ↦ ∫ x in s i, f x ∂μ) atTop (𝓝 (∫ x in ⋂ n, s n, f x ∂μ)) := by
  refine .of_neBot_imp fun hne ↦ ?_
  have := (atTop_neBot_iff.mp hne).2
  rcases hfi with ⟨i₀, hi₀⟩
  suffices Tendsto (∫ x in s i₀, f x ∂μ - ∫ x in s i₀ \ s ·, f x ∂μ) atTop
      (𝓝 (∫ x in s i₀, f x ∂μ - ∫ x in ⋃ i, s i₀ \ s i, f x ∂μ)) by
    convert! this.congr' <| (eventually_ge_atTop i₀).mono fun i hi ↦ ?_
    · rw [← sdiff_iInter, setIntegral_sdiff _ hi₀ (iInter_subset _ _), sub_sub_cancel]
      exact .iInter_of_antitone h_anti hsm
    · rw [setIntegral_sdiff (hsm i) hi₀ (h_anti hi), sub_sub_cancel]
  apply tendsto_const_nhds.sub
  refine tendsto_setIntegral_of_monotone (by measurability) ?_ ?_
  · exact fun i j h ↦ sdiff_subset_sdiff_right (h_anti h)
  · rw [← sdiff_iInter]
    exact hi₀.mono_set sdiff_subset
/-
**MeasureTheory.hasSum_integral_iUnion_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：hasSum_integral_iUnion_ae {ι : Type*} [Countable ι] {s : ι -> Set X} (hm :
 forall i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s)) (hfi :
 IntegrableOn f (⋃ i, s i) μ) : HasSum (fun n => ∫ x in s n, f x ∂μ) (∫ x in ⋃ n
, s n, f x ∂μ)
参数：hm : forall i, NullMeasurableSet (s i) μ；hd : Pairwise (AEDisjoint μ on s)；hf
i : IntegrableOn f (⋃ i, s i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_iUnion_ae`：restrict_iUnion_ae [Countable 
ι] {s : ι -> Set α} (hd : Pairwise (AEDisjoint μ on s)) (hm : forall i, NullMeas
urableSet (s i) μ) : μ.restric…
· 使用定理 `MeasureTheory.hasSum_integral_measure`：hasSum_integral_measure (hf : Int
egrable f (Measure.sum μ)) : HasSum (fun i => ∫ x, f x ∂μ i) (∫ x, f x ∂Measure.
sum μ)
-/
theorem hasSum_integral_iUnion_ae {ι : Type*} [Countable ι] {s : ι → Set X}
    (hm : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) :
    HasSum (fun n => ∫ x in s n, f x ∂μ) (∫ x in ⋃ n, s n, f x ∂μ) := by
  simp only [IntegrableOn, Measure.restrict_iUnion_ae hd hm] at hfi ⊢
  exact hasSum_integral_measure hfi
/-
**MeasureTheory.hasSum_integral_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：hasSum_integral_iUnion {ι : Type*} [Countable ι] {s : ι -> Set X} (hm : fo
rall i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s)) (hfi : IntegrableOn
 f (⋃ i, s i) μ) : HasSum (fun n => ∫ x in s n, f x ∂μ) (∫ x in ⋃ n, s n, f x ∂μ
)
参数：hm : forall i, MeasurableSet (s i)；hd : Pairwise (Disjoint on s)；hfi : Integr
ableOn f (⋃ i, s i) μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.hasSum_integral_iUnion_ae`：hasSum_integral_iUnion_ae {ι : 
Type*} [Countable ι] {s : ι -> Set X} (hm : forall i, NullMeasurableSet (s i) μ)
 (hd : Pairwise (AEDisjoint μ…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `Disjoint.aedisjoint`：∀ {α : Type u_2} {m : MeasurableSpace α} {μ : Measu
reTheory.Measure α} {s t : Set α},   Disjoint s t → MeasureTheory.AEDisjoint μ s
 t
-/
theorem hasSum_integral_iUnion {ι : Type*} [Countable ι] {s : ι → Set X}
    (hm : ∀ i, MeasurableSet (s i)) (hd : Pairwise (Disjoint on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) :
    HasSum (fun n => ∫ x in s n, f x ∂μ) (∫ x in ⋃ n, s n, f x ∂μ) :=
  hasSum_integral_iUnion_ae (fun i => (hm i).nullMeasurableSet) (hd.mono fun _ _ h => h.aedisjoint)
    hfi
/-
**MeasureTheory.integral_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_iUnion {ι : Type*} [Countable ι] {s : ι -> Set X} (hm : forall i,
 MeasurableSet (s i)) (hd : Pairwise (Disjoint on s)) (hfi : IntegrableOn f (⋃ i
, s i) μ) : ∫ x in ⋃ n, s n, f x ∂μ = ∑' n, ∫ x in s n, f x ∂μ
参数：hm : forall i, MeasurableSet (s i)；hd : Pairwise (Disjoint on s)；hfi : Integr
ableOn f (⋃ i, s i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.hasSum_integral_iUnion`：hasSum_integral_iUnion {ι : Type*}
 [Countable ι] {s : ι -> Set X} (hm : forall i, MeasurableSet (s i)) (hd : Pairw
ise (Disjoint on s)) (hfi …
-/
theorem integral_iUnion {ι : Type*} [Countable ι] {s : ι → Set X} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s)) (hfi : IntegrableOn f (⋃ i, s i) μ) :
    ∫ x in ⋃ n, s n, f x ∂μ = ∑' n, ∫ x in s n, f x ∂μ :=
  (HasSum.tsum_eq (hasSum_integral_iUnion hm hd hfi)).symm
/-
**MeasureTheory.integral_iUnion_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_iUnion_ae {ι : Type*} [Countable ι] {s : ι -> Set X} (hm : forall
 i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s)) (hfi : Integr
ableOn f (⋃ i, s i) μ) : ∫ x in ⋃ n, s n, f x ∂μ = ∑' n, ∫ x in s n, f x ∂μ
参数：hm : forall i, NullMeasurableSet (s i) μ；hd : Pairwise (AEDisjoint μ on s)；hf
i : IntegrableOn f (⋃ i, s i) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `MeasureTheory.hasSum_integral_iUnion_ae`：hasSum_integral_iUnion_ae {ι : 
Type*} [Countable ι] {s : ι -> Set X} (hm : forall i, NullMeasurableSet (s i) μ)
 (hd : Pairwise (AEDisjoint μ…
-/
theorem integral_iUnion_ae {ι : Type*} [Countable ι] {s : ι → Set X}
    (hm : ∀ i, NullMeasurableSet (s i) μ) (hd : Pairwise (AEDisjoint μ on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) : ∫ x in ⋃ n, s n, f x ∂μ = ∑' n, ∫ x in s n, f x ∂μ :=
  (HasSum.tsum_eq (hasSum_integral_iUnion_ae hm hd hfi)).symm
/-
**MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：setIntegral_eq_zero_of_ae_eq_zero (ht_eq : forallᵐ x ∂μ, x in t -> f x = 0
) : ∫ x in t, f x ∂μ = 0
参数：ht_eq : forallᵐ x ∂μ, x in t -> f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_eq_zero_of_ae`：integral_eq_zero_of_ae {f : α -> G
} (hf : f =ᵐ[μ] 0) : ∫ a, f a ∂μ = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_restrict_iff`：ae_restrict_iff {p : α -> Prop} (hp : Mea
surableSet { x | p x }) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s 
-> p x
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_eq_fun`：measurableSet_eq_
fun (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSe
t[m] {a | f a = g a}
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.stronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2} {
x : MeasurableSpace α} [inst : TopologicalSpace β] [inst_1 : Zero β],   MeasureT
heory.StronglyMeasurable 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem setIntegral_eq_zero_of_ae_eq_zero (ht_eq : ∀ᵐ x ∂μ, x ∈ t → f x = 0) :
    ∫ x in t, f x ∂μ = 0 := by
  by_cases hf : AEStronglyMeasurable f (μ.restrict t); swap
  · rw [integral_undef]
    contrapose hf
    exact hf.1
  have : ∫ x in t, hf.mk f x ∂μ = 0 := by
    refine integral_eq_zero_of_ae ?_
    rw [EventuallyEq,
      ae_restrict_iff (hf.stronglyMeasurable_mk.measurableSet_eq_fun stronglyMeasurable_zero)]
    filter_upwards [ae_imp_of_ae_restrict hf.ae_eq_mk, ht_eq] with x hx h'x h''x
    rw [← hx h''x]
    exact h'x h''x
  rw [← this]
  exact integral_congr_ae hf.ae_eq_mk
/-
**MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：setIntegral_eq_zero_of_forall_eq_zero (ht_eq : forall x in t, f x = 0) : ∫
 x in t, f x ∂μ = 0
参数：ht_eq : forall x in t, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero`：setIntegral_eq_zero_of_
ae_eq_zero (ht_eq : forallᵐ x ∂μ, x in t -> f x = 0) : ∫ x in t, f x ∂μ = 0
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem setIntegral_eq_zero_of_forall_eq_zero (ht_eq : ∀ x ∈ t, f x = 0) :
    ∫ x in t, f x ∂μ = 0 :=
  setIntegral_eq_zero_of_ae_eq_zero (Eventually.of_forall ht_eq)
/-
**MeasureTheory.frequently_ae_ne_zero_of_setIntegral_ne_zero** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：frequently_ae_ne_zero_of_setIntegral_ne_zero (hU : ∫ x in t, f x ∂μ != 0) 
: existsᶠ x in ae (μ.restrict t), f x != 0
参数：hU : ∫ x in t, f x ∂μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.frequently_ae_ne_zero_of_integral_ne_zero`：frequently_ae_n
e_zero_of_integral_ne_zero {f : α -> G} (h : ∫ a, f a ∂μ != 0) : existsᶠ a in ae
 μ, f a != 0
-/
theorem frequently_ae_ne_zero_of_setIntegral_ne_zero (hU : ∫ x in t, f x ∂μ ≠ 0) :
    ∃ᶠ x in ae (μ.restrict t), f x ≠ 0 :=
  frequently_ae_ne_zero_of_integral_ne_zero hU
/-
**MeasureTheory.exists_ne_zero_of_setIntegral_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：exists_ne_zero_of_setIntegral_ne_zero (hU : ∫ x in t, f x ∂μ != 0) : exist
s x, x in t ∧ f x != 0
参数：hU : ∫ x in t, f x ∂μ != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero`：setIntegral_eq_zero
_of_forall_eq_zero (ht_eq : forall x in t, f x = 0) : ∫ x in t, f x ∂μ = 0
-/
theorem exists_ne_zero_of_setIntegral_ne_zero (hU : ∫ x in t, f x ∂μ ≠ 0) :
    ∃ x, x ∈ t ∧ f x ≠ 0 := by
  contrapose! hU; exact setIntegral_eq_zero_of_forall_eq_zero hU
/-
**MeasureTheory.integral_union_eq_left_of_ae_aux** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：integral_union_eq_left_of_ae_aux (ht_eq : forallᵐ x ∂μ.restrict t, f x = 0
) (haux : StronglyMeasurable f) (H : IntegrableOn f (s union t) μ) : ∫ x in s un
ion t, f x ∂μ = ∫ x in s, f x ∂μ
参数：ht_eq : forallᵐ x ∂μ.restrict t, f x = 0；haux : StronglyMeasurable f；H : Inte
grableOn f (s union t) μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero`：setIntegral_eq_zero
_of_forall_eq_zero (ht_eq : forall x in t, f x = 0) : ∫ x in t, f x ∂μ = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_inter_add_sdiff`：integral_inter_add_sdiff (ht : M
easurableSet t) (hfs : IntegrableOn f s μ) : ∫ x in s inter t, f x ∂μ + ∫ x in s
 \ t, f x ∂μ = ∫ x in s, f x…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Set.union_sdiff_distrib`：union_sdiff_distrib {s t u : Set α} : (s union 
t) \ u = s \ u union t \ u
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `MeasureTheory.union_ae_eq_right`：union_ae_eq_right : (s union t : Set α)
 =ᵐ[μ] t ↔ μ (s \ t) = 0
· 使用定理 `MeasureTheory.measure_mono_null`：measure_mono_null (h : s subseteq t) (h
t : μ t = 0) : μ s = 0
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `MeasureTheory.measure_eq_zero_iff_ae_notMem`：measure_eq_zero_iff_ae_notM
em {s : Set α} : μ s = 0 ↔ forallᵐ a ∂μ, a ∉ s
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem integral_union_eq_left_of_ae_aux (ht_eq : ∀ᵐ x ∂μ.restrict t, f x = 0)
    (haux : StronglyMeasurable f) (H : IntegrableOn f (s ∪ t) μ) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ := by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  have h's : IntegrableOn f s μ := H.mono subset_union_left le_rfl
  have A : ∀ u : Set X, ∫ x in u ∩ k, f x ∂μ = 0 := fun u =>
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => hx.2
  rw [← integral_inter_add_sdiff hk h's, ← integral_inter_add_sdiff hk H, A, A, zero_add, zero_add,
    union_sdiff_distrib, union_comm]
  apply setIntegral_congr_set
  rw [union_ae_eq_right]
  apply measure_mono_null sdiff_subset
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_imp_of_ae_restrict ht_eq] with x hx h'x using h'x.2 (hx h'x.1)
/-
**MeasureTheory.integral_union_eq_left_of_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_union_eq_left_of_ae (ht_eq : forallᵐ x ∂μ.restrict t, f x = 0) : 
∫ x in s union t, f x ∂μ = ∫ x in s, f x ∂μ
参数：ht_eq : forallᵐ x ∂μ.restrict t, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.IntegrableOn.congr_fun_ae`：∀ {α : Type u_1} {ε : Type u_3}
 {mα : MeasurableSpace α} {f g : α → ε} {s : Set α} {μ : MeasureTheory.Measure α
}   [inst : TopologicalSpace …
· 使用定理 `MeasureTheory.integrableOn_zero`：integrableOn_zero : IntegrableOn (fun _
 => (0 : ε')) s μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.integral_union_eq_left_of_ae_aux`：integral_union_eq_left_o
f_ae_aux (ht_eq : forallᵐ x ∂μ.restrict t, f x = 0) (haux : StronglyMeasurable f
) (H : IntegrableOn f (s union t) μ)…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_mono`：ae_mono (h : μ <= ν) : ae μ <= ae ν
· 使用定理 `MeasureTheory.Measure.restrict_mono`：restrict_mono {_m0 : MeasurableSpac
e α} ⦃s s' : Set α⦄ (hs : s subseteq s') ⦃μ ν : Measure α⦄ (hμν : μ <= ν) : μ.re
strict s <= ν.restrict s'
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem integral_union_eq_left_of_ae (ht_eq : ∀ᵐ x ∂μ.restrict t, f x = 0) :
    ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ := by
  have ht : IntegrableOn f t μ := by apply integrableOn_zero.congr_fun_ae; symm; exact ht_eq
  by_cases H : IntegrableOn f (s ∪ t) μ; swap
  · rw [integral_undef H, integral_undef]; simpa [integrableOn_union, ht] using! H
  let f' := H.1.mk f
  calc
    ∫ x : X in s ∪ t, f x ∂μ = ∫ x : X in s ∪ t, f' x ∂μ := integral_congr_ae H.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        integral_union_eq_left_of_ae_aux _ H.1.stronglyMeasurable_mk (H.congr_fun_ae H.1.ae_eq_mk)
      filter_upwards [ht_eq,
        ae_mono (Measure.restrict_mono subset_union_right le_rfl) H.1.ae_eq_mk] with x hx h'x
      rw [← h'x, hx]
    _ = ∫ x in s, f x ∂μ :=
      integral_congr_ae
        (ae_mono (Measure.restrict_mono subset_union_left le_rfl) H.1.ae_eq_mk.symm)
/-
**MeasureTheory.integral_union_eq_left_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：integral_union_eq_left_of_forall {f : X -> E} (ht : MeasurableSet t) (ht_e
q : forall x in t, f x = 0) : ∫ x in s union t, f x ∂μ = ∫ x in s, f x ∂μ
参数：ht : MeasurableSet t；ht_eq : forall x in t, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_union_eq_left_of_forall₀`：integral_union_eq_left_
of_forall₀ {f : X -> E} (ht : NullMeasurableSet t μ) (ht_eq : forall x in t, f x
 = 0) : ∫ x in s union t, f x ∂μ = ∫ …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem integral_union_eq_left_of_forall₀ {f : X → E} (ht : NullMeasurableSet t μ)
    (ht_eq : ∀ x ∈ t, f x = 0) : ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_union_eq_left_of_ae ((ae_restrict_iff'₀ ht).2 (Eventually.of_forall ht_eq))
/-
**MeasureTheory.integral_union_eq_left_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：integral_union_eq_left_of_forall {f : X -> E} (ht : MeasurableSet t) (ht_e
q : forall x in t, f x = 0) : ∫ x in s union t, f x ∂μ = ∫ x in s, f x ∂μ
参数：ht : MeasurableSet t；ht_eq : forall x in t, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_union_eq_left_of_forall₀`：integral_union_eq_left_
of_forall₀ {f : X -> E} (ht : NullMeasurableSet t μ) (ht_eq : forall x in t, f x
 = 0) : ∫ x in s union t, f x ∂μ = ∫ …
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
-/
theorem integral_union_eq_left_of_forall {f : X → E} (ht : MeasurableSet t)
    (ht_eq : ∀ x ∈ t, f x = 0) : ∫ x in s ∪ t, f x ∂μ = ∫ x in s, f x ∂μ :=
  integral_union_eq_left_of_forall₀ ht.nullMeasurableSet ht_eq
/-
**MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux (hts : s subseteq t) (h't
 : forallᵐ x ∂μ, x in t \ s -> f x = 0) (haux : StronglyMeasurable f) (h'aux : I
ntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ
参数：hts : s subseteq t；h't : forallᵐ x ∂μ, x in t \ s -> f x = 0；haux : StronglyM
easurable f；h'aux : IntegrableOn f t μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `OpensMeasurableSpace.toMeasurableSingletonClass`：∀ {α : Type u_1} [inst 
: TopologicalSpace α] [inst_1 : MeasurableSpace α] [OpensMeasurableSpace α] [T1S
pace α],   MeasurableSingletonClass α
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_inter_add_sdiff`：integral_inter_add_sdiff (ht : M
easurableSet t) (hfs : IntegrableOn f s μ) : ∫ x in s inter t, f x ∂μ + ∫ x in s
 \ t, f x ∂μ = ∫ x in s, f x…
· 使用定理 `MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero`：setIntegral_eq_zero
_of_forall_eq_zero (ht_eq : forall x in t, f x = 0) : ∫ x in t, f x ∂μ = 0
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `MeasureTheory.IntegrableOn.mono`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} {f : α → ε} {s t : Set α} {μ ν : MeasureTheory.Measure α}   [i
nst : TopologicalSpac…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux (hts : s ⊆ t)
    (h't : ∀ᵐ x ∂μ, x ∈ t \ s → f x = 0) (haux : StronglyMeasurable f)
    (h'aux : IntegrableOn f t μ) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ := by
  let k := f ⁻¹' {0}
  have hk : MeasurableSet k := by borelize E; exact haux.measurable (measurableSet_singleton _)
  calc
    ∫ x in t, f x ∂μ = ∫ x in t ∩ k, f x ∂μ + ∫ x in t \ k, f x ∂μ := by
      rw [integral_inter_add_sdiff hk h'aux]
    _ = ∫ x in t \ k, f x ∂μ := by
      rw [setIntegral_eq_zero_of_forall_eq_zero fun x hx => ?_, zero_add]; exact hx.2
    _ = ∫ x in s \ k, f x ∂μ := by
      apply setIntegral_congr_set
      filter_upwards [h't] with x hx
      change (x ∈ t \ k) = (x ∈ s \ k)
      simp only [eq_iff_iff, and_congr_left_iff, Set.mem_sdiff]
      intro h'x
      by_cases xs : x ∈ s
      · simp only [xs, hts xs]
      · simp only [xs, iff_false]
        intro xt
        exact h'x (hx ⟨xt, xs⟩)
    _ = ∫ x in s ∩ k, f x ∂μ + ∫ x in s \ k, f x ∂μ := by
      have : ∀ x ∈ s ∩ k, f x = 0 := fun x hx => hx.2
      rw [setIntegral_eq_zero_of_forall_eq_zero this, zero_add]
    _ = ∫ x in s, f x ∂μ := by rw [integral_inter_add_sdiff hk (h'aux.mono hts le_rfl)]

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_ae_diff_eq_zero_aux :=
  setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux

/-- If a function vanishes almost everywhere on `t \ s` with `s ⊆ t`, then its integrals on `s`
and `t` coincide if `t` is null-measurable. -/
/-
**MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (ht : NullMeasurableSet t μ) 
(hts : s subseteq t) (h't : forallᵐ x ∂μ, x in t \ s -> f x = 0) : ∫ x in t, f x
 ∂μ = ∫ x in s, f x ∂μ
参数：ht : NullMeasurableSet t μ；hts : s subseteq t；h't : forallᵐ x ∂μ, x in t \ s 
-> f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux`：setInteg
ral_eq_of_subset_of_ae_sdiff_eq_zero_aux (hts : s subseteq t) (h't : forallᵐ x ∂
μ, x in t \ s -> f x = 0) (haux : StronglyMeasurable…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.ae_imp_of_ae_restrict`：ae_imp_of_ae_restrict {s : Set α} {
p : α -> Prop} (h : forallᵐ x ∂μ.restrict s, p x) : forallᵐ x ∂μ, x in s -> p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.ae_restrict_of_ae_restrict_of_subset`：ae_restrict_of_ae_re
strict_of_subset {s t : Set α} {p : α -> Prop} (hst : s subseteq t) (h : forallᵐ
 x ∂μ.restrict t, p x) : forallᵐ x ∂μ.re…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.IntegrableOn.of_ae_sdiff_eq_zero`：∀ {α : Type u_1} {mα : M
easurableSpace α} {s t : Set α} {μ : MeasureTheory.Measure α} {ε' : Type u_7}   
[inst : TopologicalSpace ε'] [inst_1…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0

--- 原说明 ---
If a function vanishes almost everywhere on `t \ s` with `s ⊆ t`, then its integ
rals on `s`
and `t` coincide if `t` is null-measurable.
-/
theorem setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (ht : NullMeasurableSet t μ) (hts : s ⊆ t)
    (h't : ∀ᵐ x ∂μ, x ∈ t \ s → f x = 0) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ := by
  by_cases h : IntegrableOn f t μ; swap
  · have : ¬IntegrableOn f s μ := fun H => h (H.of_ae_sdiff_eq_zero ht h't)
    rw [integral_undef h, integral_undef this]
  let f' := h.1.mk f
  calc
    ∫ x in t, f x ∂μ = ∫ x in t, f' x ∂μ := integral_congr_ae h.1.ae_eq_mk
    _ = ∫ x in s, f' x ∂μ := by
      apply
        setIntegral_eq_of_subset_of_ae_sdiff_eq_zero_aux hts _ h.1.stronglyMeasurable_mk
          (h.congr h.1.ae_eq_mk)
      filter_upwards [h't, ae_imp_of_ae_restrict h.1.ae_eq_mk] with x hx h'x h''x
      rw [← h'x h''x.1, hx h''x]
    _ = ∫ x in s, f x ∂μ := by
      apply integral_congr_ae
      apply ae_restrict_of_ae_restrict_of_subset hts
      exact h.1.ae_eq_mk.symm

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_ae_diff_eq_zero := setIntegral_eq_of_subset_of_ae_sdiff_eq_zero

/-- If a function vanishes on `t \ s` with `s ⊆ t`, then its integrals on `s`
and `t` coincide if `t` is measurable. -/
/-
**MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero** 是 Mathlib 中的一
个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (ht : MeasurableSet t) (h
ts : s subseteq t) (h't : forall x in t \ s, f x = 0) : ∫ x in t, f x ∂μ = ∫ x i
n s, f x ∂μ
参数：ht : MeasurableSet t；hts : s subseteq t；h't : forall x in t \ s, f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero`：setIntegral_
eq_of_subset_of_ae_sdiff_eq_zero (ht : NullMeasurableSet t μ) (hts : s subseteq 
t) (h't : forallᵐ x ∂μ, x in t \ s -> f x = 0) :…
· 使用定理 `MeasurableSet.nullMeasurableSet`：∀ {α : Type u_2} {m0 : MeasurableSpace 
α} {μ : MeasureTheory.Measure α} {s : Set α},   MeasurableSet s → MeasureTheory.
NullMeasurableSet s μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
If a function vanishes on `t \ s` with `s ⊆ t`, then its integrals on `s`
and `t` coincide if `t` is measurable.
-/
theorem setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (ht : MeasurableSet t) (hts : s ⊆ t)
    (h't : ∀ x ∈ t \ s, f x = 0) : ∫ x in t, f x ∂μ = ∫ x in s, f x ∂μ :=
  setIntegral_eq_of_subset_of_ae_sdiff_eq_zero ht.nullMeasurableSet hts
    (Eventually.of_forall fun x hx => h't x hx)

@[deprecated (since := "2026-06-03")]
alias setIntegral_eq_of_subset_of_forall_diff_eq_zero :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero

/-- If a function vanishes almost everywhere on `sᶜ`, then its integral on `s`
coincides with its integral on the whole space. -/
/-
**MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_eq_integral_of_ae_compl_eq_zero (h : forallᵐ x ∂μ, x ∉ s -> f 
x = 0) : ∫ x in s, f x ∂μ = ∫ x, f x ∂μ
参数：h : forallᵐ x ∂μ, x ∉ s -> f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_eq_of_subset_of_ae_sdiff_eq_zero`：setIntegral_
eq_of_subset_of_ae_sdiff_eq_zero (ht : NullMeasurableSet t μ) (hts : s subseteq 
t) (h't : forallᵐ x ∂μ, x in t \ s -> f x = 0) :…
· 使用定理 `MeasureTheory.nullMeasurableSet_univ`：nullMeasurableSet_univ : NullMeasu
rableSet univ μ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If a function vanishes almost everywhere on `sᶜ`, then its integral on `s`
coincides with its integral on the whole space.
-/
theorem setIntegral_eq_integral_of_ae_compl_eq_zero (h : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ := by
  symm
  nth_rw 1 [← setIntegral_univ]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero nullMeasurableSet_univ (subset_univ _)
  filter_upwards [h] with x hx h'x using hx h'x.2

/-- If a function vanishes on `sᶜ`, then its integral on `s` coincides with its integral on the
whole space. -/
/-
**MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_eq_integral_of_forall_compl_eq_zero (h : forall x, x ∉ s -> f 
x = 0) : ∫ x in s, f x ∂μ = ∫ x, f x ∂μ
参数：h : forall x, x ∉ s -> f x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_eq_integral_of_ae_compl_eq_zero`：setIntegral_e
q_integral_of_ae_compl_eq_zero (h : forallᵐ x ∂μ, x ∉ s -> f x = 0) : ∫ x in s, 
f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α

--- 原说明 ---
If a function vanishes on `sᶜ`, then its integral on `s` coincides with its inte
gral on the
whole space.
-/
theorem setIntegral_eq_integral_of_forall_compl_eq_zero (h : ∀ x, x ∉ s → f x = 0) :
    ∫ x in s, f x ∂μ = ∫ x, f x ∂μ :=
  setIntegral_eq_integral_of_ae_compl_eq_zero (Eventually.of_forall h)
/-
**MeasureTheory.setIntegral_neg_eq_setIntegral_nonpos** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory`。
形式化陈述：setIntegral_neg_eq_setIntegral_nonpos [PartialOrder E] {f : X -> E} (hf : 
AEStronglyMeasurable f μ) : ∫ x in {x | f x < 0}, f x ∂μ = ∫ x in {x | f x <= 0}
, f x ∂μ
参数：hf : AEStronglyMeasurable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_eq_fun`：nullMeasura
bleSet_eq_fun {E} [TopologicalSpace E] [MetrizableSpace E] {f g : α -> E} (hf : 
AEStronglyMeasurable f μ) (hg : AEStronglyMeasura…
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.aestronglyMeasurable_zero`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Measu
re α}   [inst_1 : Zero β], Me…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_union_eq_left_of_ae`：integral_union_eq_left_of_ae
 (ht_eq : forallᵐ x ∂μ.restrict t, f x = 0) : ∫ x in s union t, f x ∂μ = ∫ x in 
s, f x ∂μ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_mem₀`：ae_restrict_mem₀ (hs : NullMeasurableSet
 s μ) : forallᵐ x ∂μ.restrict s, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
theorem setIntegral_neg_eq_setIntegral_nonpos [PartialOrder E] {f : X → E}
    (hf : AEStronglyMeasurable f μ) :
    ∫ x in {x | f x < 0}, f x ∂μ = ∫ x in {x | f x ≤ 0}, f x ∂μ := by
  have h_union : {x | f x ≤ 0} = {x | f x < 0} ∪ {x | f x = 0} := by
    simp_rw [le_iff_lt_or_eq, ofPred_or]
  rw [h_union]
  have B : NullMeasurableSet {x | f x = 0} μ :=
    hf.nullMeasurableSet_eq_fun aestronglyMeasurable_zero
  symm
  refine integral_union_eq_left_of_ae ?_
  filter_upwards [ae_restrict_mem₀ B] with x hx using hx
/-
**MeasureTheory.integral_norm_eq_pos_sub_neg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_norm_eq_pos_sub_neg {f : X -> Real} (hfi : Integrable f μ) : ∫ x,
 ‖f x‖ ∂μ = ∫ x in {x | 0 <= f x}, f x ∂μ - ∫ x in {x | f x <= 0}, f x ∂μ
参数：hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.nullMeasurableSet_le`：nullMeasurableS
et_le [Preorder β] [OrderClosedTopology β] [PseudoMetrizableSpace β] {f g : α ->
 β} (hf : AEStronglyMeasurable f μ) (hg : AES…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_add_compl₀`：integral_add_compl₀ (hs : NullMeasura
bleSet s μ) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x,
 f x ∂μ
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.setIntegral_congr_fun₀`：setIntegral_congr_fun₀ (hs : NullM
easurableSet s μ) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `MeasureTheory.NullMeasurableSet.compl`：compl (h : NullMeasurableSet s μ)
 : NullMeasurableSet sᶜ μ
· 使用定理 `abs_eq_neg_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Line
arOrder G] [IsOrderedAddMonoid G] {a : G}, |a| = -a ↔ a ≤ 0
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 53 条，此处仅展示前 30 条）
-/
theorem integral_norm_eq_pos_sub_neg {f : X → ℝ} (hfi : Integrable f μ) :
    ∫ x, ‖f x‖ ∂μ = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | f x ≤ 0}, f x ∂μ :=
  have h_meas : NullMeasurableSet {x | 0 ≤ f x} μ :=
    aestronglyMeasurable_const.nullMeasurableSet_le hfi.1
  calc
    ∫ x, ‖f x‖ ∂μ = ∫ x in {x | 0 ≤ f x}, ‖f x‖ ∂μ + ∫ x in {x | 0 ≤ f x}ᶜ, ‖f x‖ ∂μ := by
      rw [← integral_add_compl₀ h_meas hfi.norm]
    _ = ∫ x in {x | 0 ≤ f x}, f x ∂μ + ∫ x in {x | 0 ≤ f x}ᶜ, ‖f x‖ ∂μ := by
      congr 1
      refine setIntegral_congr_fun₀ h_meas fun x hx => ?_
      rw [Real.norm_eq_abs, abs_eq_self.mpr _]
      exact hx
    _ = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | 0 ≤ f x}ᶜ, f x ∂μ := by
      congr 1
      rw [← integral_neg]
      refine setIntegral_congr_fun₀ h_meas.compl fun x hx => ?_
      rw [Real.norm_eq_abs, abs_eq_neg_self.mpr _]
      rw [Set.mem_compl_iff, Set.notMem_ofPred_iff] at hx
      linarith
    _ = ∫ x in {x | 0 ≤ f x}, f x ∂μ - ∫ x in {x | f x ≤ 0}, f x ∂μ := by
      rw [← setIntegral_neg_eq_setIntegral_nonpos hfi.1, compl_ofPred]; simp only [not_le]
/-
**MeasureTheory.setIntegral_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_const [CompleteSpace E] (c : E) : ∫ _ in s, c ∂μ = μ.real s • 
c
参数：c : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_const`：integral_const (c : E) : ∫ _ : α, c ∂μ = μ
.real univ • c
· 使用定理 `MeasureTheory.measureReal_restrict_apply_univ`：measureReal_restrict_appl
y_univ (s : Set α) : (μ.restrict s).real univ = μ.real s
-/
theorem setIntegral_const [CompleteSpace E] (c : E) : ∫ _ in s, c ∂μ = μ.real s • c := by
  rw [integral_const, measureReal_restrict_apply_univ]

@[simp]
/-
**MeasureTheory.integral_indicator_const** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：integral_indicator_const [CompleteSpace E] (e : E) ⦃s : Set X⦄ (s_meas : M
easurableSet s) : ∫ x : X, s.indicator (fun _ : X => e) x ∂μ = μ.real s • e
参数：e : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
-/
theorem integral_indicator_const [CompleteSpace E] (e : E) ⦃s : Set X⦄ (s_meas : MeasurableSet s) :
    ∫ x : X, s.indicator (fun _ : X => e) x ∂μ = μ.real s • e := by
  rw [integral_indicator s_meas, ← setIntegral_const]

@[simp]
/-
**MeasureTheory.integral_indicator_one** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：integral_indicator_one ⦃s : Set X⦄ (hs : MeasurableSet s) : ∫ x, s.indicat
or 1 x ∂μ = μ.real s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.integral_indicator_const`：integral_indicator_const [Comple
teSpace E] (e : E) ⦃s : Set X⦄ (s_meas : MeasurableSet s) : ∫ x : X, s.indicator
 (fun _ : X => e) x ∂μ = μ.r…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem integral_indicator_one ⦃s : Set X⦄ (hs : MeasurableSet s) :
    ∫ x, s.indicator 1 x ∂μ = μ.real s :=
  (integral_indicator_const 1 hs).trans ((smul_eq_mul ..).trans (mul_one _))
/-
**MeasureTheory.setIntegral_indicatorConstLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：setIntegral_indicatorConstLp [CompleteSpace E] {p : Real>=0∞} (hs : Measur
ableSet s) (ht : MeasurableSet t) (hμt : μ t != ∞) (e : E) : ∫ x in s, indicator
ConstLp p ht hμt e x ∂μ = μ.real (t inter s) • e
参数：hs : MeasurableSet s；ht : MeasurableSet t；hμt : μ t != ∞；e : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.indicatorConstLp_coeFn`：indicatorConstLp_coeFn : ⇑(indicat
orConstLp p hs hμs c) =ᵐ[μ] s.indicator fun _ => c
· 使用定理 `MeasureTheory.integral_indicator_const`：integral_indicator_const [Comple
teSpace E] (e : E) ⦃s : Set X⦄ (s_meas : MeasurableSet s) : ∫ x : X, s.indicator
 (fun _ : X => e) x ∂μ = μ.r…
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
-/
theorem setIntegral_indicatorConstLp [CompleteSpace E]
    {p : ℝ≥0∞} (hs : MeasurableSet s) (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (e : E) :
    ∫ x in s, indicatorConstLp p ht hμt e x ∂μ = μ.real (t ∩ s) • e :=
  calc
    ∫ x in s, indicatorConstLp p ht hμt e x ∂μ = ∫ x in s, t.indicator (fun _ => e) x ∂μ := by
      rw [setIntegral_congr_ae hs (indicatorConstLp_coeFn.mono fun x hx _ => hx)]
    _ = (μ.real (t ∩ s)) • e := by rw [integral_indicator_const _ ht, measureReal_restrict_apply ht]
/-
**MeasureTheory.integral_indicatorConstLp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：integral_indicatorConstLp [CompleteSpace E] {p : Real>=0∞} (ht : Measurabl
eSet t) (hμt : μ t != ∞) (e : E) : ∫ x, indicatorConstLp p ht hμt e x ∂μ = μ.rea
l t • e
参数：ht : MeasurableSet t；hμt : μ t != ∞；e : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_indicatorConstLp`：setIntegral_indicatorConstLp
 [CompleteSpace E] {p : Real>=0∞} (hs : MeasurableSet s) (ht : MeasurableSet t) 
(hμt : μ t != ∞) (e : E) : ∫ x i…
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem integral_indicatorConstLp [CompleteSpace E]
    {p : ℝ≥0∞} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) (e : E) :
    ∫ x, indicatorConstLp p ht hμt e x ∂μ = μ.real t • e :=
  calc
    ∫ x, indicatorConstLp p ht hμt e x ∂μ = ∫ x in univ, indicatorConstLp p ht hμt e x ∂μ := by
      rw [setIntegral_univ]
    _ = μ.real (t ∩ univ) • e := setIntegral_indicatorConstLp MeasurableSet.univ ht hμt e
    _ = μ.real t • e := by rw [inter_univ]
/-
**MeasureTheory.setIntegral_map** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_map {Y} [MeasurableSpace Y] {g : X -> Y} {f : Y -> E} {s : Set
 Y} (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (Measure.map g μ)) (hg :
 AEMeasurable g μ) : ∫ y in s, f y ∂Measure.map g μ = ∫ x in g ⁻¹' s, f (g x) ∂μ
参数：hs : MeasurableSet s；hf : AEStronglyMeasurable f (Measure.map g μ)；hg : AEMea
surable g μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Measure.restrict_map_of_aemeasurable`：MeasureTheory.Measur
e.restrict_map_of_aemeasurable {f : α -> δ} (hf : AEMeasurable f μ) {s : Set δ} 
(hs : MeasurableSet s) : (μ.map f).restr…
· 使用定理 `MeasureTheory.integral_map`：integral_map {β} [MeasurableSpace β] {φ : α 
-> β} (hφ : AEMeasurable φ μ) {f : β -> G} (hfm : AEStronglyMeasurable f (Measur
e.map φ μ)) : ∫ …
· 使用定理 `AEMeasurable.mono_measure`：mono_measure (h : AEMeasurable f μ) (h' : ν <
= μ) : AEMeasurable f ν
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.mono_measure`：mono_measure {ν : Measu
re α} (hf : AEStronglyMeasurable[m] f μ) (h : ν <= μ) : AEStronglyMeasurable[m] 
f ν
· 使用定理 `MeasureTheory.Measure.map_mono_of_aemeasurable`：MeasureTheory.Measure.ma
p_mono_of_aemeasurable {f : α -> δ} (h : μ <= ν) (hf : AEMeasurable f ν) : μ.map
 f <= ν.map f
-/
theorem setIntegral_map {Y} [MeasurableSpace Y] {g : X → Y} {f : Y → E} {s : Set Y}
    (hs : MeasurableSet s) (hf : AEStronglyMeasurable f (Measure.map g μ)) (hg : AEMeasurable g μ) :
    ∫ y in s, f y ∂Measure.map g μ = ∫ x in g ⁻¹' s, f (g x) ∂μ := by
  rw [Measure.restrict_map_of_aemeasurable hg hs,
    integral_map (hg.mono_measure Measure.restrict_le_self) (hf.mono_measure _)]
  exact Measure.map_mono_of_aemeasurable Measure.restrict_le_self hg
/-
**MeasureTheory._root_.MeasurableEmbedding.setIntegral_map** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MeasurableEmbedding.setIntegral_map {Y} {_ : MeasurableSpace Y} {f : X → Y}
    (hf : MeasurableEmbedding f) (g : Y → E) (s : Set Y) :
    ∫ y in s, g y ∂Measure.map f μ = ∫ x in f ⁻¹' s, g (f x) ∂μ := by
  rw [hf.restrict_map, hf.integral_map]
/-
**MeasureTheory._root_.Topology.IsClosedEmbedding.setIntegral_map** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Topology.IsClosedEmbedding.setIntegral_map [TopologicalSpace X] [BorelSpace X] {Y}
    [MeasurableSpace Y] [TopologicalSpace Y] [BorelSpace Y] {g : X → Y} {f : Y → E} (s : Set Y)
    (hg : IsClosedEmbedding g) : ∫ y in s, f y ∂Measure.map g μ = ∫ x in g ⁻¹' s, f (g x) ∂μ :=
  hg.measurableEmbedding.setIntegral_map _ _
/-
**MeasureTheory.MeasurePreserving.setIntegral_preimage_emb** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.MeasurePreserving`。
形式化陈述：∀ {X : Type u_1} {E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℝ E]   {μ : MeasureTheory.Measure X} {Y : Typ
e u_5} {x : MeasurableSpace Y} {f : X → Y} {ν : MeasureTheory.Measure Y},   Meas
ureTheory.MeasurePreserving f μ ν →     MeasurableEmbedding f → ∀ (g : Y → E) (s
 : Set Y), ∫ (x : X) in f ⁻¹' s, g (f x) ∂μ = ∫ (y : Y) in s, g y ∂ν
参数：g : Y → E；s : Set Y；x : X；f x；y : Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.MeasurePreserving.restrict_preimage_emb`：restrict_preimage
_emb {f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) 
(s : Set β) : MeasurePreserving f (μa.restr…
-/
theorem MeasurePreserving.setIntegral_preimage_emb {Y} {_ : MeasurableSpace Y} {f : X → Y} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : Y → E) (s : Set Y) :
    ∫ x in f ⁻¹' s, g (f x) ∂μ = ∫ y in s, g y ∂ν :=
  (h₁.restrict_preimage_emb h₂ s).integral_comp h₂ _
/-
**MeasureTheory.MeasurePreserving.setIntegral_image_emb** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.MeasurePreserving`。
形式化陈述：∀ {X : Type u_1} {E : Type u_3} {mX : MeasurableSpace X} [inst : NormedAdd
CommGroup E] [inst_1 : NormedSpace ℝ E]   {μ : MeasureTheory.Measure X} {Y : Typ
e u_5} {x : MeasurableSpace Y} {f : X → Y} {ν : MeasureTheory.Measure Y},   Meas
ureTheory.MeasurePreserving f μ ν →     MeasurableEmbedding f → ∀ (g : Y → E) (s
 : Set X), ∫ (y : Y) in f '' s, g y ∂ν = ∫ (x : X) in s, g (f x) ∂μ
参数：g : Y → E；s : Set X；y : Y；x : X；f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.MeasurePreserving.restrict_image_emb`：restrict_image_emb {
f : α -> β} (hf : MeasurePreserving f μa μb) (h₂ : MeasurableEmbedding f) (s : S
et α) : MeasurePreserving f (μa.restrict…
-/
theorem MeasurePreserving.setIntegral_image_emb {Y} {_ : MeasurableSpace Y} {f : X → Y} {ν}
    (h₁ : MeasurePreserving f μ ν) (h₂ : MeasurableEmbedding f) (g : Y → E) (s : Set X) :
    ∫ y in f '' s, g y ∂ν = ∫ x in s, g (f x) ∂μ :=
  Eq.symm <| (h₁.restrict_image_emb h₂ s).integral_comp h₂ _
/-
**MeasureTheory.setIntegral_map_equiv** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_map_equiv {Y} [MeasurableSpace Y] (e : X ≃ᵐ Y) (f : Y -> E) (s
 : Set Y) : ∫ y in s, f y ∂Measure.map e μ = ∫ x in e ⁻¹' s, f (e x) ∂μ
参数：e : X ≃ᵐ Y；f : Y -> E；s : Set Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableEmbedding.setIntegral_map`：∀ {X : Type u_1} {E : Type u_3} {mX
 : MeasurableSpace X} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E]  
 {μ : MeasureTheory.Measu…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
-/
theorem setIntegral_map_equiv {Y} [MeasurableSpace Y] (e : X ≃ᵐ Y) (f : Y → E) (s : Set Y) :
    ∫ y in s, f y ∂Measure.map e μ = ∫ x in e ⁻¹' s, f (e x) ∂μ :=
  e.measurableEmbedding.setIntegral_map f s
/-
**MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：norm_setIntegral_le_of_norm_le_const_ae {C : Real} (hs : μ s < ∞) (hC : fo
rallᵐ x ∂μ.restrict s, ‖f x‖ <= C) : ‖∫ x in s, f x ∂μ‖ <= C * μ.real s
参数：hs : μ s < ∞；hC : forallᵐ x ∂μ.restrict s, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_apply_univ`：restrict_apply_univ (s : Set 
α) : μ.restrict s univ = μ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.measureReal_restrict_apply`：measureReal_restrict_apply (ht
 : MeasurableSet t) : (μ.restrict s).real t = μ.real (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.norm_integral_le_of_norm_le_const`：norm_integral_le_of_nor
m_le_const [IsFiniteMeasure μ] {f : α -> G} {C : Real} (h : forallᵐ x ∂μ, ‖f x‖ 
<= C) : ‖∫ x, f x ∂μ‖ <= C * μ.real u…
-/
theorem norm_setIntegral_le_of_norm_le_const_ae {C : ℝ} (hs : μ s < ∞)
    (hC : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C) : ‖∫ x in s, f x ∂μ‖ ≤ C * μ.real s := by
  rw [← Measure.restrict_apply_univ] at *
  have : IsFiniteMeasure (μ.restrict s) := ⟨hs⟩
  simpa using norm_integral_le_of_norm_le_const hC
/-
**MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae'** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：norm_setIntegral_le_of_norm_le_const_ae' {C : Real} (hs : μ s < ∞) (hC : f
orallᵐ x ∂μ, x in s -> ‖f x‖ <= C) : ‖∫ x in s, f x ∂μ‖ <= C * μ.real s
参数：hs : μ s < ∞；hC : forallᵐ x ∂μ, x in s -> ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae`：norm_setIntegral_
le_of_norm_le_const_ae {C : Real} (hs : μ s < ∞) (hC : forallᵐ x ∂μ.restrict s, 
‖f x‖ <= C) : ‖∫ x in s, f x ∂μ‖ <= C * μ.r…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_mem_imp_eq_mk`：ae_mem_imp_eq_mk {s
} (h : AEStronglyMeasurable[m] f (μ.restrict s)) : forallᵐ x ∂μ, x in s -> f x =
 h.mk f x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.StronglyMeasurable.measurable`：∀ {α : Type u_1} {β : Type 
u_2} {f : α → β} {x : MeasurableSpace α} [inst : TopologicalSpace β]   [Topologi
calSpace.PseudoMetrizableSpace β]…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.StronglyMeasurable.norm`：∀ {α : Type u_1} {x : MeasurableS
pace α} {β : Type u_5} [inst : SeminormedAddCommGroup β] {f : α → β},   MeasureT
heory.StronglyMeasurable f …
· 使用引理 `MeasureTheory.AEStronglyMeasurable.stronglyMeasurable_mk`：stronglyMeasur
able_mk (hf : AEStronglyMeasurable[m] f μ) : StronglyMeasurable[m] (hf.mk f)
· 使用定理 `measurableSet_Iic`：measurableSet_Iic [ClosedIicTopology α] : MeasurableS
et (Iic a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iff`：ae_restrict_iff {p : α -> Prop} (hp : Mea
surableSet { x | p x }) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s 
-> p x
· 使用定理 `MeasureTheory.AEStronglyMeasurable.ae_eq_mk`：ae_eq_mk (hf : AEStronglyMe
asurable[m] f μ) : f =ᵐ[μ] hf.mk f
· 使用定理 `MeasureTheory.integral_non_aestronglyMeasurable`：integral_non_aestrongly
Measurable {f : α -> G} (h : ¬AEStronglyMeasurable f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `MeasureTheory.frequently_ae_mem_iff`：frequently_ae_mem_iff {s : Set α} :
 (existsᵐ a ∂μ, a in s) ↔ μ s != 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.Measure.restrict_eq_zero`：restrict_eq_zero : μ.restrict s 
= 0 ↔ μ s = 0
· 使用定理 `Filter.Frequently.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 34 条，此处仅展示前 30 条）
-/
theorem norm_setIntegral_le_of_norm_le_const_ae' {C : ℝ} (hs : μ s < ∞)
    (hC : ∀ᵐ x ∂μ, x ∈ s → ‖f x‖ ≤ C) : ‖∫ x in s, f x ∂μ‖ ≤ C * μ.real s := by
  by_cases hfm : AEStronglyMeasurable f (μ.restrict s)
  · apply norm_setIntegral_le_of_norm_le_const_ae hs
    have A : ∀ᵐ x : X ∂μ, x ∈ s → ‖AEStronglyMeasurable.mk f hfm x‖ ≤ C := by
      filter_upwards [hC, hfm.ae_mem_imp_eq_mk] with _ h1 h2 h3
      rw [← h2 h3]
      exact h1 h3
    have B : MeasurableSet {x | ‖hfm.mk f x‖ ≤ C} :=
      hfm.stronglyMeasurable_mk.norm.measurable measurableSet_Iic
    filter_upwards [hfm.ae_eq_mk, (ae_restrict_iff B).2 A] with _ h1 _
    rwa [h1]
  · rw [integral_non_aestronglyMeasurable hfm]
    have : ∃ᵐ (x : X) ∂μ, x ∈ s := by
      apply frequently_ae_mem_iff.mpr
      contrapose hfm
      simp [Measure.restrict_eq_zero.mpr hfm]
    rcases (this.and_eventually hC).exists with ⟨x, hx, h'x⟩
    have : 0 ≤ C := (norm_nonneg _).trans (h'x hx)
    simp only [norm_zero, ge_iff_le]
    positivity
/-
**MeasureTheory.norm_setIntegral_le_of_norm_le_const** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：norm_setIntegral_le_of_norm_le_const {C : Real} (hs : μ s < ∞) (hC : foral
l x in s, ‖f x‖ <= C) : ‖∫ x in s, f x ∂μ‖ <= C * μ.real s
参数：hs : μ s < ∞；hC : forall x in s, ‖f x‖ <= C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.norm_setIntegral_le_of_norm_le_const_ae'`：norm_setIntegral
_le_of_norm_le_const_ae' {C : Real} (hs : μ s < ∞) (hC : forallᵐ x ∂μ, x in s ->
 ‖f x‖ <= C) : ‖∫ x in s, f x ∂μ‖ <= C * μ.r…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem norm_setIntegral_le_of_norm_le_const {C : ℝ} (hs : μ s < ∞) (hC : ∀ x ∈ s, ‖f x‖ ≤ C) :
    ‖∫ x in s, f x ∂μ‖ ≤ C * μ.real s :=
  norm_setIntegral_le_of_norm_le_const_ae' hs (Eventually.of_forall hC)
/-
**MeasureTheory.norm_integral_sub_setIntegral_le** 是 Mathlib 中的一个定理，位于命名空间 `Meas
ureTheory`。
形式化陈述：norm_integral_sub_setIntegral_le [IsFiniteMeasure μ] {C : Real} (hf : fora
llᵐ (x : X) ∂μ, ‖f x‖ <= C) {s : Set X} (hs : MeasurableSet s) (hf1 : Integrable
 f μ) : ‖∫ (x : X), f x ∂μ - ∫ x in s, f x ∂μ‖ <= μ.real sᶜ * C
参数：hf : forallᵐ (x : X) ∂μ, ‖f x‖ <= C；hs : MeasurableSet s；hf1 : Integrable f μ
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.integral_add_compl`：integral_add_compl (hs : MeasurableSet
 s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.Integrable.restrict`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {ε : Type u_8} [inst : TopologicalSpace ε]   [
inst_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `MeasureTheory.integrable_const`：integrable_const [IsFiniteMeasure μ] (c 
: β) : Integrable (fun _ : α => c) μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MeasureTheory.norm_integral_le_integral_norm`：norm_integral_le_integral_
norm (f : α -> G) : ‖∫ a, f a ∂μ‖ <= ∫ a, ‖f a‖ ∂μ
-/
theorem norm_integral_sub_setIntegral_le [IsFiniteMeasure μ] {C : ℝ}
    (hf : ∀ᵐ (x : X) ∂μ, ‖f x‖ ≤ C) {s : Set X} (hs : MeasurableSet s) (hf1 : Integrable f μ) :
    ‖∫ (x : X), f x ∂μ - ∫ x in s, f x ∂μ‖ ≤ μ.real sᶜ * C := by
  have h0 : ∫ (x : X), f x ∂μ - ∫ x in s, f x ∂μ = ∫ x in sᶜ, f x ∂μ := by
    rw [sub_eq_iff_eq_add, add_comm, integral_add_compl hs hf1]
  have h1 : ∫ x in sᶜ, ‖f x‖ ∂μ ≤ ∫ _ in sᶜ, C ∂μ :=
    integral_mono_ae hf1.norm.restrict (integrable_const C) (ae_restrict_of_ae hf)
  have h2 : ∫ _ in sᶜ, C ∂μ = μ.real sᶜ * C := by
    rw [setIntegral_const C, smul_eq_mul]
  rw [h0, ← h2]
  exact le_trans (norm_integral_le_integral_norm f) h1
/-
**MeasureTheory.setIntegral_eq_zero_iff_of_nonneg_ae** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：setIntegral_eq_zero_iff_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.restric
t s] f) (hfi : IntegrableOn f s μ) : ∫ x in s, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict s] 0
参数：hf : 0 <=ᵐ[μ.restrict s] f；hfi : IntegrableOn f s μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.integral_eq_zero_iff_of_nonneg_ae`：integral_eq_zero_iff_of
_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) : ∫ x, f x ∂
μ = 0 ↔ f =ᵐ[μ] 0
-/
theorem setIntegral_eq_zero_iff_of_nonneg_ae {f : X → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f)
    (hfi : IntegrableOn f s μ) : ∫ x in s, f x ∂μ = 0 ↔ f =ᵐ[μ.restrict s] 0 :=
  integral_eq_zero_iff_of_nonneg_ae hf hfi
/-
**MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：setIntegral_pos_iff_support_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.res
trict s] f) (hfi : IntegrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ 0 < μ (support
 f inter s)
参数：hf : 0 <=ᵐ[μ.restrict s] f；hfi : IntegrableOn f s μ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_pos_iff_support_of_nonneg_ae`：integral_pos_iff_su
pport_of_nonneg_ae {f : α -> Real} (hf : 0 <=ᵐ[μ] f) (hfi : Integrable f μ) : (0
 < ∫ x, f x ∂μ) ↔ 0 < μ (Function.support…
· 使用定理 `MeasureTheory.Measure.restrict_apply₀`：restrict_apply₀ (ht : NullMeasura
bleSet t (μ.restrict s)) : μ.restrict s t = μ (t inter s)
· 使用定理 `Function.support_eq_preimage`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] (f : ι → M), Function.support f = f ⁻¹' {0}ᶜ
· 使用定理 `AEMeasurable.nullMeasurable`：∀ {α : Type u_1} {β : Type u_2} {m0 : Measu
rableSpace α} {mβ : MeasurableSpace β} {μ : MeasureTheory.Measure α}   {f : α → 
β}, AEMeasurable …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `MeasurableSingletonClass.measurableSet_singleton`：∀ {α : Type u_7} {inst
 : MeasurableSpace α} [self : MeasurableSingletonClass α] (x : α), MeasurableSet
 {x}
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem setIntegral_pos_iff_support_of_nonneg_ae {f : X → ℝ} (hf : 0 ≤ᵐ[μ.restrict s] f)
    (hfi : IntegrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ 0 < μ (support f ∩ s) := by
  rw [integral_pos_iff_support_of_nonneg_ae hf hfi, Measure.restrict_apply₀]
  rw [support_eq_preimage]
  exact hfi.aestronglyMeasurable.aemeasurable.nullMeasurable (measurableSet_singleton 0).compl
/-
**MeasureTheory.setIntegral_gt_gt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_gt_gt {R : Real} {f : X -> Real} (hR : 0 <= R) (hfint : Integr
ableOn f {x | ↑R < f x} μ) (hμ : μ {x | ↑R < f x} != 0) : μ.real {x | ↑R < f x} 
* R < ∫ x in {x | ↑R < f x}, f x ∂μ
参数：hR : 0 <= R；hfint : IntegrableOn f {x | ↑R < f x} μ；hμ : μ {x | ↑R < f x} != 
0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.aestronglyMeasurable_const`：aestronglyMeasurable_const {b 
: β} : AEStronglyMeasurable[m] (fun _ : α => b) μ
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.setLIntegral_mono_ae`：setLIntegral_mono_ae {s : Set α} {f 
g : α -> Real>=0∞} (hg : AEMeasurable g (μ.restrict s)) (hfg : forallᵐ x ∂μ, x i
n s -> f x <= g x) : ∫⁻ …
· 使用定理 `MeasureTheory.AEStronglyMeasurable.enorm`：∀ {α : Type u_1} {m₀ : Measura
bleSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : TopologicalSpac
e β]   [inst_1 : ContinuousENo…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.nnnorm_of_nonneg`：nnnorm_of_nonneg (hr : 0 <= r) : ‖r‖₊ = .mk r hr
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用定理 `MeasureTheory.integral_sub`：integral_sub {f g : α -> G} (hf : Integrable
 f μ) (hg : Integrable g μ) : ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae`：setIntegral_pos_
iff_support_of_nonneg_ae {f : X -> Real} (hf : 0 <=ᵐ[μ.restrict s] f) (hfi : Int
egrableOn f s μ) : (0 < ∫ x in s, f x ∂μ) ↔ …
· 使用定理 `Pi.zero_def`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zero 
(M i)], 0 = fun x => 0
· 使用定理 `Filter.EventuallyLE.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE β] 
(l : Filter α) (f g : α → β), (f ≤ᶠ[l] g) = ∀ᶠ (x : α) in l, f x ≤ g x
· 使用定理 `MeasureTheory.ae_restrict_iff₀`：ae_restrict_iff₀ {p : α -> Prop} (hp : N
ullMeasurableSet { x | p x } (μ.restrict s)) : (forallᵐ x ∂μ.restrict s, p x) ↔ 
forallᵐ x ∂μ, x in s…
（共 53 条，此处仅展示前 30 条）
-/
theorem setIntegral_gt_gt {R : ℝ} {f : X → ℝ} (hR : 0 ≤ R)
    (hfint : IntegrableOn f {x | ↑R < f x} μ) (hμ : μ {x | ↑R < f x} ≠ 0) :
    μ.real {x | ↑R < f x} * R < ∫ x in {x | ↑R < f x}, f x ∂μ := by
  have : IntegrableOn (fun _ => R) {x | ↑R < f x} μ := by
    refine ⟨aestronglyMeasurable_const, lt_of_le_of_lt ?_ hfint.2⟩
    refine setLIntegral_mono_ae hfint.1.enorm <| ae_of_all _ fun x hx => ?_
    simp only [ENNReal.coe_le_coe, Real.nnnorm_of_nonneg hR, enorm_eq_nnnorm,
      Real.nnnorm_of_nonneg (hR.trans <| le_of_lt hx)]
    exact le_of_lt hx
  rw [← sub_pos, ← smul_eq_mul, ← setIntegral_const, ← integral_sub hfint this,
    setIntegral_pos_iff_support_of_nonneg_ae]
  · rw [← pos_iff_ne_zero] at hμ
    rwa [Set.inter_eq_self_of_subset_right]
    exact fun x hx => Ne.symm (ne_of_lt <| sub_pos.2 hx)
  · rw [Pi.zero_def, EventuallyLE, ae_restrict_iff₀]
    · exact Eventually.of_forall fun x hx => sub_nonneg.2 <| le_of_lt hx
    · exact nullMeasurableSet_le aemeasurable_zero (hfint.1.aemeasurable.sub aemeasurable_const)
  · exact Integrable.sub hfint this
/-
**MeasureTheory.setIntegral_trim** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_trim {X} {m m0 : MeasurableSpace X} {μ : Measure X} (hm : m <=
 m0) {f : X -> E} (hf_meas : StronglyMeasurable[m] f) {s : Set X} (hs : Measurab
leSet[m] s) : ∫ x in s, f x ∂μ = ∫ x in s, f x ∂μ.trim hm
参数：hm : m <= m0；hf_meas : StronglyMeasurable[m] f；hs : MeasurableSet[m] s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_trim`：integral_trim (hm : m <= m0) {f : β -> G} (
hf : StronglyMeasurable[m] f) : ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm
· 使用定理 `MeasureTheory.restrict_trim`：restrict_trim (hm : m <= m0) (μ : Measure α
) (hs : @MeasurableSet α m s) : @Measure.restrict α m (μ.trim hm) s = (μ.restric
t s).trim hm
-/
theorem setIntegral_trim {X} {m m0 : MeasurableSpace X} {μ : Measure X} (hm : m ≤ m0) {f : X → E}
    (hf_meas : StronglyMeasurable[m] f) {s : Set X} (hs : MeasurableSet[m] s) :
    ∫ x in s, f x ∂μ = ∫ x in s, f x ∂μ.trim hm := by
  rwa [integral_trim hm hf_meas, restrict_trim hm μ]

/-! ### Lemmas about adding and removing interval boundaries

The primed lemmas take explicit arguments about the endpoint having zero measure, while the
unprimed ones use `[NullSingletonClass μ]`.
-/

section PartialOrder

variable [PartialOrder X] {x y : X}

/-
**MeasureTheory.integral_Icc_eq_integral_Ioc'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_Icc_eq_integral_Ioc' (hx : μ {x} = 0) : ∫ t in Icc x y, f t ∂μ = 
∫ t in Ioc x y, f t ∂μ
参数：hx : μ {x} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Ioc_ae_eq_Icc'`：Ioc_ae_eq_Icc' (ha : μ {a} = 0) : Ioc a b 
=ᵐ[μ] Icc a b
-/
theorem integral_Icc_eq_integral_Ioc' (hx : μ {x} = 0) :
    ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ :=
  setIntegral_congr_set (Ioc_ae_eq_Icc' hx).symm
/-
**MeasureTheory.integral_Icc_eq_integral_Ico'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_Icc_eq_integral_Ico' (hy : μ {y} = 0) : ∫ t in Icc x y, f t ∂μ = 
∫ t in Ico x y, f t ∂μ
参数：hy : μ {y} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Ico_ae_eq_Icc'`：Ico_ae_eq_Icc' (hb : μ {b} = 0) : Ico a b 
=ᵐ[μ] Icc a b
-/
theorem integral_Icc_eq_integral_Ico' (hy : μ {y} = 0) :
    ∫ t in Icc x y, f t ∂μ = ∫ t in Ico x y, f t ∂μ :=
  setIntegral_congr_set (Ico_ae_eq_Icc' hy).symm
/-
**MeasureTheory.integral_Ioc_eq_integral_Ioo'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_Ioc_eq_integral_Ioo' (hy : μ {y} = 0) : ∫ t in Ioc x y, f t ∂μ = 
∫ t in Ioo x y, f t ∂μ
参数：hy : μ {y} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ioc'`：Ioo_ae_eq_Ioc' (hb : μ {b} = 0) : Ioo a b 
=ᵐ[μ] Ioc a b
-/
theorem integral_Ioc_eq_integral_Ioo' (hy : μ {y} = 0) :
    ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  setIntegral_congr_set (Ioo_ae_eq_Ioc' hy).symm
/-
**MeasureTheory.integral_Ico_eq_integral_Ioo'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_Ico_eq_integral_Ioo' (hx : μ {x} = 0) : ∫ t in Ico x y, f t ∂μ = 
∫ t in Ioo x y, f t ∂μ
参数：hx : μ {x} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Ioo_ae_eq_Ico'`：Ioo_ae_eq_Ico' (ha : μ {a} = 0) : Ioo a b 
=ᵐ[μ] Ico a b
-/
theorem integral_Ico_eq_integral_Ioo' (hx : μ {x} = 0) :
    ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  setIntegral_congr_set (Ioo_ae_eq_Ico' hx).symm
/-
**MeasureTheory.integral_Icc_eq_integral_Ioo'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_Icc_eq_integral_Ioo' (hx : μ {x} = 0) (hy : μ {y} = 0) : ∫ t in I
cc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
参数：hx : μ {x} = 0；hy : μ {y} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Ioo_ae_eq_Icc'`：Ioo_ae_eq_Icc' (ha : μ {a} = 0) (hb : μ {b
} = 0) : Ioo a b =ᵐ[μ] Icc a b
-/
theorem integral_Icc_eq_integral_Ioo' (hx : μ {x} = 0) (hy : μ {y} = 0) :
    ∫ t in Icc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  setIntegral_congr_set (Ioo_ae_eq_Icc' hx hy).symm
/-
**MeasureTheory.integral_Iic_eq_integral_Iio'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_Iic_eq_integral_Iio' (hx : μ {x} = 0) : ∫ t in Iic x, f t ∂μ = ∫ 
t in Iio x, f t ∂μ
参数：hx : μ {x} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Iio_ae_eq_Iic'`：Iio_ae_eq_Iic' (ha : μ {a} = 0) : Iio a =ᵐ
[μ] Iic a
-/
theorem integral_Iic_eq_integral_Iio' (hx : μ {x} = 0) :
    ∫ t in Iic x, f t ∂μ = ∫ t in Iio x, f t ∂μ :=
  setIntegral_congr_set (Iio_ae_eq_Iic' hx).symm
/-
**MeasureTheory.integral_Ici_eq_integral_Ioi'** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory`。
形式化陈述：integral_Ici_eq_integral_Ioi' (hx : μ {x} = 0) : ∫ t in Ici x, f t ∂μ = ∫ 
t in Ioi x, f t ∂μ
参数：hx : μ {x} = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.Ioi_ae_eq_Ici'`：Ioi_ae_eq_Ici' (ha : μ {a} = 0) : Ioi a =ᵐ
[μ] Ici a
-/
theorem integral_Ici_eq_integral_Ioi' (hx : μ {x} = 0) :
    ∫ t in Ici x, f t ∂μ = ∫ t in Ioi x, f t ∂μ :=
  setIntegral_congr_set (Ioi_ae_eq_Ici' hx).symm

variable [NullSingletonClass μ]
/-
**MeasureTheory.integral_Icc_eq_integral_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_Icc_eq_integral_Ioc : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f 
t ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_Icc_eq_integral_Ioc'`：integral_Icc_eq_integral_Io
c' (hx : μ {x} = 0) : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem integral_Icc_eq_integral_Ioc : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ :=
  integral_Icc_eq_integral_Ioc' <| measure_singleton x
/-
**MeasureTheory.integral_Icc_eq_integral_Ico** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_Icc_eq_integral_Ico : ∫ t in Icc x y, f t ∂μ = ∫ t in Ico x y, f 
t ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_Icc_eq_integral_Ico'`：integral_Icc_eq_integral_Ic
o' (hy : μ {y} = 0) : ∫ t in Icc x y, f t ∂μ = ∫ t in Ico x y, f t ∂μ
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem integral_Icc_eq_integral_Ico : ∫ t in Icc x y, f t ∂μ = ∫ t in Ico x y, f t ∂μ :=
  integral_Icc_eq_integral_Ico' <| measure_singleton y
/-
**MeasureTheory.integral_Ioc_eq_integral_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_Ioc_eq_integral_Ioo : ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f 
t ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_Ioc_eq_integral_Ioo'`：integral_Ioc_eq_integral_Io
o' (hy : μ {y} = 0) : ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem integral_Ioc_eq_integral_Ioo : ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  integral_Ioc_eq_integral_Ioo' <| measure_singleton y
/-
**MeasureTheory.integral_Ico_eq_integral_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_Ico_eq_integral_Ioo : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f 
t ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_Ico_eq_integral_Ioo'`：integral_Ico_eq_integral_Io
o' (hx : μ {x} = 0) : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem integral_Ico_eq_integral_Ioo : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ :=
  integral_Ico_eq_integral_Ioo' <| measure_singleton x
/-
**MeasureTheory.integral_Ico_eq_integral_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_Ico_eq_integral_Ioc : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioc x y, f 
t ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_Ico_eq_integral_Ioo`：integral_Ico_eq_integral_Ioo
 : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
· 使用定理 `MeasureTheory.integral_Ioc_eq_integral_Ioo`：integral_Ioc_eq_integral_Ioo
 : ∫ t in Ioc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
-/
theorem integral_Ico_eq_integral_Ioc : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioc x y, f t ∂μ := by
  rw [integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
/-
**MeasureTheory.integral_Icc_eq_integral_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_Icc_eq_integral_Ioo : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioo x y, f 
t ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_Icc_eq_integral_Ico`：integral_Icc_eq_integral_Ico
 : ∫ t in Icc x y, f t ∂μ = ∫ t in Ico x y, f t ∂μ
· 使用定理 `MeasureTheory.integral_Ico_eq_integral_Ioo`：integral_Ico_eq_integral_Ioo
 : ∫ t in Ico x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ
-/
theorem integral_Icc_eq_integral_Ioo : ∫ t in Icc x y, f t ∂μ = ∫ t in Ioo x y, f t ∂μ := by
  rw [integral_Icc_eq_integral_Ico, integral_Ico_eq_integral_Ioo]
/-
**MeasureTheory.integral_Iic_eq_integral_Iio** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_Iic_eq_integral_Iio : ∫ t in Iic x, f t ∂μ = ∫ t in Iio x, f t ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_Iic_eq_integral_Iio'`：integral_Iic_eq_integral_Ii
o' (hx : μ {x} = 0) : ∫ t in Iic x, f t ∂μ = ∫ t in Iio x, f t ∂μ
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem integral_Iic_eq_integral_Iio : ∫ t in Iic x, f t ∂μ = ∫ t in Iio x, f t ∂μ :=
  integral_Iic_eq_integral_Iio' <| measure_singleton x
/-
**MeasureTheory.integral_Ici_eq_integral_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：integral_Ici_eq_integral_Ioi : ∫ t in Ici x, f t ∂μ = ∫ t in Ioi x, f t ∂μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_Ici_eq_integral_Ioi'`：integral_Ici_eq_integral_Io
i' (hx : μ {x} = 0) : ∫ t in Ici x, f t ∂μ = ∫ t in Ioi x, f t ∂μ
· 使用定理 `MeasureTheory.NullSingletonClass.measure_singleton`：∀ {α : Type u_1} {m0
 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [self : MeasureTheory.NullSi
ngletonClass μ]   (x : α), μ {x} = 0
-/
theorem integral_Ici_eq_integral_Ioi : ∫ t in Ici x, f t ∂μ = ∫ t in Ioi x, f t ∂μ :=
  integral_Ici_eq_integral_Ioi' <| measure_singleton x

end PartialOrder

end NormedAddCommGroup

section Mono

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E]
    [IsOrderedAddMonoid E] [IsOrderedModule ℝ E]
    {μ : Measure X} {f g : X → E} {s t : Set X}

/-
**MeasureTheory.setIntegral_mono_set** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_mono_set [OrderClosedTopology E] (hfi : IntegrableOn f t μ) (h
f : 0 <=ᵐ[μ.restrict t] f) (hst : s <=ᵐ[μ] t) : ∫ x in s, f x ∂μ <= ∫ x in t, f 
x ∂μ
参数：hfi : IntegrableOn f t μ；hf : 0 <=ᵐ[μ.restrict t] f；hst : s <=ᵐ[μ] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_mono_measure`：integral_mono_measure [OrderClosedT
opology E] {f : α -> E} {ν : Measure α} (hle : μ <= ν) (hf : 0 <=ᵐ[ν] f) (hfi : 
Integrable f ν) : ∫ (a : …
· 使用定理 `MeasureTheory.Measure.restrict_mono_ae`：restrict_mono_ae (h : s <=ᵐ[μ] t
) : μ.restrict s <= μ.restrict t
-/
theorem setIntegral_mono_set [OrderClosedTopology E] (hfi : IntegrableOn f t μ)
    (hf : 0 ≤ᵐ[μ.restrict t] f) (hst : s ≤ᵐ[μ] t) :
    ∫ x in s, f x ∂μ ≤ ∫ x in t, f x ∂μ :=
  integral_mono_measure (Measure.restrict_mono_ae hst) hf hfi
/-
**MeasureTheory.setIntegral_le_integral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：setIntegral_le_integral [OrderClosedTopology E] (hfi : Integrable f μ) (hf
 : 0 <=ᵐ[μ] f) : ∫ x in s, f x ∂μ <= ∫ x, f x ∂μ
参数：hfi : Integrable f μ；hf : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_mono_measure`：integral_mono_measure [OrderClosedT
opology E] {f : α -> E} {ν : Measure α} (hle : μ <= ν) (hf : 0 <=ᵐ[ν] f) (hfi : 
Integrable f ν) : ∫ (a : …
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
-/
theorem setIntegral_le_integral [OrderClosedTopology E] (hfi : Integrable f μ) (hf : 0 ≤ᵐ[μ] f) :
    ∫ x in s, f x ∂μ ≤ ∫ x, f x ∂μ :=
  integral_mono_measure (Measure.restrict_le_self) hf hfi

variable [ClosedIciTopology E]

section
variable (hf : IntegrableOn f s μ) (hg : IntegrableOn g s μ)
include hf hg

/-
**MeasureTheory.setIntegral_mono_ae_restrict** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：setIntegral_mono_ae_restrict (h : f <=ᵐ[μ.restrict s] g) : ∫ x in s, f x ∂
μ <= ∫ x in s, g x ∂μ
参数：h : f <=ᵐ[μ.restrict s] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_mono_ae`：integral_mono_ae {f g : α -> E} (hf : In
tegrable f μ) (hg : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ x, f x ∂μ <= ∫ x, g x ∂
μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_def`：∀ {α : Type u_6} {G : Type u_7} [inst : Norm
edAddCommGroup G] [inst_1 : NormedSpace ℝ G] {x : MeasurableSpace α}   (μ : Meas
ureTheory.Measur…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem setIntegral_mono_ae_restrict (h : f ≤ᵐ[μ.restrict s] g) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ := by
  by_cases hE : CompleteSpace E
  · exact integral_mono_ae hf hg h
  · simp [integral, hE]
/-
**MeasureTheory.setIntegral_mono_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_mono_ae (h : f <=ᵐ[μ] g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂
μ
参数：h : f <=ᵐ[μ] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.setIntegral_mono_ae_restrict`：setIntegral_mono_ae_restrict
 (h : f <=ᵐ[μ.restrict s] g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
-/
theorem setIntegral_mono_ae (h : f ≤ᵐ[μ] g) : ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ :=
  setIntegral_mono_ae_restrict hf hg (ae_restrict_of_ae h)
/-
**MeasureTheory.setIntegral_mono_on** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_mono_on (hs : MeasurableSet s) (h : forall x in s, f x <= g x)
 : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : forall x in s, f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_mono_ae_restrict`：setIntegral_mono_ae_restrict
 (h : f <=ᵐ[μ.restrict s] g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_eq`：ae_restrict_eq (hs : MeasurableSet s) : ae
 (μ.restrict s) = ae μ ⊓ 𝓟 s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
-/
theorem setIntegral_mono_on (hs : MeasurableSet s) (h : ∀ x ∈ s, f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ :=
  setIntegral_mono_ae_restrict hf hg
    (by simp [hs, EventuallyLE, eventually_inf_principal, ae_of_all _ h])
/-
**MeasureTheory.setIntegral_mono_on_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：setIntegral_mono_on_ae (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s ->
 f x <= g x) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : forallᵐ x ∂μ, x in s -> f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.setIntegral_mono_ae_restrict`：setIntegral_mono_ae_restrict
 (h : f <=ᵐ[μ.restrict s] g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyLE.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE β] 
(l : Filter α) (f g : α → β), (f ≤ᶠ[l] g) = ∀ᶠ (x : α) in l, f x ≤ g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
-/
theorem setIntegral_mono_on_ae (hs : MeasurableSet s) (h : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ := by
  refine setIntegral_mono_ae_restrict hf hg ?_; rwa [EventuallyLE, ae_restrict_iff' hs]
/-
**MeasureTheory.setIntegral_mono_on_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：setIntegral_mono_on_ae (hs : MeasurableSet s) (h : forallᵐ x ∂μ, x in s ->
 f x <= g x) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : forallᵐ x ∂μ, x in s -> f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.setIntegral_mono_ae_restrict`：setIntegral_mono_ae_restrict
 (h : f <=ᵐ[μ.restrict s] g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyLE.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE β] 
(l : Filter α) (f g : α → β), (f ≤ᶠ[l] g) = ∀ᶠ (x : α) in l, f x ≤ g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
-/
lemma setIntegral_mono_on_ae₀ (hs : NullMeasurableSet s μ) (h : ∀ᵐ x ∂μ, x ∈ s → f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ := by
  rw [setIntegral_congr_set hs.toMeasurable_ae_eq.symm,
    setIntegral_congr_set hs.toMeasurable_ae_eq.symm]
  refine setIntegral_mono_on_ae ?_ ?_ ?_ ?_
  · rwa [integrableOn_congr_set_ae hs.toMeasurable_ae_eq]
  · rwa [integrableOn_congr_set_ae hs.toMeasurable_ae_eq]
  · exact measurableSet_toMeasurable μ s
  · filter_upwards [hs.toMeasurable_ae_eq.mem_iff, h] with x hx h
    rwa [hx]

@[gcongr high] -- higher priority than `integral_mono`
-- this lemma is better because it also gives the `x ∈ s` hypothesis
/-
**MeasureTheory.setIntegral_mono_on** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_mono_on (hs : MeasurableSet s) (h : forall x in s, f x <= g x)
 : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
参数：hs : MeasurableSet s；h : forall x in s, f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_mono_ae_restrict`：setIntegral_mono_ae_restrict
 (h : f <=ᵐ[μ.restrict s] g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_restrict_eq`：ae_restrict_eq (hs : MeasurableSet s) : ae
 (μ.restrict s) = ae μ ⊓ 𝓟 s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
-/
lemma setIntegral_mono_on₀ (hs : NullMeasurableSet s μ) (h : ∀ x ∈ s, f x ≤ g x) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ :=
  setIntegral_mono_on_ae₀ hf hg hs (Eventually.of_forall h)
/-
**MeasureTheory.setIntegral_mono** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_mono (h : f <= g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
参数：h : f <= g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_mono`：integral_mono {f g : α -> E} (hf : Integrab
le f μ) (hg : Integrable g μ) (h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
-/
theorem setIntegral_mono (h : f ≤ g) : ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ :=
  integral_mono hf hg h

end

/-
**MeasureTheory.setIntegral_ge_of_const_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：setIntegral_ge_of_const_le [CompleteSpace E] {c : E} (hs : MeasurableSet s
) (hμs : μ s != ∞) (hf : forall x in s, c <= f x) (hfint : IntegrableOn (fun x :
 X => f x) s μ) : μ.real s • c <= ∫ x in s, f x ∂μ
参数：hs : MeasurableSet s；hμs : μ s != ∞；hf : forall x in s, c <= f x；hfint : Inte
grableOn (fun x : X => f x) s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_const`：setIntegral_const [CompleteSpace E] (c 
: E) : ∫ _ in s, c ∂μ = μ.real s • c
· 使用定理 `MeasureTheory.setIntegral_mono_on`：setIntegral_mono_on (hs : MeasurableS
et s) (h : forall x in s, f x <= g x) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
-/
theorem setIntegral_ge_of_const_le [CompleteSpace E] {c : E} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (hf : ∀ x ∈ s, c ≤ f x) (hfint : IntegrableOn (fun x : X => f x) s μ) :
    μ.real s • c ≤ ∫ x in s, f x ∂μ := by
  rw [← setIntegral_const c]
  exact setIntegral_mono_on (integrableOn_const hμs) hfint hs hf
/-
**MeasureTheory.setIntegral_ge_of_const_le_real** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：setIntegral_ge_of_const_le_real {f : X -> Real} {c : Real} (hs : Measurabl
eSet s) (hμs : μ s != ∞) (hf : forall x in s, c <= f x) (hfint : IntegrableOn (f
un x : X => f x) s μ) : c * μ.real s <= ∫ x in s, f x ∂μ
参数：hs : MeasurableSet s；hμs : μ s != ∞；hf : forall x in s, c <= f x；hfint : Inte
grableOn (fun x : X => f x) s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `MeasureTheory.setIntegral_ge_of_const_le`：setIntegral_ge_of_const_le [Co
mpleteSpace E] {c : E} (hs : MeasurableSet s) (hμs : μ s != ∞) (hf : forall x in
 s, c <= f x) (hfint : Integra…
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem setIntegral_ge_of_const_le_real {f : X → ℝ} {c : ℝ} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (hf : ∀ x ∈ s, c ≤ f x) (hfint : IntegrableOn (fun x : X => f x) s μ) :
    c * μ.real s ≤ ∫ x in s, f x ∂μ := by
  simpa [mul_comm] using setIntegral_ge_of_const_le hs hμs hf hfint

end Mono

section Nonneg

variable {μ : Measure X} {f : X → ℝ} {s : Set X}

/-
**MeasureTheory.setIntegral_nonneg_of_ae_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：setIntegral_nonneg_of_ae_restrict (hf : 0 <=ᵐ[μ.restrict s] f) : 0 <= ∫ x 
in s, f x ∂μ
参数：hf : 0 <=ᵐ[μ.restrict s] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem setIntegral_nonneg_of_ae_restrict (hf : 0 ≤ᵐ[μ.restrict s] f) : 0 ≤ ∫ x in s, f x ∂μ :=
  integral_nonneg_of_ae hf
/-
**MeasureTheory.setIntegral_nonneg_of_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setIntegral_nonneg_of_ae (hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x in s, f x ∂μ
参数：hf : 0 <=ᵐ[μ] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.setIntegral_nonneg_of_ae_restrict`：setIntegral_nonneg_of_a
e_restrict (hf : 0 <=ᵐ[μ.restrict s] f) : 0 <= ∫ x in s, f x ∂μ
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
-/
theorem setIntegral_nonneg_of_ae (hf : 0 ≤ᵐ[μ] f) : 0 ≤ ∫ x in s, f x ∂μ :=
  setIntegral_nonneg_of_ae_restrict (ae_restrict_of_ae hf)
/-
**MeasureTheory.setIntegral_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_nonneg (hs : MeasurableSet s) (hf : forall x, x in s -> 0 <= f
 x) : 0 <= ∫ x in s, f x ∂μ
参数：hs : MeasurableSet s；hf : forall x, x in s -> 0 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_nonneg_of_ae_restrict`：setIntegral_nonneg_of_a
e_restrict (hf : 0 <=ᵐ[μ.restrict s] f) : 0 <= ∫ x in s, f x ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
-/
theorem setIntegral_nonneg (hs : MeasurableSet s) (hf : ∀ x, x ∈ s → 0 ≤ f x) :
    0 ≤ ∫ x in s, f x ∂μ :=
  setIntegral_nonneg_of_ae_restrict ((ae_restrict_iff' hs).mpr (ae_of_all μ hf))
/-
**MeasureTheory.setIntegral_nonneg_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_nonneg_ae (hs : MeasurableSet s) (hf : forallᵐ x ∂μ, x in s ->
 0 <= f x) : 0 <= ∫ x in s, f x ∂μ
参数：hs : MeasurableSet s；hf : forallᵐ x ∂μ, x in s -> 0 <= f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.setIntegral_nonneg_of_ae_restrict`：setIntegral_nonneg_of_a
e_restrict (hf : 0 <=ᵐ[μ.restrict s] f) : 0 <= ∫ x in s, f x ∂μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyLE.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE β] 
(l : Filter α) (f g : α → β), (f ≤ᶠ[l] g) = ∀ᶠ (x : α) in l, f x ≤ g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
-/
theorem setIntegral_nonneg_ae (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, x ∈ s → 0 ≤ f x) :
    0 ≤ ∫ x in s, f x ∂μ :=
  setIntegral_nonneg_of_ae_restrict <| by rwa [EventuallyLE, ae_restrict_iff' hs]
/-
**MeasureTheory.setIntegral_le_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_le_nonneg {s : Set X} (hs : MeasurableSet s) (hf : StronglyMea
surable f) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ <= ∫ x in {y | 0 <= f y}, f
 x ∂μ
参数：hs : MeasurableSet s；hf : StronglyMeasurable f；hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_le`：measurableSet_le (hf 
: StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSet[m] {a 
| f a <= g a}
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用引理 `MeasureTheory.integral_mono`：integral_mono {f g : α -> E} (hf : Integrab
le f μ) (hg : Integrable g μ) (h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用引理 `Set.indicator_le_indicator_nonneg`：indicator_le_indicator_nonneg (s : Se
t α) (f : α -> M) : s.indicator f <= {a | 0 <= f a}.indicator f
-/
theorem setIntegral_le_nonneg {s : Set X} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hfi : Integrable f μ) : ∫ x in s, f x ∂μ ≤ ∫ x in {y | 0 ≤ f y}, f x ∂μ := by
  rw [← integral_indicator hs, ←
    integral_indicator (stronglyMeasurable_const.measurableSet_le hf)]
  exact
    integral_mono (hfi.indicator hs)
      (hfi.indicator (stronglyMeasurable_const.measurableSet_le hf))
      (indicator_le_indicator_nonneg s f)
/-
**MeasureTheory.setIntegral_nonpos_of_ae_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory`。
形式化陈述：setIntegral_nonpos_of_ae_restrict (hf : f <=ᵐ[μ.restrict s] 0) : ∫ x in s,
 f x ∂μ <= 0
参数：hf : f <=ᵐ[μ.restrict s] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `MeasureTheory.integral_nonpos_of_ae`：integral_nonpos_of_ae {f : α -> E} 
(hf : f <=ᵐ[μ] 0) : ∫ x, f x ∂μ <= 0
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
-/
theorem setIntegral_nonpos_of_ae_restrict (hf : f ≤ᵐ[μ.restrict s] 0) : ∫ x in s, f x ∂μ ≤ 0 :=
  integral_nonpos_of_ae hf
/-
**MeasureTheory.setIntegral_nonpos_of_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：setIntegral_nonpos_of_ae (hf : f <=ᵐ[μ] 0) : ∫ x in s, f x ∂μ <= 0
参数：hf : f <=ᵐ[μ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.setIntegral_nonpos_of_ae_restrict`：setIntegral_nonpos_of_a
e_restrict (hf : f <=ᵐ[μ.restrict s] 0) : ∫ x in s, f x ∂μ <= 0
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
-/
theorem setIntegral_nonpos_of_ae (hf : f ≤ᵐ[μ] 0) : ∫ x in s, f x ∂μ ≤ 0 :=
  setIntegral_nonpos_of_ae_restrict (ae_restrict_of_ae hf)
/-
**MeasureTheory.setIntegral_nonpos_ae** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_nonpos_ae (hs : MeasurableSet s) (hf : forallᵐ x ∂μ, x in s ->
 f x <= 0) : ∫ x in s, f x ∂μ <= 0
参数：hs : MeasurableSet s；hf : forallᵐ x ∂μ, x in s -> f x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.setIntegral_nonpos_of_ae_restrict`：setIntegral_nonpos_of_a
e_restrict (hf : f <=ᵐ[μ.restrict s] 0) : ∫ x in s, f x ∂μ <= 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyLE.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE β] 
(l : Filter α) (f g : α → β), (f ≤ᶠ[l] g) = ∀ᶠ (x : α) in l, f x ≤ g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
-/
theorem setIntegral_nonpos_ae (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, x ∈ s → f x ≤ 0) :
    ∫ x in s, f x ∂μ ≤ 0 :=
  setIntegral_nonpos_of_ae_restrict <| by rwa [EventuallyLE, ae_restrict_iff' hs]
/-
**MeasureTheory.setIntegral_nonpos** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_nonpos (hs : MeasurableSet s) (hf : forall x, x in s -> f x <=
 0) : ∫ x in s, f x ∂μ <= 0
参数：hs : MeasurableSet s；hf : forall x, x in s -> f x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.setIntegral_nonpos_ae`：setIntegral_nonpos_ae (hs : Measura
bleSet s) (hf : forallᵐ x ∂μ, x in s -> f x <= 0) : ∫ x in s, f x ∂μ <= 0
· 使用定理 `MeasureTheory.ae_of_all`：ae_of_all {p : α -> Prop} (μ : F) : (forall a, 
p a) -> forallᵐ a ∂μ, p a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
-/
theorem setIntegral_nonpos (hs : MeasurableSet s) (hf : ∀ x, x ∈ s → f x ≤ 0) :
    ∫ x in s, f x ∂μ ≤ 0 :=
  setIntegral_nonpos_ae hs <| ae_of_all μ hf
/-
**MeasureTheory.setIntegral_nonpos_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：setIntegral_nonpos_le {s : Set X} (hs : MeasurableSet s) (hf : StronglyMea
surable f) (hfi : Integrable f μ) : ∫ x in {y | f y <= 0}, f x ∂μ <= ∫ x in s, f
 x ∂μ
参数：hs : MeasurableSet s；hf : StronglyMeasurable f；hfi : Integrable f μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_indicator`：integral_indicator (hs : MeasurableSet
 s) : ∫ x, indicator s f x ∂μ = ∫ x in s, f x ∂μ
· 使用引理 `MeasureTheory.StronglyMeasurable.measurableSet_le`：measurableSet_le (hf 
: StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) : MeasurableSet[m] {a 
| f a <= g a}
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.stronglyMeasurable_const`：stronglyMeasurable_const {b : β}
 : StronglyMeasurable fun _ : α => b
· 使用引理 `MeasureTheory.integral_mono`：integral_mono {f g : α -> E} (hf : Integrab
le f μ) (hg : Integrable g μ) (h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `MeasureTheory.Integrable.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {mα
 : MeasurableSpace α} {s : Set α} {μ : MeasureTheory.Measure α}   [inst : Topolo
gicalSpace ε'] [inst_1 :…
· 使用引理 `Set.indicator_nonpos_le_indicator`：indicator_nonpos_le_indicator (s : Se
t α) (f : α -> M) : {a | f a <= 0}.indicator f <= s.indicator f
-/
theorem setIntegral_nonpos_le {s : Set X} (hs : MeasurableSet s) (hf : StronglyMeasurable f)
    (hfi : Integrable f μ) : ∫ x in {y | f y ≤ 0}, f x ∂μ ≤ ∫ x in s, f x ∂μ := by
  rw [← integral_indicator hs, ←
    integral_indicator (hf.measurableSet_le stronglyMeasurable_const)]
  exact
    integral_mono (hfi.indicator (hf.measurableSet_le stronglyMeasurable_const))
      (hfi.indicator hs) (indicator_nonpos_le_indicator s f)
/-
**MeasureTheory.Integrable.measure_le_integral** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.Integrable`。
形式化陈述：∀ {X : Type u_1} {mX : MeasurableSpace X} {μ : MeasureTheory.Measure X} {f
 : X → ℝ},   MeasureTheory.Integrable f μ →     0 ≤ᵐ[μ] f → ∀ {s : Set X}, (∀ x 
∈ s, 1 ≤ f x) → μ s ≤ ENNReal.ofReal (∫ (x : X), f x ∂μ)
参数：∀ x ∈ s, 1 ≤ f x；∫ (x : X), f x ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用引理 `MeasureTheory.meas_le_lintegral₀`：meas_le_lintegral₀ {f : α -> Real>=0∞}
 (hf : AEMeasurable f μ) {s : Set α} (hs : forall x in s, 1 <= f x) : μ s <= ∫⁻ 
a, f a ∂μ
· 使用定理 `Measurable.comp_aemeasurable`：Measurable.comp_aemeasurable [MeasurableSp
ace δ] {f : α -> δ} {g : δ -> β} (hg : Measurable g) (hf : AEMeasurable f μ) : A
EMeasurable (g ∘ f…
· 使用定理 `Continuous.measurable`：Continuous.measurable {f : α -> γ} (hf : Continuo
us f) : Measurable f
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `ENNReal.continuous_ofReal`：continuous_ofReal : Continuous ENNReal.ofReal
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_one`：ENNReal.ofReal 1 = 1
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
-/
lemma Integrable.measure_le_integral {f : X → ℝ} (f_int : Integrable f μ) (f_nonneg : 0 ≤ᵐ[μ] f)
    {s : Set X} (hs : ∀ x ∈ s, 1 ≤ f x) :
    μ s ≤ ENNReal.ofReal (∫ x, f x ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal f_int f_nonneg]
  apply meas_le_lintegral₀
  · exact ENNReal.continuous_ofReal.measurable.comp_aemeasurable f_int.1.aemeasurable
  · intro x hx
    simpa using ENNReal.ofReal_le_ofReal (hs x hx)
/-
**MeasureTheory.integral_le_measure** 是 Mathlib 中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：integral_le_measure {f : X -> Real} {s : Set X} (hs : forall x in s, f x <
= 1) (h's : forall x in sᶜ, f x <= 0) : ENNReal.ofReal (∫ x, f x ∂μ) <= μ s
参数：hs : forall x in s, f x <= 1；h's : forall x in sᶜ, f x <= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Integrable.pos_part`：∀ {α : Type u_1} {m : MeasurableSpace
 α} {μ : MeasureTheory.Measure α} {f : α → ℝ},   MeasureTheory.Integrable f μ → 
MeasureTheory.Integrabl…
· 使用定理 `ENNReal.ofReal_le_ofReal`：ofReal_le_ofReal {p q : Real} (h : p <= q) : E
NNReal.ofReal p <= ENNReal.ofReal q
· 使用引理 `MeasureTheory.integral_mono`：integral_mono {f g : α -> E} (hf : Integrab
le f μ) (hg : Integrable g μ) (h : f <= g) : ∫ x, f x ∂μ <= ∫ x, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ofReal_integral_eq_lintegral_ofReal`：ofReal_integral_eq_li
ntegral_ofReal {f : α -> Real} (hfi : Integrable f μ) (f_nn : 0 <=ᵐ[μ] f) : ENNR
eal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNRea…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `MeasureTheory.lintegral_le_meas`：lintegral_le_meas {s : Set α} {f : α ->
 Real>=0∞} (hf : forall a, f a <= 1) (h'f : forall a in sᶜ, f a = 0) : ∫⁻ a, f a
 ∂μ <= μ s
· 使用定理 `ENNReal.ofReal_le_of_le_toReal`：ofReal_le_of_le_toReal {a : Real} {b : R
eal>=0∞} (h : a <= ENNReal.toReal b) : ENNReal.ofReal a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.ofReal_max`：∀ (x y : ℝ), ENNReal.ofReal (max x y) = max (ENNReal
.ofReal x) (ENNReal.ofReal y)
· 使用定理 `ENNReal.ofReal_zero`：ENNReal.ofReal 0 = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
-/
lemma integral_le_measure {f : X → ℝ} {s : Set X}
    (hs : ∀ x ∈ s, f x ≤ 1) (h's : ∀ x ∈ sᶜ, f x ≤ 0) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ μ s := by
  by_cases H : Integrable f μ; swap
  · simp [integral_undef H]
  let g x := max (f x) 0
  have g_int : Integrable g μ := H.pos_part
  have : ENNReal.ofReal (∫ x, f x ∂μ) ≤ ENNReal.ofReal (∫ x, g x ∂μ) := by
    apply ENNReal.ofReal_le_ofReal
    exact integral_mono H g_int (fun x ↦ le_max_left _ _)
  apply this.trans
  rw [ofReal_integral_eq_lintegral_ofReal g_int (Eventually.of_forall (fun x ↦ le_max_right _ _))]
  apply lintegral_le_meas
  · intro x
    apply ENNReal.ofReal_le_of_le_toReal
    by_cases H : x ∈ s
    · simpa [g] using hs x H
    · apply le_trans _ zero_le_one
      simpa [g] using h's x H
  · intro x hx
    simpa [g] using h's x hx
/-
**MeasureTheory.setIntegral_mono_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `MeasureThe
ory`。
形式化陈述：setIntegral_mono_of_nonneg {g : X -> Real} (hf : forall x in s, 0 <= f x) 
(h : forall x in s, f x <= g x) (hg : IntegrableOn g s μ) : ∫ x in s, f x ∂μ <= 
∫ x in s, g x ∂μ
参数：hf : forall x in s, 0 <= f x；h : forall x in s, f x <= g x；hg : IntegrableOn 
g s μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.integral_mono_of_nonneg`：integral_mono_of_nonneg {f g : α 
-> E} (hf : 0 <=ᵐ[μ] f) (hgi : Integrable g μ) (h : f <=ᵐ[μ] g) : ∫ a, f a ∂μ <=
 ∫ a, g a ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_iff₀`：ae_restrict_iff₀ {p : α -> Prop} (hp : N
ullMeasurableSet { x | p x } (μ.restrict s)) : (forallᵐ x ∂μ.restrict s, p x) ↔ 
forallᵐ x ∂μ, x in s…
· 使用定理 `nullMeasurableSet_le`：nullMeasurableSet_le [SecondCountableTopology α] [
OrderClosedTopology α] {μ : Measure δ} {f g : δ -> α} (hf : AEMeasurable f μ) (h
g : AEMeas…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `MeasureTheory.Integrable.aemeasurable`：∀ {α : Type u_1} {ε : Type u_5} {
m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]
   [inst_1 : ContinuousENor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_non_aestronglyMeasurable`：integral_non_aestrongly
Measurable {f : α -> G} (h : ¬AEStronglyMeasurable f μ) : ∫ a, f a ∂μ = 0
· 使用引理 `MeasureTheory.integral_nonneg_of_ae`：integral_nonneg_of_ae {f : α -> E} 
(hf : 0 <=ᵐ[μ] f) : 0 <= ∫ x, f x ∂μ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma setIntegral_mono_of_nonneg {g : X → ℝ} (hf : ∀ x ∈ s, 0 ≤ f x)
    (h : ∀ x ∈ s, f x ≤ g x) (hg : IntegrableOn g s μ) :
    ∫ x in s, f x ∂μ ≤ ∫ x in s, g x ∂μ := by
  by_cases h'f : AEStronglyMeasurable f (μ.restrict s); swap
  · rw [integral_non_aestronglyMeasurable h'f]
    apply integral_nonneg_of_ae
    apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using (hf x hx).trans (h x hx)
    · exact nullMeasurableSet_le aemeasurable_const hg.aemeasurable
  refine integral_mono_of_nonneg ?_ hg ?_
  · apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using hf x hx
    · exact nullMeasurableSet_le aemeasurable_const h'f.aemeasurable
  · apply (ae_restrict_iff₀ ?_).2
    · filter_upwards with x hx using h x hx
    · exact nullMeasurableSet_le h'f.aemeasurable hg.aemeasurable

end Nonneg

section IntegrableUnion

variable {ι : Type*} [Countable ι] {μ : Measure X} [NormedAddCommGroup E]

/-
**MeasureTheory.integrableOn_iUnion_of_summable_integral_norm** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_iUnion_of_summable_integral_norm {f : X -> E} {s : ι -> Set X
} (hi : forall i : ι, IntegrableOn f (s i) μ) (h : Summable fun i : ι => ∫ x : X
 in s i, ‖f x‖ ∂μ) : IntegrableOn f (iUnion s) μ
参数：hi : forall i : ι, IntegrableOn f (s i) μ；h : Summable fun i : ι => ∫ x : X i
n s i, ‖f x‖ ∂μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEStronglyMeasurable.iUnion`：∀ {α : Type u_1} {β : Type u_
2} {ι : Type u_4} [Countable ι] [inst : TopologicalSpace β] {m₀ : MeasurableSpac
e α}   {μ : MeasureTheory.Measu…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.lintegral_iUnion_le`：lintegral_iUnion_le [Countable β] (s 
: β -> Set α) (f : α -> Real>=0∞) : ∫⁻ a in ⋃ i, s i, f a ∂μ <= ∑' i, ∫⁻ a in s 
i, f a ∂μ
· 使用定理 `MeasureTheory.lintegral_coe_eq_integral`：lintegral_coe_eq_integral (f : 
α -> Real>=0) (hfi : Integrable (fun x => (f x : Real)) μ) : ∫⁻ a, f a ∂μ = ENNR
eal.ofReal (∫ a, f a ∂μ)
· 使用定理 `MeasureTheory.Integrable.norm`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f 
: α → β}, MeasureTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.summable_coe`：summable_coe {f : α -> Real>=0} : (Summable (fun a 
=> (f a : Real)) L) ↔ Summable f L
· 使用定理 `ENNReal.tsum_coe_eq`：∀ {α : Type u_1} {r : NNReal} {f : α → NNReal}, Has
Sum f r → ∑' (a : α), ↑(f a) = ↑r
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ENNReal.coe_nnreal_eq`：coe_nnreal_eq (r : Real>=0) : (r : Real>=0∞) = EN
NReal.ofReal r
· 使用定理 `ENNReal.ofReal_lt_top`：∀ {r : ℝ}, ENNReal.ofReal r < ⊤
-/
theorem integrableOn_iUnion_of_summable_integral_norm {f : X → E} {s : ι → Set X}
    (hi : ∀ i : ι, IntegrableOn f (s i) μ)
    (h : Summable fun i : ι => ∫ x : X in s i, ‖f x‖ ∂μ) : IntegrableOn f (iUnion s) μ := by
  refine ⟨AEStronglyMeasurable.iUnion fun i => (hi i).1, (lintegral_iUnion_le _ _).trans_lt ?_⟩
  have B := fun i => lintegral_coe_eq_integral (fun x : X => ‖f x‖₊) (hi i).norm
  simp_rw [enorm_eq_nnnorm, tsum_congr B]
  have S' : Summable fun i : ι =>
      (NNReal.mk (∫ x : X in s i, ‖f x‖₊ ∂μ) (integral_nonneg fun x => NNReal.coe_nonneg _)) := by
    rw [← NNReal.summable_coe]; exact h
  have S'' := ENNReal.tsum_coe_eq S'.hasSum
  simp_rw [ENNReal.coe_nnreal_eq, NNReal.coe_mk, coe_nnnorm] at S''
  convert! ENNReal.ofReal_lt_top

variable [TopologicalSpace X] [BorelSpace X] [T2Space X] [IsLocallyFiniteMeasure μ]

/-- If `s` is a countable family of compact sets, `f` is a continuous function, and the sequence
`‖f.restrict (s i)‖ * μ (s i)` is summable, then `f` is integrable on the union of the `s i`. -/
/-
**MeasureTheory.integrableOn_iUnion_of_summable_norm_restrict** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：integrableOn_iUnion_of_summable_norm_restrict {f : C(X, E)} {s : ι -> Comp
acts X} (hf : Summable fun i : ι => ‖f.restrict (s i)‖ * μ.real (s i)) : Integra
bleOn f (⋃ i : ι, s i) μ
参数：X, E；hf : Summable fun i : ι => ‖f.restrict (s i)‖ * μ.real (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.instCompactSpaceElemCoeCompacts`：∀ {X : Type u_4} [inst : 
TopologicalSpace X] (K : TopologicalSpace.Compacts X), CompactSpace ↑↑K
· 使用定理 `MeasureTheory.integrableOn_iUnion_of_summable_integral_norm`：integrableO
n_iUnion_of_summable_integral_norm {f : X -> E} {s : ι -> Set X} (hi : forall i 
: ι, IntegrableOn f (s i) μ) (h : Summable fun i …
· 使用定理 `ContinuousOn.integrableOn_compact`：ContinuousOn.integrableOn_compact [T2
Space X] (hK : IsCompact K) (hf : ContinuousOn f K) : IntegrableOn f K μ
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
· 使用定理 `TopologicalSpace.Compacts.isCompact`：∀ {α : Type u_1} [inst : Topologica
lSpace α] (s : TopologicalSpace.Compacts α), IsCompact ↑s
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `MeasureTheory.norm_setIntegral_le_of_norm_le_const`：norm_setIntegral_le_
of_norm_le_const {C : Real} (hs : μ s < ∞) (hC : forall x in s, ‖f x‖ <= C) : ‖∫
 x in s, f x ∂μ‖ <= C * μ.real s
· 使用定理 `IsCompact.measure_lt_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖

--- 原说明 ---
If `s` is a countable family of compact sets, `f` is a continuous function, and 
the sequence
`‖f.restrict (s i)‖ * μ (s i)` is summable, then `f` is integrable on the union 
of the `s i`.
-/
theorem integrableOn_iUnion_of_summable_norm_restrict {f : C(X, E)} {s : ι → Compacts X}
    (hf : Summable fun i : ι => ‖f.restrict (s i)‖ * μ.real (s i)) :
    IntegrableOn f (⋃ i : ι, s i) μ := by
  refine
    integrableOn_iUnion_of_summable_integral_norm
      (fun i => (map_continuous f).continuousOn.integrableOn_compact (s i).isCompact)
      (.of_nonneg_of_le (fun ι => integral_nonneg fun x => norm_nonneg _) (fun i => ?_) hf)
  rw [← (Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _) : ‖_‖ = ∫ x in s i, ‖f x‖ ∂μ)]
  exact
    norm_setIntegral_le_of_norm_le_const (s i).isCompact.measure_lt_top
      fun x hx => (norm_norm (f x)).symm ▸ (f.restrict (s i : Set X)).norm_coe_le_norm ⟨x, hx⟩

/-- If `s` is a countable family of compact sets covering `X`, `f` is a continuous function, and
the sequence `‖f.restrict (s i)‖ * μ (s i)` is summable, then `f` is integrable. -/
/-
**MeasureTheory.integrable_of_summable_norm_restrict** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：integrable_of_summable_norm_restrict {f : C(X, E)} {s : ι -> Compacts X} (
hf : Summable fun i : ι => ‖f.restrict (s i)‖ * μ.real (s i)) (hs : ⋃ i : ι, ↑(s
 i) = (univ : Set X)) : Integrable f μ
参数：X, E；hf : Summable fun i : ι => ‖f.restrict (s i)‖ * μ.real (s i)；hs : ⋃ i : 
ι, ↑(s i) = (univ : Set X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.instCompactSpaceElemCoeCompacts`：∀ {X : Type u_4} [inst : 
TopologicalSpace X] (K : TopologicalSpace.Compacts X), CompactSpace ↑↑K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integrableOn_iUnion_of_summable_norm_restrict`：integrableO
n_iUnion_of_summable_norm_restrict {f : C(X, E)} {s : ι -> Compacts X} (hf : Sum
mable fun i : ι => ‖f.restrict (s i)‖ * μ.real (s…

--- 原说明 ---
If `s` is a countable family of compact sets covering `X`, `f` is a continuous f
unction, and
the sequence `‖f.restrict (s i)‖ * μ (s i)` is summable, then `f` is integrable.
-/
theorem integrable_of_summable_norm_restrict {f : C(X, E)} {s : ι → Compacts X}
    (hf : Summable fun i : ι => ‖f.restrict (s i)‖ * μ.real (s i))
    (hs : ⋃ i : ι, ↑(s i) = (univ : Set X)) : Integrable f μ := by
  simpa only [hs, integrableOn_univ] using integrableOn_iUnion_of_summable_norm_restrict hf

end IntegrableUnion

/-! ### Continuity of the set integral

We prove that for any set `s`, the function
`fun f : X →₁[μ] E => ∫ x in s, f x ∂μ` is continuous. -/

section ContinuousSetIntegral

variable [NormedAddCommGroup E]
  {𝕜 : Type*} [NormedRing 𝕜] [NormedAddCommGroup F] [Module 𝕜 F] [IsBoundedSMul 𝕜 F]
  {p : ℝ≥0∞} {μ : Measure X}

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memLp f).restrict s).toLp f`. This map is additive. -/
/-
**MeasureTheory.Lp_toLp_restrict_add** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Lp_toLp_restrict_add (f g : Lp E p μ) (s : Set X) : ((Lp.memLp (f + g)).re
strict s).toLp (⇑(f + g)) = ((Lp.memLp f).restrict s).toLp f + ((Lp.memLp g).res
trict s).toLp g
参数：f g : Lp E p μ；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `MeasureTheory.MemLp.restrict`：∀ {α : Type u_1} {m0 : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topological
Space ε] [inst_1 :…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Lp.coeFn_add`：coeFn_add (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] 
f + g
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i

--- 原说明 ---
For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memLp f).restrict s).toLp f`. This map is additive.
-/
theorem Lp_toLp_restrict_add (f g : Lp E p μ) (s : Set X) :
    ((Lp.memLp (f + g)).restrict s).toLp (⇑(f + g)) =
      ((Lp.memLp f).restrict s).toLp f + ((Lp.memLp g).restrict s).toLp g := by
  ext1
  refine (ae_restrict_of_ae (Lp.coeFn_add f g)).mp ?_
  refine
    (Lp.coeFn_add (MemLp.toLp f ((Lp.memLp f).restrict s))
          (MemLp.toLp g ((Lp.memLp g).restrict s))).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp f).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp g).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp (f + g)).restrict s)).mono fun x hx1 hx2 hx3 hx4 hx5 => ?_
  rw [hx4, hx1, Pi.add_apply, hx2, hx3, hx5, Pi.add_apply]

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memLp f).restrict s).toLp f`. This map commutes with scalar multiplication. -/
/-
**MeasureTheory.Lp_toLp_restrict_smul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：Lp_toLp_restrict_smul (c : 𝕜) (f : Lp F p μ) (s : Set X) : ((Lp.memLp (c •
 f)).restrict s).toLp (⇑(c • f)) = c • ((Lp.memLp f).restrict s).toLp f
参数：c : 𝕜；f : Lp F p μ；s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.Lp.ext`：ext {f g : Lp E p μ} (h : f =ᵐ[μ] g) : f = g
· 使用定理 `MeasureTheory.MemLp.restrict`：∀ {α : Type u_1} {m0 : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topological
Space ε] [inst_1 :…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_of_ae`：ae_restrict_of_ae {s : Set α} {p : α ->
 Prop} (h : forallᵐ x ∂μ, p x) : forallᵐ x ∂μ.restrict s, p x
· 使用定理 `MeasureTheory.Lp.coeFn_smul`：coeFn_smul (c : 𝕜) (f : Lp E p μ) : ⇑(c • f
) =ᵐ[μ] c • ⇑f
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memLp f).restrict s).toLp f`. This map commutes with scalar multiplication.
-/
theorem Lp_toLp_restrict_smul (c : 𝕜) (f : Lp F p μ) (s : Set X) :
    ((Lp.memLp (c • f)).restrict s).toLp (⇑(c • f)) = c • ((Lp.memLp f).restrict s).toLp f := by
  ext1
  refine (ae_restrict_of_ae (Lp.coeFn_smul c f)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp f).restrict s)).mp ?_
  refine (MemLp.coeFn_toLp ((Lp.memLp (c • f)).restrict s)).mp ?_
  refine
    (Lp.coeFn_smul c (MemLp.toLp f ((Lp.memLp f).restrict s))).mono fun x hx1 hx2 hx3 hx4 => ?_
  simp only [hx2, hx1, hx3, hx4, Pi.smul_apply]

/-- For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memLp f).restrict s).toLp f`. This map is non-expansive. -/
/-
**MeasureTheory.norm_Lp_toLp_restrict_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y`。
形式化陈述：norm_Lp_toLp_restrict_le (s : Set X) (f : Lp E p μ) : ‖((Lp.memLp f).restr
ict s).toLp f‖ <= ‖f‖
参数：s : Set X；f : Lp E p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.restrict`：∀ {α : Type u_1} {m0 : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topological
Space ε] [inst_1 :…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.Lp.norm_def`：norm_def (f : Lp E p μ) : ‖f‖ = ENNReal.toRea
l (eLpNorm f p μ)
· 使用定理 `MeasureTheory.eLpNorm_congr_ae`：eLpNorm_congr_ae {f g : α -> ε} (hfg : f
 =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `ENNReal.toReal_mono`：toReal_mono (hb : b != ∞) (h : a <= b) : a.toReal <
= b.toReal
· 使用定理 `MeasureTheory.Lp.eLpNorm_ne_top`：eLpNorm_ne_top (f : Lp E p μ) : eLpNorm
 f p μ != ∞
· 使用定理 `MeasureTheory.eLpNorm_mono_measure`：eLpNorm_mono_measure (f : α -> ε) (h
μν : ν <= μ) : eLpNorm f p ν <= eLpNorm f p μ
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ

--- 原说明 ---
For `f : Lp E p μ`, we can define an element of `Lp E p (μ.restrict s)` by
`(Lp.memLp f).restrict s).toLp f`. This map is non-expansive.
-/
theorem norm_Lp_toLp_restrict_le (s : Set X) (f : Lp E p μ) :
    ‖((Lp.memLp f).restrict s).toLp f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
  refine ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) ?_
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

variable (X F 𝕜) in
/-- Continuous linear map sending a function of `Lp F p μ` to the same function in
`Lp F p (μ.restrict s)`. -/
/-
**MeasureTheory.LpToLpRestrictCLM** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory`。
形式化陈述：LpToLpRestrictCLM (μ : Measure X) (p : Real>=0∞) [hp : Fact (1 <= p)] (s :
 Set X) : Lp F p μ ->L[𝕜] Lp F p (μ.restrict s)
参数：μ : Measure X；p : Real>=0∞；1 <= p；s : Set X。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Lp_toLp_restrict_add`：Lp_toLp_restrict_add (f g : Lp E p μ
) (s : Set X) : ((Lp.memLp (f + g)).restrict s).toLp (⇑(f + g)) = ((Lp.memLp f).
restrict s).toLp f + ((L…
· 使用定理 `MeasureTheory.Lp_toLp_restrict_smul`：Lp_toLp_restrict_smul (c : 𝕜) (f : 
Lp F p μ) (s : Set X) : ((Lp.memLp (c • f)).restrict s).toLp (⇑(c • f)) = c • ((
Lp.memLp f).restrict s).t…

--- 原说明 ---
Continuous linear map sending a function of `Lp F p μ` to the same function in
`Lp F p (μ.restrict s)`.
-/
noncomputable def LpToLpRestrictCLM (μ : Measure X) (p : ℝ≥0∞) [hp : Fact (1 ≤ p)] (s : Set X) :
    Lp F p μ →L[𝕜] Lp F p (μ.restrict s) :=
  @LinearMap.mkContinuous 𝕜 𝕜 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _ _ (RingHom.id 𝕜)
    ⟨⟨fun f => MemLp.toLp f ((Lp.memLp f).restrict s), fun f g => Lp_toLp_restrict_add f g s⟩,
      fun c f => Lp_toLp_restrict_smul c f s⟩
    1 (by intro f; rw [one_mul]; exact norm_Lp_toLp_restrict_le s f)

variable (𝕜) in
/-
**MeasureTheory.LpToLpRestrictCLM_coeFn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：LpToLpRestrictCLM_coeFn [Fact (1 <= p)] (s : Set X) (f : Lp F p μ) : LpToL
pRestrictCLM X F 𝕜 μ p s f =ᵐ[μ.restrict s] f
参数：1 <= p；s : Set X；f : Lp F p μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.MemLp.coeFn_toLp`：coeFn_toLp {f : α -> E} (hf : MemLp f p 
μ) : hf.toLp f =ᵐ[μ] f
· 使用定理 `MeasureTheory.MemLp.restrict`：∀ {α : Type u_1} {m0 : MeasurableSpace α} 
{p : ENNReal} {μ : MeasureTheory.Measure α} {ε : Type u_7}   [inst : Topological
Space ε] [inst_1 :…
· 使用定理 `MeasureTheory.Lp.memLp`：∀ {α : Type u_1} {E : Type u_4} {m : MeasurableS
pace α} {p : ENNReal} {μ : MeasureTheory.Measure α}   [inst : NormedAddCommGroup
 E] (f : ↥(M…
-/
theorem LpToLpRestrictCLM_coeFn [Fact (1 ≤ p)] (s : Set X) (f : Lp F p μ) :
    LpToLpRestrictCLM X F 𝕜 μ p s f =ᵐ[μ.restrict s] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).restrict s)

@[continuity]
/-
**MeasureTheory.continuous_setIntegral** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`
。
形式化陈述：continuous_setIntegral [NormedSpace Real E] (s : Set X) : Continuous fun f
 : X ->₁[μ] E => ∫ x in s, f x ∂μ
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `MeasureTheory.integral_congr_ae`：integral_congr_ae {f g : α -> G} (h : f
 =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.LpToLpRestrictCLM_coeFn`：LpToLpRestrictCLM_coeFn [Fact (1 
<= p)] (s : Set X) (f : Lp F p μ) : LpToLpRestrictCLM X F 𝕜 μ p s f =ᵐ[μ.restric
t s] f
· 使用定理 `fact_one_le_one_ennreal`：Fact (1 ≤ 1)
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `MeasureTheory.continuous_integral`：continuous_integral : Continuous fun 
f : α ->₁[μ] G => ∫ a, f a ∂μ
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem continuous_setIntegral [NormedSpace ℝ E] (s : Set X) :
    Continuous fun f : X →₁[μ] E => ∫ x in s, f x ∂μ := by
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  have h_comp :
    (fun f : X →₁[μ] E => ∫ x in s, f x ∂μ) =
      integral (μ.restrict s) ∘ fun f => LpToLpRestrictCLM X E ℝ μ 1 s f := by
    ext1 f
    rw [Function.comp_apply, integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s f)]
  rw [h_comp]
  exact continuous_integral.comp (LpToLpRestrictCLM X E ℝ μ 1 s).continuous

end ContinuousSetIntegral

end MeasureTheory

section OpenPos

open Measure

variable [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
  {μ : Measure X} [IsOpenPosMeasure μ]

/-
**Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero** 是 Mathlib 中的一个定理
，位于命名空间 ``。
形式化陈述：Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero [IsFiniteMeasu
reOnCompacts μ] {f : X -> Real} {x : X} (f_cont : Continuous f) (f_comp : HasCom
pactSupport f) (f_nonneg : 0 <= f) (f_x : f x != 0) : 0 < ∫ x, f x ∂μ
参数：f_cont : Continuous f；f_comp : HasCompactSupport f；f_nonneg : 0 <= f；f_x : f 
x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.integral_pos_of_integrable_nonneg_nonzero`：integral_pos_of
_integrable_nonneg_nonzero [TopologicalSpace α] [Measure.IsOpenPosMeasure μ] {f 
: α -> Real} {x : α} (f_cont : Continuous f) …
· 使用定理 `Continuous.integrable_of_hasCompactSupport`：Continuous.integrable_of_has
CompactSupport (hf : Continuous f) (hcf : HasCompactSupport f) : Integrable f μ
-/
theorem Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero [IsFiniteMeasureOnCompacts μ]
    {f : X → ℝ} {x : X} (f_cont : Continuous f) (f_comp : HasCompactSupport f) (f_nonneg : 0 ≤ f)
    (f_x : f x ≠ 0) : 0 < ∫ x, f x ∂μ :=
  integral_pos_of_integrable_nonneg_nonzero f_cont (f_cont.integrable_of_hasCompactSupport f_comp)
    f_nonneg f_x

end OpenPos

section Support

variable {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] {mX : MeasurableSpace X}
  {ν : Measure X} {F : X → M}

/-
**MeasureTheory.setIntegral_support** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.setIntegral_support : ∫ x in support F, F x ∂ν = ∫ x, F x ∂ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`：setInteg
ral_eq_of_subset_of_forall_sdiff_eq_zero (ht : MeasurableSet t) (hts : s subsete
q t) (h't : forall x in t \ s, f x = 0) : ∫ x in t, …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.notMem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M]
 {f : ι → M} {x : ι}, x ∉ Function.support f ↔ f x = 0
· 使用定理 `Set.notMem_of_mem_sdiff`：notMem_of_mem_sdiff {s t : Set α} {x : α} (h : 
x in s \ t) : x ∉ t
-/
theorem MeasureTheory.setIntegral_support : ∫ x in support F, F x ∂ν = ∫ x, F x ∂ν := by
  nth_rw 2 [← setIntegral_univ]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ (subset_univ (support F))]
  exact fun _ hx => notMem_support.mp <| notMem_of_mem_sdiff hx
/-
**MeasureTheory.setIntegral_tsupport** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasureTheory.setIntegral_tsupport [TopologicalSpace X] : ∫ x in tsupport 
F, F x ∂ν = ∫ x, F x ∂ν
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero`：setInteg
ral_eq_of_subset_of_forall_sdiff_eq_zero (ht : MeasurableSet t) (hts : s subsete
q t) (h't : forall x in t \ s, f x = 0) : ∫ x in t, …
· 使用定理 `MeasurableSet.univ`：∀ {α : Type u_1} {m : MeasurableSpace α}, Measurable
Set Set.univ
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `image_eq_zero_of_notMem_tsupport`：∀ {X : Type u_1} {α : Type u_2} [inst 
: Zero α] [inst_1 : TopologicalSpace X] {f : X → α} {x : X},   x ∉ tsupport f → 
f x = 0
· 使用定理 `Set.notMem_of_mem_sdiff`：notMem_of_mem_sdiff {s t : Set α} {x : α} (h : 
x in s \ t) : x ∉ t
-/
theorem MeasureTheory.setIntegral_tsupport [TopologicalSpace X] :
    ∫ x in tsupport F, F x ∂ν = ∫ x, F x ∂ν := by
  nth_rw 2 [← setIntegral_univ]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
    (subset_univ (tsupport F))]
  exact fun _ hx => image_eq_zero_of_notMem_tsupport <| notMem_of_mem_sdiff hx

end Support

section thickenedIndicator

variable [MeasurableSpace X] [PseudoEMetricSpace X]

/-
**measure_le_lintegral_thickenedIndicatorAux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measure_le_lintegral_thickenedIndicatorAux (μ : Measure X) {E : Set X} (E_
mble : MeasurableSet E) (δ : Real) : μ E <= ∫⁻ x, (thickenedIndicatorAux δ E x :
 Real>=0∞) ∂μ
参数：μ : Measure X；E_mble : MeasurableSet E；δ : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.lintegral_indicator`：lintegral_indicator {s : Set α} (hs :
 MeasurableSet s) (f : α -> Real>=0∞) : ∫⁻ a, s.indicator f a ∂μ = ∫⁻ a in s, f 
a ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasureTheory.lintegral_one`：lintegral_one : ∫⁻ _, (1 : Real>=0∞) ∂μ = μ
 univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `indicator_le_thickenedIndicatorAux`：indicator_le_thickenedIndicatorAux (
δ : Real) (E : Set α) : (E.indicator fun _ => (1 : Real>=0∞)) <= thickenedIndica
torAux δ E
-/
theorem measure_le_lintegral_thickenedIndicatorAux (μ : Measure X) {E : Set X}
    (E_mble : MeasurableSet E) (δ : ℝ) : μ E ≤ ∫⁻ x, (thickenedIndicatorAux δ E x : ℝ≥0∞) ∂μ := by
  convert_to lintegral μ (E.indicator fun _ => (1 : ℝ≥0∞)) ≤ lintegral μ (thickenedIndicatorAux δ E)
  · rw [lintegral_indicator E_mble]
    simp only [lintegral_one, Measure.restrict_apply, MeasurableSet.univ, univ_inter]
  · apply lintegral_mono
    apply indicator_le_thickenedIndicatorAux

set_option backward.defeqAttrib.useBackward true in
/-
**measure_le_lintegral_thickenedIndicator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measure_le_lintegral_thickenedIndicator (μ : Measure X) {E : Set X} (E_mbl
e : MeasurableSet E) {δ : Real} (δ_pos : 0 < δ) : μ E <= ∫⁻ x, (thickenedIndicat
or δ_pos E x : Real>=0∞) ∂μ
参数：μ : Measure X；E_mble : MeasurableSet E；δ_pos : 0 < δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_toNNReal`：∀ {a : ENNReal}, a ≠ ⊤ → ↑a.toNNReal = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `thickenedIndicatorAux_lt_top`：thickenedIndicatorAux_lt_top {δ : Real} {E
 : Set α} {x : α} : thickenedIndicatorAux δ E x < ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `measure_le_lintegral_thickenedIndicatorAux`：measure_le_lintegral_thicken
edIndicatorAux (μ : Measure X) {E : Set X} (E_mble : MeasurableSet E) (δ : Real)
 : μ E <= ∫⁻ x, (thickenedIndica…
-/
theorem measure_le_lintegral_thickenedIndicator (μ : Measure X) {E : Set X}
    (E_mble : MeasurableSet E) {δ : ℝ} (δ_pos : 0 < δ) :
    μ E ≤ ∫⁻ x, (thickenedIndicator δ_pos E x : ℝ≥0∞) ∂μ := by
  convert! measure_le_lintegral_thickenedIndicatorAux μ E_mble δ
  dsimp
  simp only [thickenedIndicatorAux_lt_top.ne, ENNReal.coe_toNNReal, Ne, not_false_iff]

end thickenedIndicator

-- We declare a new `{X : Type*}` to discard the instance `[MeasurableSpace X]`
-- which has been in scope for the entire file up to this point.
variable {X : Type*}

section BilinearMap

namespace MeasureTheory

variable {X : Type*} {f : X → ℝ} {m m0 : MeasurableSpace X} {μ : Measure X}

/-
**MeasureTheory.Integrable.simpleFunc_mul** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.Integrable`。
形式化陈述：∀ {X : Type u_6} {f : X → ℝ} {m0 : MeasurableSpace X} {μ : MeasureTheory.M
easure X} (g : MeasureTheory.SimpleFunc X ℝ),   MeasureTheory.Integrable f μ → M
easureTheory.Integrable (⇑g * f) μ
参数：g : MeasureTheory.SimpleFunc X ℝ；⇑g * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.induction`：∀ {α : Type u_5} {γ : Type u_6} [ins
t : MeasurableSpace α] [inst_1 : AddZeroClass γ]   {motive : MeasureTheory.Simpl
eFunc α γ → Prop},   (∀ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero
 M] {s : Set α} {f : α → M} [inst_1 : DecidablePred fun x => x ∈ s],   s.piecewi
se f 0 = s.indic…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MeasureTheory.integrable_indicator_iff`：integrable_indicator_iff (hs : M
easurableSet s) : Integrable (indicator s f) μ ↔ IntegrableOn f s μ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Integrable.smul`：∀ {α : Type u_1} {β : Type u_2} {m : Meas
urableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {𝕜 
: Type u_8} [inst_1…
· 使用定理 `MeasureTheory.Integrable.congr`：∀ {α : Type u_1} {ε : Type u_5} {m : Mea
surableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpace ε]   [ins
t_1 : ContinuousENor…
· 使用定理 `MeasureTheory.Integrable.add`：∀ {α : Type u_1} {m : MeasurableSpace α} {
μ : MeasureTheory.Measure α} {ε' : Type u_8} [inst : TopologicalSpace ε']   [ins
t_1 : ESeminormedA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.SimpleFunc.coe_add`：∀ {α : Type u_1} {β : Type u_2} [inst 
: MeasurableSpace α] [inst_1 : Add β] (f g : MeasureTheory.SimpleFunc α β),   ⇑(
f + g) = ⇑f + ⇑g
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem Integrable.simpleFunc_mul (g : SimpleFunc X ℝ) (hf : Integrable f μ) :
    Integrable (⇑g * f) μ := by
  refine
    SimpleFunc.induction (fun c s hs => ?_)
      (fun g₁ g₂ _ h_int₁ h_int₂ =>
        (h_int₁.add h_int₂).congr (by rw [SimpleFunc.coe_add, add_mul]))
      g
  simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
    SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
  have : Set.indicator s (Function.const X c) * f = s.indicator (c • f) := by
    ext1 x
    by_cases hx : x ∈ s
    · simp only [hx, Pi.mul_apply, Set.indicator_of_mem, Pi.smul_apply, smul_eq_mul,
        ← Function.const_def]
    · simp only [hx, Pi.mul_apply, Set.indicator_of_notMem, not_false_iff, zero_mul]
  rw [this, integrable_indicator_iff hs]
  exact (hf.smul c).integrableOn
/-
**MeasureTheory.Integrable.simpleFunc_mul'** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.Integrable`。
形式化陈述：∀ {X : Type u_6} {f : X → ℝ} {m m0 : MeasurableSpace X} {μ : MeasureTheory
.Measure X},   m ≤ m0 → ∀ (g : MeasureTheory.SimpleFunc X ℝ), MeasureTheory.Inte
grable f μ → MeasureTheory.Integrable (⇑g * f) μ
参数：g : MeasureTheory.SimpleFunc X ℝ；⇑g * f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.SimpleFunc.coe_toLargerSpace_eq`：∀ {β : Type u_6} {γ : Typ
e u_7} {m m0 : MeasurableSpace β} (hm : m ≤ m0) (f : MeasureTheory.SimpleFunc β 
γ),   ⇑(MeasureTheory.SimpleFunc.to…
· 使用定理 `MeasureTheory.Integrable.simpleFunc_mul`：∀ {X : Type u_6} {f : X → ℝ} {m
0 : MeasurableSpace X} {μ : MeasureTheory.Measure X} (g : MeasureTheory.SimpleFu
nc X ℝ),   MeasureTheory.Inte…
-/
theorem Integrable.simpleFunc_mul' (hm : m ≤ m0) (g : @SimpleFunc X m ℝ) (hf : Integrable f μ) :
    Integrable (⇑g * f) μ := by
  rw [← SimpleFunc.coe_toLargerSpace_eq hm g]; exact hf.simpleFunc_mul (g.toLargerSpace hm)

end MeasureTheory

end BilinearMap

section ParametricIntegral

variable {G 𝕜 : Type*} [TopologicalSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] {μ : Measure Y}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open Metric ContinuousLinearMap

/-- The parametric integral over a continuous function on a compact set is continuous,
  under mild assumptions on the topologies involved. -/
/-
**continuous_parametric_integral_of_continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_parametric_integral_of_continuous [FirstCountableTopology X] [L
ocallyCompactSpace X] [SecondCountableTopologyEither Y E] [IsLocallyFiniteMeasur
e μ] {f : X -> Y -> E} (hf : Continuous f.uncurry) {s : Set Y} (hs : IsCompact s
) : Continuous (∫ y in s, f · y ∂μ)
参数：hf : Continuous f.uncurry；hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `IsCompact.bddAbove_image`：IsCompact.bddAbove_image [ClosedIciTopology α]
 [Nonempty α] {f : β -> α} {K : Set β} (hK : IsCompact K) (hf : ContinuousOn f K
) : BddAbove (…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsCompact.prod`：IsCompact.prod {t : Set Y} (hs : IsCompact s) (ht : IsCo
mpact t) : IsCompact (s ×ˢ t)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Continuous.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAddGr
oup E] [inst_1 : TopologicalSpace α] {f : α → E},   Continuous f → Continuous fu
n x =…
· 使用定理 `MeasureTheory.continuousAt_of_dominated`：continuousAt_of_dominated {F : 
X -> α -> G} {x₀ : X} {bound : α -> Real} (hF_meas : forallᶠ x in 𝓝 x₀, AEStrong
lyMeasurable (F x) μ) (h_boun…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_restrict_iff`：ae_restrict_iff {p : α -> Prop} (hp : Mea
surableSet { x | p x }) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s 
-> p x
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用定理 `IsCompact.measure_ne_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用定理 `isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure`：∀ {α : Type u_1} [i
nst : TopologicalSpace α] {x : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
  [MeasureTheory.IsLocallyFiniteMeasure μ…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The parametric integral over a continuous function on a compact set is continuou
s,
  under mild assumptions on the topologies involved.
-/
theorem continuous_parametric_integral_of_continuous
    [FirstCountableTopology X] [LocallyCompactSpace X]
    [SecondCountableTopologyEither Y E] [IsLocallyFiniteMeasure μ]
    {f : X → Y → E} (hf : Continuous f.uncurry) {s : Set Y} (hs : IsCompact s) :
    Continuous (∫ y in s, f · y ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rcases exists_compact_mem_nhds x₀ with ⟨U, U_cpct, U_nhds⟩
  rcases (U_cpct.prod hs).bddAbove_image hf.norm.continuousOn with ⟨M, hM⟩
  apply continuousAt_of_dominated
  · filter_upwards with x using Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [U_nhds] with x x_in
    rw [ae_restrict_iff]
    · filter_upwards with t t_in using hM (mem_image_of_mem _ <| mk_mem_prod x_in t_in)
    · exact (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  · exact integrableOn_const hs.measure_ne_top
  · filter_upwards using (by fun_prop)

/-- Consider a parameterized integral `x ↦ ∫ y, L (g y) (f x y)` where `L` is bilinear,
`g` is locally integrable and `f` is continuous and uniformly compactly supported. Then the
integral depends continuously on `x`. -/
/-
**continuousOn_integral_bilinear_of_locally_integrable_of_compact_support** 是 Ma
thlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuousOn_integral_bilinear_of_locally_integrable_of_compact_support [N
ormedSpace 𝕜 E] (L : F ->L[𝕜] G ->L[𝕜] E) {f : X -> Y -> G} {s : Set X} {k : Set
 Y} {g : Y -> F} (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ univ)) (h
fs : forall p, forall x, p in s -> x ∉ k -> f p x = 0) (hg : IntegrableOn g k μ)
 : ContinuousOn (fun x => ∫ y, L (g y) (f x y) ∂μ) s
参数：L : F ->L[𝕜] G ->L[𝕜] E；hk : IsCompact k；hf : ContinuousOn f.uncurry (s ×ˢ un
iv)；hfs : forall p, forall x, p in s -> x ∉ k -> f p x = 0；hg : IntegrableOn g k
 μ。
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
· 使用定理 `ContinuousOn.comp_continuous`：ContinuousOn.comp_continuous {g : β -> γ} 
{f : α -> β} {s : Set β} (hg : ContinuousOn g s) (hf : Continuous f) (hs : foral
l x, f x in s) : C…
· 使用定理 `Continuous.prodMk_right`：Continuous.prodMk_right (x : X) : Continuous fu
n y : Y => (x, y)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.continuousWithinAt_iff'`：continuousWithinAt_iff' [TopologicalSpac
e β] {f : β -> α} {b : β} {s : Set β} : ContinuousWithinAt f s b ↔ forall ε > 0,
 forallᶠ x in 𝓝[s] b…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.integral_mul_const`：integral_mul_const {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, f a * r ∂μ = (∫ a, f a ∂μ) * r
· 使用定理 `exists_pos_mul_lt`：exists_pos_mul_lt {a : α} (h : 0 < a) (b : α) : exist
s c : α, 0 < c ∧ b * c < a
· 使用引理 `IsCompact.mem_uniformity_of_prod`：IsCompact.mem_uniformity_of_prod {α β 
E : Type*} [TopologicalSpace α] [TopologicalSpace β] [UniformSpace E] {f : α -> 
β -> E} {s : Set α} {k…
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `Set.prod_mono_right`：prod_mono_right (ht : t₁ subseteq t₂) : s ×ˢ t₁ sub
seteq s ×ˢ t₂
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `ContinuousOn.prodMk`：ContinuousOn.prodMk {f : α -> β} {g : α -> γ} {s : 
Set α} (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => 
(f x, g x…
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
（共 75 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a parameterized integral `x ↦ ∫ y, L (g y) (f x y)` where `L` is biline
ar,
`g` is locally integrable and `f` is continuous and uniformly compactly supporte
d. Then the
integral depends continuously on `x`.
-/
lemma continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
    [NormedSpace 𝕜 E] (L : F →L[𝕜] G →L[𝕜] E)
    {f : X → Y → G} {s : Set X} {k : Set Y} {g : Y → F}
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hfs : ∀ p, ∀ x, p ∈ s → x ∉ k → f p x = 0) (hg : IntegrableOn g k μ) :
    ContinuousOn (fun x ↦ ∫ y, L (g y) (f x y) ∂μ) s := by
  have A : ∀ p ∈ s, Continuous (f p) := fun p hp ↦ by
    refine hf.comp_continuous (.prodMk_right _) fun y => ?_
    simpa only [prodMk_mem_set_prod_eq, mem_univ, and_true] using hp
  intro q hq
  apply Metric.continuousWithinAt_iff'.2 (fun ε εpos ↦ ?_)
  obtain ⟨δ, δpos, hδ⟩ : ∃ (δ : ℝ), 0 < δ ∧ ∫ x in k, ‖L‖ * ‖g x‖ * δ ∂μ < ε := by
    simpa [integral_mul_const] using exists_pos_mul_lt εpos _
  obtain ⟨v, v_mem, hv⟩ : ∃ v ∈ 𝓝[s] q, ∀ p ∈ v, ∀ x ∈ k, dist (f p x) (f q x) < δ :=
    hk.mem_uniformity_of_prod
      (hf.mono (Set.prod_mono_right (subset_univ k))) hq (dist_mem_uniformity δpos)
  simp_rw [dist_eq_norm] at hv ⊢
  have I : ∀ p ∈ s, IntegrableOn (fun y ↦ L (g y) (f p y)) k μ := by
    intro p hp
    obtain ⟨C, hC⟩ : ∃ C, ∀ y, ‖f p y‖ ≤ C := by
      have : ContinuousOn (f p) k := by
        have : ContinuousOn (fun y ↦ (p, y)) k := by fun_prop
        exact hf.comp this (by simp [MapsTo, hp])
      rcases IsCompact.exists_bound_of_continuousOn hk this with ⟨C, hC⟩
      refine ⟨max C 0, fun y ↦ ?_⟩
      by_cases hx : y ∈ k
      · exact (hC y hx).trans (le_max_left _ _)
      · simp [hfs p y hp hx]
    have : IntegrableOn (fun y ↦ ‖L‖ * ‖g y‖ * C) k μ :=
      (hg.norm.const_mul _).mul_const _
    apply Integrable.mono' this ?_ ?_
    · borelize G
      apply L.aestronglyMeasurable_comp₂ hg.aestronglyMeasurable
      apply StronglyMeasurable.aestronglyMeasurable
      apply Continuous.stronglyMeasurable_of_support_subset_isCompact (A p hp) hk
      apply support_subset_iff'.2 (fun y hy ↦ hfs p y hp hy)
    · apply Eventually.of_forall (fun y ↦ (le_opNorm₂ L (g y) (f p y)).trans ?_)
      gcongr
      apply hC
  filter_upwards [v_mem, self_mem_nhdsWithin] with p hp h'p
  calc
  ‖∫ x, L (g x) (f p x) ∂μ - ∫ x, L (g x) (f q x) ∂μ‖
    = ‖∫ x in k, L (g x) (f p x) ∂μ - ∫ x in k, L (g x) (f q x) ∂μ‖ := by
      congr 2
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)).symm
        simp [hfs p y h'p hy]
      · refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy ↦ ?_)).symm
        simp [hfs q y hq hy]
  _ = ‖∫ x in k, L (g x) (f p x) - L (g x) (f q x) ∂μ‖ := by rw [integral_sub (I p h'p) (I q hq)]
  _ ≤ ∫ x in k, ‖L (g x) (f p x) - L (g x) (f q x)‖ ∂μ := norm_integral_le_integral_norm _
  _ ≤ ∫ x in k, ‖L‖ * ‖g x‖ * δ ∂μ := by
      apply integral_mono_of_nonneg (Eventually.of_forall (fun y ↦ by positivity))
      · exact (hg.norm.const_mul _).mul_const _
      · filter_upwards with y
        by_cases hy : y ∈ k
        · specialize hv p hp y hy
          calc
          ‖L (g y) (f p y) - L (g y) (f q y)‖
            = ‖L (g y) (f p y - f q y)‖ := by simp only [map_sub]
          _ ≤ ‖L‖ * ‖g y‖ * ‖f p y - f q y‖ := le_opNorm₂ _ _ _
          _ ≤ ‖L‖ * ‖g y‖ * δ := by gcongr
        · simp only [hfs p y h'p hy, hfs q y hq hy, sub_self, norm_zero]
          positivity
  _ < ε := hδ

/-- Consider a parameterized integral `x ↦ ∫ y, f x y` where `f` is continuous and uniformly
compactly supported. Then the integral depends continuously on `x`. -/
/-
**continuousOn_integral_of_compact_support** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuousOn_integral_of_compact_support {f : X -> Y -> E} {s : Set X} {k 
: Set Y} [IsFiniteMeasureOnCompacts μ] (hk : IsCompact k) (hf : ContinuousOn f.u
ncurry (s ×ˢ univ)) (hfs : forall p, forall x, p in s -> x ∉ k -> f p x = 0) : C
ontinuousOn (fun x => ∫ y, f x y ∂μ) s
参数：hk : IsCompact k；hf : ContinuousOn f.uncurry (s ×ˢ univ)；hfs : forall p, fora
ll x, p in s -> x ∉ k -> f p x = 0。
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
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `continuousOn_integral_bilinear_of_locally_integrable_of_compact_support`
：continuousOn_integral_bilinear_of_locally_integrable_of_compact_support [Normed
Space 𝕜 E] (L : F ->L[𝕜] G ->L[𝕜] E) {f : X -> Y -> G} {s : S…
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用定理 `IsCompact.measure_ne_top`：∀ {α : Type u_1} {m0 : MeasurableSpace α} [ins
t : TopologicalSpace α] {μ : MeasureTheory.Measure α}   [MeasureTheory.IsFiniteM
easureOnCompac…
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞

--- 原说明 ---
Consider a parameterized integral `x ↦ ∫ y, f x y` where `f` is continuous and u
niformly
compactly supported. Then the integral depends continuously on `x`.
-/
lemma continuousOn_integral_of_compact_support
    {f : X → Y → E} {s : Set X} {k : Set Y} [IsFiniteMeasureOnCompacts μ]
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ univ))
    (hfs : ∀ p, ∀ x, p ∈ s → x ∉ k → f p x = 0) :
    ContinuousOn (fun x ↦ ∫ y, f x y ∂μ) s := by
  simpa using continuousOn_integral_bilinear_of_locally_integrable_of_compact_support (lsmul ℝ ℝ)
    hk hf hfs (integrableOn_const hk.measure_ne_top) (g := fun _ ↦ 1)

end ParametricIntegral

