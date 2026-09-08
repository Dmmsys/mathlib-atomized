/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Notation

/-!
# Basic properties of the manifold Fréchet derivative

In this file, we show various properties of the manifold Fréchet derivative,
mimicking the API for Fréchet derivatives.
- basic properties of unique differentiability sets
- various general lemmas about the manifold Fréchet derivative
- deducing differentiability from smoothness,
- deriving continuity from differentiability on manifolds,
- congruence lemmas for derivatives on manifolds
- composition lemmas and the chain rule

-/

public section

noncomputable section

assert_not_exists tangentBundleCore

open scoped Topology Manifold
open Function Set Bundle ChartedSpace

section DerivativesProperties

/-! ### Unique differentiability sets in manifolds -/

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f f₁ : M → M'} {x : M} {s t : Set M} {g : M' → M''} {u : Set M'}

/-
**uniqueMDiffWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ : Set M)] x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ModelWithCorners.uniqueDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ : Set M)] x := by
  unfold UniqueMDiffWithinAt
  simp only [preimage_univ, univ_inter]
  exact I.uniqueDiffOn _ (mem_range_self _)

variable {I}
/-
**uniqueMDiffWithinAt_iff_inter_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueMDiffWithinAt_iff_inter_range {s : Set M} {x : M} : UniqueMDiffAt[s]
 x ↔ UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s inter range I) ((extChart
At I x) x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uniqueMDiffWithinAt_iff_inter_range {s : Set M} {x : M} :
    UniqueMDiffAt[s] x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) := Iff.rfl
/-
**uniqueMDiffWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueMDiffWithinAt_iff {s : Set M} {x : M} : UniqueMDiffAt[s] x ↔ UniqueD
iffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s inter (extChartAt I x).target) ((extC
hartAt I x) x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniqueDiffWithinAt_congr`：uniqueDiffWithinAt_congr (st : 𝓝[s] x = 𝓝[t] x
) : UniqueDiffWithinAt 𝕜 s x ↔ UniqueDiffWithinAt 𝕜 t x
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsWithin_inter`：nhdsWithin_inter (a : α) (s t : Set α) : 𝓝[s inter t] 
a = 𝓝[s] a ⊓ 𝓝[t] a
· 使用定理 `nhdsWithin_extChartAt_target_eq`：nhdsWithin_extChartAt_target_eq (x : M)
 : 𝓝[(extChartAt I x).target] (extChartAt I x) x = 𝓝[range I] (extChartAt I x) x
-/
theorem uniqueMDiffWithinAt_iff {s : Set M} {x : M} :
    UniqueMDiffAt[s] x ↔
      UniqueDiffWithinAt 𝕜 ((extChartAt I x).symm ⁻¹' s ∩ (extChartAt I x).target)
        ((extChartAt I x) x) := by
  apply uniqueDiffWithinAt_congr
  rw [nhdsWithin_inter, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]

nonrec theorem UniqueMDiffWithinAt.mono_nhds {s t : Set M} {x : M} (hs : UniqueMDiffAt[s] x)
    (ht : 𝓝[s] x ≤ 𝓝[t] x) : UniqueMDiffAt[t] x :=
  hs.mono_nhds <| by simpa only [← map_extChartAt_nhdsWithin] using Filter.map_mono ht
/-
**UniqueMDiffWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffWithinAt.mono_of_mem_nhdsWithin {s t : Set M} {x : M} (hs : Uni
queMDiffAt[s] x) (ht : t in 𝓝[s] x) : UniqueMDiffAt[t] x
参数：hs : UniqueMDiffAt[s] x；ht : t in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.mono_nhds`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `nhdsWithin_le_iff`：nhdsWithin_le_iff {s t : Set α} {x : α} : 𝓝[s] x <= 𝓝
[t] x ↔ t in 𝓝[s] x
-/
theorem UniqueMDiffWithinAt.mono_of_mem_nhdsWithin {s t : Set M} {x : M}
    (hs : UniqueMDiffAt[s] x) (ht : t ∈ 𝓝[s] x) : UniqueMDiffAt[t] x :=
  hs.mono_nhds (nhdsWithin_le_iff.2 ht)
/-
**UniqueMDiffWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffWithinAt.mono (h : UniqueMDiffAt[s] x) (st : s subseteq t) : Un
iqueMDiffAt[t] x
参数：h : UniqueMDiffAt[s] x；st : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueDiffWithinAt.mono`：UniqueDiffWithinAt.mono (h : UniqueDiffWithinAt
 𝕜 s x) (st : s subseteq t) : UniqueDiffWithinAt 𝕜 t x
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem UniqueMDiffWithinAt.mono (h : UniqueMDiffAt[s] x) (st : s ⊆ t) :
    UniqueMDiffAt[t] x :=
  UniqueDiffWithinAt.mono h <| inter_subset_inter (preimage_mono st) (Subset.refl _)
/-
**UniqueMDiffWithinAt.inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffWithinAt.inter' (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝[s] x) : 
UniqueMDiffAt[s inter t] x
参数：hs : UniqueMDiffAt[s] x；ht : t in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.mono_of_mem_nhdsWithin`：UniqueMDiffWithinAt.mono_of_
mem_nhdsWithin {s t : Set M} {x : M} (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝[s] x
) : UniqueMDiffAt[t] x
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem UniqueMDiffWithinAt.inter' (hs : UniqueMDiffAt[s] x) (ht : t ∈ 𝓝[s] x) :
    UniqueMDiffAt[s ∩ t] x :=
  hs.mono_of_mem_nhdsWithin (Filter.inter_mem self_mem_nhdsWithin ht)
/-
**UniqueMDiffWithinAt.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffWithinAt.inter (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝 x) : Uniq
ueMDiffAt[s inter t] x
参数：hs : UniqueMDiffAt[s] x；ht : t in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.inter'`：UniqueMDiffWithinAt.inter' (hs : UniqueMDiff
At[s] x) (ht : t in 𝓝[s] x) : UniqueMDiffAt[s inter t] x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
theorem UniqueMDiffWithinAt.inter (hs : UniqueMDiffAt[s] x) (ht : t ∈ 𝓝 x) :
    UniqueMDiffAt[s ∩ t] x :=
  hs.inter' (nhdsWithin_le_nhds ht)
/-
**IsOpen.uniqueMDiffWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.uniqueMDiffWithinAt (hs : IsOpen s) (xs : x in s) : UniqueMDiffAt[s
] x
参数：hs : IsOpen s；xs : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.mono_of_mem_nhdsWithin`：UniqueMDiffWithinAt.mono_of_
mem_nhdsWithin {s t : Set M} {x : M} (hs : UniqueMDiffAt[s] x) (ht : t in 𝓝[s] x
) : UniqueMDiffAt[t] x
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem IsOpen.uniqueMDiffWithinAt (hs : IsOpen s) (xs : x ∈ s) : UniqueMDiffAt[s] x :=
  (uniqueMDiffWithinAt_univ I).mono_of_mem_nhdsWithin <| nhdsWithin_le_nhds <| hs.mem_nhds xs
/-
**UniqueMDiffOn.inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.inter (hs : UniqueMDiff[s]) (ht : IsOpen t) : UniqueMDiff[s 
inter t]
参数：hs : UniqueMDiff[s]；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.inter`：UniqueMDiffWithinAt.inter (hs : UniqueMDiffAt
[s] x) (ht : t in 𝓝 x) : UniqueMDiffAt[s inter t] x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem UniqueMDiffOn.inter (hs : UniqueMDiff[s]) (ht : IsOpen t) : UniqueMDiff[s ∩ t] :=
  fun _x hx => UniqueMDiffWithinAt.inter (hs _ hx.1) (ht.mem_nhds hx.2)
/-
**IsOpen.uniqueMDiffOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.uniqueMDiffOn (hs : IsOpen s) : UniqueMDiff[s]
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.uniqueMDiffWithinAt`：IsOpen.uniqueMDiffWithinAt (hs : IsOpen s) (
xs : x in s) : UniqueMDiffAt[s] x
-/
theorem IsOpen.uniqueMDiffOn (hs : IsOpen s) : UniqueMDiff[s] :=
  fun _x hx => hs.uniqueMDiffWithinAt hx
/-
**uniqueMDiffOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueMDiffOn_univ : UniqueMDiff[(univ : Set M)]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.uniqueMDiffOn`：IsOpen.uniqueMDiffOn (hs : IsOpen s) : UniqueMDiff
[s]
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
-/
theorem uniqueMDiffOn_univ : UniqueMDiff[(univ : Set M)] :=
  isOpen_univ.uniqueMDiffOn

nonrec theorem UniqueMDiffWithinAt.prod {x : M} {y : M'} {s : Set M} {t : Set M'}
    (hs : UniqueMDiffAt[s] x) (ht : UniqueMDiffAt[t] y) : UniqueMDiffAt[s ×ˢ t] (x, y) := by
  refine (hs.prod ht).mono ?_
  rw [ModelWithCorners.range_prod, ← prod_inter_prod]
  rfl
/-
**UniqueMDiffOn.prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.prod {s : Set M} {t : Set M'} (hs : UniqueMDiff[s]) (ht : Un
iqueMDiff[t]) : UniqueMDiff[s ×ˢ t]
参数：hs : UniqueMDiff[s]；ht : UniqueMDiff[t]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.prod`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {H : Type u_…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem UniqueMDiffOn.prod {s : Set M} {t : Set M'} (hs : UniqueMDiff[s])
    (ht : UniqueMDiff[t]) : UniqueMDiff[s ×ˢ t] := fun x h ↦
  (hs x.1 h.1).prod (ht x.2 h.2)
/-
**MDifferentiableWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.mono (hst : s subseteq t) (h : MDiffAt[t] f x) : M
DiffAt[s] f x
参数：hst : s subseteq t；h : MDiffAt[t] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt`：MDif
ferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt {f : M -> M'} {s 
: Set M} {x : M} (hf : MDifferentiableWithinAt I I' f s …
· 使用定理 `Set.inter_subset_inter_left`：inter_subset_inter_left {s t : Set α} (u : 
Set α) (H : s subseteq t) : s inter u subseteq t inter u
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem MDifferentiableWithinAt.mono (hst : s ⊆ t) (h : MDiffAt[t] f x) : MDiffAt[s] f x :=
  ⟨ContinuousWithinAt.mono h.1 hst, DifferentiableWithinAt.mono
    h.differentiableWithinAt_writtenInExtChartAt
    (inter_subset_inter_left _ (preimage_mono hst))⟩
/-
**mdifferentiableWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_univ : MDiffAt[univ] f x ↔ MDiffAt f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mdifferentiableWithinAt_univ : MDiffAt[univ] f x ↔ MDiffAt f x := by
  simp_rw [MDifferentiableWithinAt, MDifferentiableAt, ChartedSpace.LiftPropAt]
/-
**mdifferentiableWithinAt_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_inter (ht : t in 𝓝 x) : MDiffAt[s inter t] f x ↔ M
DiffAt[s] f x
参数：ht : t in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiableWithinAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {H : Type u_…
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter`：liftPropWit
hinAt_inter (ht : t in 𝓝 x) : LiftPropWithinAt P g (s inter t) x ↔ LiftPropWithi
nAt P g s x
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mdifferentiableWithinAt_inter (ht : t ∈ 𝓝 x) : MDiffAt[s ∩ t] f x ↔ MDiffAt[s] f x := by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter ht]
/-
**mdifferentiableWithinAt_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_inter' (ht : t in 𝓝[s] x) : MDiffAt[s inter t] f x
 ↔ MDiffAt[s] f x
参数：ht : t in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiableWithinAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorme
dField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace
 𝕜 E] {H : Type u_…
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_inter'`：liftPropWi
thinAt_inter' (ht : t in 𝓝[s] x) : LiftPropWithinAt P g (s inter t) x ↔ LiftProp
WithinAt P g s x
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mdifferentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) : MDiffAt[s ∩ t] f x ↔ MDiffAt[s] f x := by
  rw [MDifferentiableWithinAt, MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_inter' ht]
/-
**MDifferentiableAt.mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.mdifferentiableWithinAt (h : MDiffAt f x) : MDiffAt[s] f
 x
参数：h : MDiffAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mono`：MDifferentiableWithinAt.mono (hst : s subs
eteq t) (h : MDiffAt[t] f x) : MDiffAt[s] f x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
-/
theorem MDifferentiableAt.mdifferentiableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x :=
  MDifferentiableWithinAt.mono (subset_univ _) (mdifferentiableWithinAt_univ.2 h)
/-
**MDifferentiableWithinAt.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.mdifferentiableAt (h : MDiffAt[s] f x) (hs : s in 
𝓝 x) : MDiffAt f x
参数：h : MDiffAt[s] f x；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用定理 `mdifferentiableWithinAt_inter`：mdifferentiableWithinAt_inter (ht : t in 
𝓝 x) : MDiffAt[s inter t] f x ↔ MDiffAt[s] f x
-/
theorem MDifferentiableWithinAt.mdifferentiableAt (h : MDiffAt[s] f x) (hs : s ∈ 𝓝 x) :
    MDiffAt f x := by
  have : s = univ ∩ s := by rw [univ_inter]
  rwa [this, mdifferentiableWithinAt_inter hs, mdifferentiableWithinAt_univ] at h
/-
**MDifferentiableOn.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.mono (h : MDiff[t] f) (st : s subseteq t) : MDiff[s] f
参数：h : MDiff[t] f；st : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mono`：MDifferentiableWithinAt.mono (hst : s subs
eteq t) (h : MDiffAt[t] f x) : MDiffAt[s] f x
-/
theorem MDifferentiableOn.mono (h : MDiff[t] f) (st : s ⊆ t) : MDiff[s] f :=
  fun x hx => (h x (st hx)).mono st

@[simp]
/-
**mdifferentiableOn_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_empty : MDiff[∅] f
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mdifferentiableOn_empty : MDiff[∅] f := fun _x hx ↦ hx.elim
/-
**mdifferentiableOn_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_univ : MDiff[univ] f ↔ MDiff f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mdifferentiableOn_univ : MDiff[univ] f ↔ MDiff f := by
  simp only [MDifferentiableOn, mdifferentiableWithinAt_univ, mfld_simps]; rfl
/-
**MDifferentiableOn.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.mdifferentiableAt (h : MDiff[s] f) (hx : s in 𝓝 x) : MDi
ffAt f x
参数：h : MDiff[s] f；hx : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mdifferentiableAt`：MDifferentiableWithinAt.mdiff
erentiableAt (h : MDiffAt[s] f x) (hs : s in 𝓝 x) : MDiffAt f x
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem MDifferentiableOn.mdifferentiableAt (h : MDiff[s] f) (hx : s ∈ 𝓝 x) : MDiffAt f x :=
  (h x (mem_of_mem_nhds hx)).mdifferentiableAt hx
/-
**MDifferentiable.mdifferentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.mdifferentiableOn (h : MDiff f) : MDiff[s] f
参数：h : MDiff f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableOn.mono`：MDifferentiableOn.mono (h : MDiff[t] f) (st : s 
subseteq t) : MDiff[s] f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mdifferentiableOn_univ`：mdifferentiableOn_univ : MDiff[univ] f ↔ MDiff f
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem MDifferentiable.mdifferentiableOn (h : MDiff f) : MDiff[s] f :=
  (mdifferentiableOn_univ.2 h).mono (subset_univ _)
/-
**mdifferentiableOn_of_locally_mdifferentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_of_locally_mdifferentiableOn (h : forall x in s, exists 
u, IsOpen u ∧ x in u ∧ MDiff[s inter u] f) : MDiff[s] f
参数：h : forall x in s, exists u, IsOpen u ∧ x in u ∧ MDiff[s inter u] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_inter`：mdifferentiableWithinAt_inter (ht : t in 
𝓝 x) : MDiffAt[s inter t] f x ↔ MDiffAt[s] f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
theorem mdifferentiableOn_of_locally_mdifferentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ MDiff[s ∩ u] f) : MDiff[s] f := by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (mdifferentiableWithinAt_inter (t_open.mem_nhds xt)).1 (ht x ⟨xs, xt⟩)
/-
**MDifferentiable.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.mdifferentiableAt (hf : MDiff f) : MDiffAt f x
参数：hf : MDiff f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MDifferentiable.mdifferentiableAt (hf : MDiff f) : MDiffAt f x :=
  hf x

/-!
### Relating differentiability in a manifold and differentiability in the model space
through extended charts
-/

/-
**mdifferentiableWithinAt_iff_target_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff_target_inter {f : M -> M'} {s : Set M} {x : M}
 : MDiffAt[s] f x ↔ ContinuousWithinAt f s x ∧ DifferentiableWithinAt 𝕜 (written
InExtChartAt I I' x f) ((extChartAt I x).target inter (extChartAt I x).symm ⁻¹' 
s) ((extChartAt I x) x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_iff'`：mdifferentiableWithinAt_iff' (f : M -> M')
 (s : Set M) (x : M) : MDifferentiableWithinAt I I' f s x ↔ ContinuousWithinAt f
 s x ∧ Differentia…
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_inter`：nhdsWithin_inter (a : α) (s t : Set α) : 𝓝[s inter t] 
a = 𝓝[s] a ⊓ 𝓝[t] a
· 使用定理 `nhdsWithin_extChartAt_target_eq`：nhdsWithin_extChartAt_target_eq (x : M)
 : 𝓝[(extChartAt I x).target] (extChartAt I x) x = 𝓝[range I] (extChartAt I x) x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
### Relating differentiability in a manifold and differentiability in the model 
space
through extended charts
-/
theorem mdifferentiableWithinAt_iff_target_inter {f : M → M'} {s : Set M} {x : M} :
    MDiffAt[s] f x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (writtenInExtChartAt I I' x f)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' s) ((extChartAt I x) x) := by
  rw [mdifferentiableWithinAt_iff']
  refine and_congr Iff.rfl (exists_congr fun f' => ?_)
  rw [inter_comm]
  simp only [HasFDerivWithinAt, nhdsWithin_inter, nhdsWithin_extChartAt_target_eq]

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. -/
/-
**mdifferentiableWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff : MDiffAt[s] f x ↔ ContinuousWithinAt f s x ∧ 
DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) ((ext
ChartAt I x).symm ⁻¹' s inter range I) (extChartAt I x x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
One can reformulate smoothness within a set at a point as continuity within this
 set at this
point, and smoothness in the corresponding extended chart.
-/
theorem mdifferentiableWithinAt_iff :
    MDiffAt[s] f x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x) := by
  simp_rw [MDifferentiableWithinAt, ChartedSpace.liftPropWithinAt_iff']; rfl

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. This form states smoothness of `f`
written in such a way that the set is restricted to lie within the domain/codomain of the
corresponding charts.
Even though this expression is more complicated than the one in `mdifferentiableWithinAt_iff`, it is
a smaller set, but their germs at `extChartAt I x x` are equal. It is sometimes useful to rewrite
using this in the goal.
-/
/-
**mdifferentiableWithinAt_iff_target_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff_target_inter' : MDiffAt[s] f x ↔ ContinuousWit
hinAt f s x ∧ DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I 
x).symm) ((extChartAt I x).target inter (extChartAt I x).symm ⁻¹' (s inter f ⁻¹'
 (extChartAt I' (f x)).source)) (extChartAt I x x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `differentiableWithinAt_congr_nhds`：differentiableWithinAt_congr_nhds {t 
: Set E} (hst : 𝓝[s] x = 𝓝[t] x) : DifferentiableWithinAt 𝕜 f s x ↔ Differentiab
leWithinAt 𝕜 f t x
· 使用定理 `ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range`：Cont
inuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range {f : M -> M'} {x 
: M} (hc : ContinuousWithinAt f s x) : 𝓝[(extChartAt I x…

--- 原说明 ---
One can reformulate smoothness within a set at a point as continuity within this
 set at this
point, and smoothness in the corresponding extended chart. This form states smoo
thness of `f`
written in such a way that the set is restricted to lie within the domain/codoma
in of the
corresponding charts.
Even though this expression is more complicated than the one in `mdifferentiable
WithinAt_iff`, it is
a smaller set, but their germs at `extChartAt I x x` are equal. It is sometimes 
useful to rewrite
using this in the goal.
-/
theorem mdifferentiableWithinAt_iff_target_inter' :
    MDiffAt[s] f x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩
            (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source))
          (extChartAt I x x) := by
  simp only [MDifferentiableWithinAt, liftPropWithinAt_iff']
  exact and_congr_right fun hc => differentiableWithinAt_congr_nhds <|
    hc.nhdsWithin_extChartAt_symm_preimage_inter_range

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart in the target. -/
/-
**mdifferentiableWithinAt_iff_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff_target : MDiffAt[s] f x ↔ ContinuousWithinAt f
 s x ∧ MDiffAt[s] (extChartAt I' (f x) ∘ f) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_iff_left_of_imp`：∀ {a b : Prop}, (a → b) → (a ∧ b ↔ a)
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `continuousAt_extChartAt`：continuousAt_extChartAt (x : M) : ContinuousAt 
(extChartAt I x) x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.refl_apply`：∀ (X : Type u_7) [inst : TopologicalSp
ace X], ↑(OpenPartialHomeomorph.refl X) = id
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
One can reformulate smoothness within a set at a point as continuity within this
 set at this
point, and smoothness in the corresponding extended chart in the target.
-/
theorem mdifferentiableWithinAt_iff_target :
    MDiffAt[s] f x ↔ ContinuousWithinAt f s x ∧ MDiffAt[s] (extChartAt I' (f x) ∘ f) x := by
  simp_rw [MDifferentiableWithinAt, liftPropWithinAt_iff', ← and_assoc]
  have cont :
    ContinuousWithinAt f s x ∧ ContinuousWithinAt (extChartAt I' (f x) ∘ f) s x ↔
        ContinuousWithinAt f s x :=
      and_iff_left_of_imp <| (continuousAt_extChartAt _).comp_continuousWithinAt
  simp_rw [cont, DifferentiableWithinAtProp, extChartAt, OpenPartialHomeomorph.extend,
    PartialEquiv.coe_trans, ModelWithCorners.toPartialEquiv_coe,
    OpenPartialHomeomorph.coe_toPartialEquiv, modelWithCornersSelf_coe, chartAt_self_eq,
    OpenPartialHomeomorph.refl_apply]
  rfl
/-
**mdifferentiableAt_iff_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_iff_target {x : M} : MDiffAt f x ↔ ContinuousAt f x ∧ MD
iffAt (extChartAt I' (f x) ∘ f) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用定理 `mdifferentiableWithinAt_iff_target`：mdifferentiableWithinAt_iff_target :
 MDiffAt[s] f x ↔ ContinuousWithinAt f s x ∧ MDiffAt[s] (extChartAt I' (f x) ∘ f
) x
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mdifferentiableAt_iff_target {x : M} :
    MDiffAt f x ↔ ContinuousAt f x ∧ MDiffAt (extChartAt I' (f x) ∘ f) x := by
  rw [← mdifferentiableWithinAt_univ, ← mdifferentiableWithinAt_univ,
    mdifferentiableWithinAt_iff_target, continuousWithinAt_univ]

section IsManifold

variable {e : OpenPartialHomeomorph M H} {e' : OpenPartialHomeomorph M' H'}

open IsManifold

/-
**mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (he : e in maximalA
tlas I 1 M) (hx : x in e.source) : MDiffAt[s] f x ↔ MDiffAt[(e.extend I).symm ⁻¹
' s inter range I] (f ∘ (e.extend I).symm) (e.extend I x)
参数：he : e in maximalAtlas I 1 M；hx : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_source
`：liftPropWithinAt_indep_chart_source (he : e in G.maximalAtlas M) (xe : x in e.
source) : LiftPropWithinAt P g s x ↔ LiftPropWithinAt P (g ∘ e…
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.extend_symm_continuousWithinAt_comp_right_iff`：ext
end_symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {g : M -> X}
 {s : Set M} {x : M} : ContinuousWithinAt (g ∘ (f.extend …
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (he : e ∈ maximalAtlas I 1 M)
    (hx : x ∈ e.source) :
    MDiffAt[s] f x ↔
      MDiffAt[(e.extend I).symm ⁻¹' s ∩ range I] (f ∘ (e.extend I).symm) (e.extend I x) := by
  have h2x := hx; rw [← e.extend_source (I := I)] at h2x
  simp_rw [MDifferentiableWithinAt,
    differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_source he hx,
    StructureGroupoid.liftPropWithinAt_self_source,
    e.extend_symm_continuousWithinAt_comp_right_iff, differentiableWithinAtProp_self_source,
    DifferentiableWithinAtProp, Function.comp, e.left_inv hx, (e.extend I).left_inv h2x]
  rfl
/-
**mdifferentiableWithinAt_iff_source_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff_source_of_mem_source [IsManifold I 1 M] {x' : 
M} (hx' : x' in (chartAt H x).source) : MDiffAt[s] f x' ↔ MDiffAt[(extChartAt I 
x).symm ⁻¹' s inter range I] (f ∘ (extChartAt I x).symm) (extChartAt I x x')
参数：hx' : x' in (chartAt H x).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas`：mdifferentiableW
ithinAt_iff_source_of_mem_maximalAtlas (he : e in maximalAtlas I 1 M) (hx : x in
 e.source) : MDiffAt[s] f x ↔ MDiffAt[(e.ext…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
-/
theorem mdifferentiableWithinAt_iff_source_of_mem_source
    [IsManifold I 1 M] {x' : M} (hx' : x' ∈ (chartAt H x).source) :
    MDiffAt[s] f x' ↔
      MDiffAt[(extChartAt I x).symm ⁻¹' s ∩ range I] (f ∘ (extChartAt I x).symm)
        (extChartAt I x x') :=
  mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hx'
/-
**mdifferentiableAt_iff_source_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_iff_source_of_mem_source [IsManifold I 1 M] {x' : M} (hx
' : x' in (chartAt H x).source) : MDiffAt f x' ↔ MDiffAt[range I] (f ∘ (extChart
At I x).symm) (extChartAt I x x')
参数：hx' : x' in (chartAt H x).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_iff_source_of_mem_source`：mdifferentiableWithinA
t_iff_source_of_mem_source [IsManifold I 1 M] {x' : M} (hx' : x' in (chartAt H x
).source) : MDiffAt[s] f x' ↔ MDiffAt[…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mdifferentiableAt_iff_source_of_mem_source
    [IsManifold I 1 M] {x' : M} (hx' : x' ∈ (chartAt H x).source) :
    MDiffAt f x' ↔ MDiffAt[range I] (f ∘ (extChartAt I x).symm) (extChartAt I x x') := by
  simp_rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_iff_source_of_mem_source hx',
    preimage_univ, univ_inter]
/-
**mdifferentiableWithinAt_iff_target_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff_target_of_mem_source [IsManifold I' 1 M'] {x :
 M} {y : M'} (hy : f x in (chartAt H' y).source) : MDiffAt[s] f x ↔ ContinuousWi
thinAt f s x ∧ MDiffAt[s] (extChartAt I' y ∘ f) x
参数：hy : f x in (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart_target
`：liftPropWithinAt_indep_chart_target (hf : f in G'.maximalAtlas M') (xf : g x i
n f.source) : LiftPropWithinAt P g s x ↔ ContinuousWithinAt g …
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
· 使用定理 `and_congr_right`：∀ {a b c : Prop}, (a → (b ↔ c)) → (a ∧ b ↔ a ∧ c)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ContinuousAt.comp_continuousWithinAt`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst_2
 : TopologicalSpace γ] {f …
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `continuousAt_extChartAt'`：continuousAt_extChartAt' {x x' : M} (h : x' in
 (extChartAt I x).source) : ContinuousAt (extChartAt I x) x'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mdifferentiableWithinAt_iff_target_of_mem_source
    [IsManifold I' 1 M'] {x : M} {y : M'} (hy : f x ∈ (chartAt H' y).source) :
    MDiffAt[s] f x ↔ ContinuousWithinAt f s x ∧ MDiffAt[s] (extChartAt I' y ∘ f) x := by
  simp_rw [MDifferentiableWithinAt]
  rw [differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart_target
      (chart_mem_maximalAtlas y) hy, and_congr_right]
  intro hf
  simp_rw [StructureGroupoid.liftPropWithinAt_self_target]
  simp_rw [((chartAt H' y).continuousAt hy).comp_continuousWithinAt hf]
  rw [← extChartAt_source I'] at hy
  simp_rw [(continuousAt_extChartAt' hy).comp_continuousWithinAt hf]
  rfl
/-
**mdifferentiableAt_iff_target_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_iff_target_of_mem_source [IsManifold I' 1 M'] {x : M} {y
 : M'} (hy : f x in (chartAt H' y).source) : MDiffAt f x ↔ ContinuousAt f x ∧ MD
iffAt (extChartAt I' y ∘ f) x
参数：hy : f x in (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用定理 `mdifferentiableWithinAt_iff_target_of_mem_source`：mdifferentiableWithinA
t_iff_target_of_mem_source [IsManifold I' 1 M'] {x : M} {y : M'} (hy : f x in (c
hartAt H' y).source) : MDiffAt[s] f x …
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mdifferentiableAt_iff_target_of_mem_source
    [IsManifold I' 1 M'] {x : M} {y : M'} (hy : f x ∈ (chartAt H' y).source) :
    MDiffAt f x ↔ ContinuousAt f x ∧ MDiffAt (extChartAt I' y ∘ f) x := by
  rw [← mdifferentiableWithinAt_univ, mdifferentiableWithinAt_iff_target_of_mem_source hy,
    continuousWithinAt_univ, ← mdifferentiableWithinAt_univ]
/-
**mdifferentiableWithinAt_iff_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff_of_mem_maximalAtlas {x : M} (he : e in maximal
Atlas I 1 M) (he' : e' in maximalAtlas I' 1 M') (hx : x in e.source) (hy : f x i
n e'.source) : MDiffAt[s] f x ↔ ContinuousWithinAt f s x ∧ DifferentiableWithinA
t 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) ((e.extend I).symm ⁻¹' s inter range 
I) (e.extend I x)
参数：he : e in maximalAtlas I 1 M；he' : e' in maximalAtlas I' 1 M'；hx : x in e.sou
rce；hy : f x in e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_indep_chart`：liftP
ropWithinAt_indep_chart (he : e in G.maximalAtlas M) (xe : x in e.source) (hf : 
f in G'.maximalAtlas M') (xf : g x in f.source) : LiftP…
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
-/
theorem mdifferentiableWithinAt_iff_of_mem_maximalAtlas {x : M} (he : e ∈ maximalAtlas I 1 M)
    (he' : e' ∈ maximalAtlas I' 1 M') (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
    MDiffAt[s] f x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm)
          ((e.extend I).symm ⁻¹' s ∩ range I) (e.extend I x) :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_indep_chart he hx he' hy

/-- An alternative formulation of `mdifferentiableWithinAt_iff_of_mem_maximalAtlas`
if the set if `s` lies in `e.source`. -/
/-
**mdifferentiableWithinAt_iff_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff_image {x : M} (he : e in maximalAtlas I 1 M) (
he' : e' in maximalAtlas I' 1 M') (hs : s subseteq e.source) (hx : x in e.source
) (hy : f x in e'.source) : MDiffAt[s] f x ↔ ContinuousWithinAt f s x ∧ Differen
tiableWithinAt 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) (e.ext
end I x)
参数：he : e in maximalAtlas I 1 M；he' : e' in maximalAtlas I' 1 M'；hs : s subseteq
 e.source；hx : x in e.source；hy : f x in e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_iff_of_mem_maximalAtlas`：mdifferentiableWithinAt
_iff_of_mem_maximalAtlas {x : M} (he : e in maximalAtlas I 1 M) (he' : e' in max
imalAtlas I' 1 M') (hx : x in e.sourc…
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `differentiableWithinAt_congr_nhds`：differentiableWithinAt_congr_nhds {t 
: Set E} (hst : 𝓝[s] x = 𝓝[t] x) : DifferentiableWithinAt 𝕜 f s x ↔ Differentiab
leWithinAt 𝕜 f t x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `OpenPartialHomeomorph.extend_symm_preimage_inter_range_eventuallyEq`：ext
end_symm_preimage_inter_range_eventuallyEq {s : Set M} {x : M} (hs : s subseteq 
f.source) (hx : x in f.source) : ((f.extend I).symm ⁻¹' s…

--- 原说明 ---
An alternative formulation of `mdifferentiableWithinAt_iff_of_mem_maximalAtlas`
if the set if `s` lies in `e.source`.
-/
theorem mdifferentiableWithinAt_iff_image {x : M} (he : e ∈ maximalAtlas I 1 M)
    (he' : e' ∈ maximalAtlas I' 1 M') (hs : s ⊆ e.source) (hx : x ∈ e.source)
    (hy : f x ∈ e'.source) :
    MDiffAt[s] f x ↔
      ContinuousWithinAt f s x ∧
        DifferentiableWithinAt 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s)
          (e.extend I x) := by
  rw [mdifferentiableWithinAt_iff_of_mem_maximalAtlas he he' hx hy, and_congr_right_iff]
  refine fun _ => differentiableWithinAt_congr_nhds ?_
  simp_rw [nhdsWithin_eq_iff_eventuallyEq, e.extend_symm_preimage_inter_range_eventuallyEq hs hx]

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in any chart containing that point. -/
/-
**mdifferentiableWithinAt_iff_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff_of_mem_source [IsManifold I 1 M] [IsManifold I
' 1 M'] {x' : M} {y : M'} (hx : x' in (chartAt H x).source) (hy : f x' in (chart
At H' y).source) : MDiffAt[s] f x' ↔ ContinuousWithinAt f s x' ∧ DifferentiableW
ithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) ((extChartAt I x).symm ⁻
¹' s inter range I) (extChartAt I x x')
参数：hx : x' in (chartAt H x).source；hy : f x' in (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableWithinAt_iff_of_mem_maximalAtlas`：mdifferentiableWithinAt
_iff_of_mem_maximalAtlas {x : M} (he : e in maximalAtlas I 1 M) (he' : e' in max
imalAtlas I' 1 M') (hx : x in e.sourc…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M

--- 原说明 ---
One can reformulate smoothness within a set at a point as continuity within this
 set at this
point, and smoothness in any chart containing that point.
-/
theorem mdifferentiableWithinAt_iff_of_mem_source [IsManifold I 1 M] [IsManifold I' 1 M']
    {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    MDiffAt[s] f x' ↔
      ContinuousWithinAt f s x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).symm ⁻¹' s ∩ range I) (extChartAt I x x') :=
  mdifferentiableWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hx hy

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in any chart containing that point. Version requiring differentiability
in the target instead of `range I`. -/
/-
**mdifferentiableWithinAt_iff_of_mem_source'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_iff_of_mem_source' [IsManifold I 1 M] [IsManifold 
I' 1 M'] {x' : M} {y : M'} (hx : x' in (chartAt H x).source) (hy : f x' in (char
tAt H' y).source) : MDiffAt[s] f x' ↔ ContinuousWithinAt f s x' ∧ Differentiable
WithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) ((extChartAt I x).targe
t inter (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' y).source)) (ext
ChartAt I x x')
参数：hx : x' in (chartAt H x).source；hy : f x' in (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mdifferentiableWithinAt_iff_of_mem_source`：mdifferentiableWithinAt_iff_o
f_mem_source [IsManifold I 1 M] [IsManifold I' 1 M'] {x' : M} {y : M'} (hx : x' 
in (chartAt H x).source) (hy : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `differentiableWithinAt_congr_nhds`：differentiableWithinAt_congr_nhds {t 
: Set E} (hst : 𝓝[s] x = 𝓝[t] x) : DifferentiableWithinAt 𝕜 f s x ↔ Differentiab
leWithinAt 𝕜 f t x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.image_source_inter_eq'`：image_source_inter_eq' (s : Set α) 
: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `map_extChartAt_nhdsWithin_eq_image'`：map_extChartAt_nhdsWithin_eq_image'
 {x y : M} (hy : y in (extChartAt I x).source) : map (extChartAt I x) (𝓝[s] y) =
 𝓝[extChartAt I x '' ((ex…
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `map_extChartAt_nhdsWithin'`：map_extChartAt_nhdsWithin' {x y : M} (hy : y
 in (extChartAt I x).source) : map (extChartAt I x) (𝓝[s] y) = 𝓝[(extChartAt I x
).symm ⁻¹' s int…
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `extChartAt_source_mem_nhds'`：extChartAt_source_mem_nhds' {x x' : M} (h :
 x' in (extChartAt I x).source) : (extChartAt I x).source in 𝓝 x'

--- 原说明 ---
One can reformulate smoothness within a set at a point as continuity within this
 set at this
point, and smoothness in any chart containing that point. Version requiring diff
erentiability
in the target instead of `range I`.
-/
theorem mdifferentiableWithinAt_iff_of_mem_source' [IsManifold I 1 M] [IsManifold I' 1 M']
    {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    MDiffAt[s] f x' ↔
      ContinuousWithinAt f s x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
          ((extChartAt I x).target ∩ (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source))
          (extChartAt I x x') := by
  refine (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans ?_
  rw [← extChartAt_source I] at hx
  rw [← extChartAt_source I'] at hy
  rw [and_congr_right_iff]
  set e := extChartAt I x; set e' := extChartAt I' (f x)
  refine fun hc => differentiableWithinAt_congr_nhds ?_
  rw [← e.image_source_inter_eq', ← map_extChartAt_nhdsWithin_eq_image' hx,
    ← map_extChartAt_nhdsWithin' hx, inter_comm, nhdsWithin_inter_of_mem]
  exact hc (extChartAt_source_mem_nhds' hy)
/-
**mdifferentiableAt_iff_of_mem_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_iff_of_mem_source [IsManifold I 1 M] [IsManifold I' 1 M'
] {x' : M} {y : M'} (hx : x' in (chartAt H x).source) (hy : f x' in (chartAt H' 
y).source) : MDiffAt f x' ↔ ContinuousAt f x' ∧ DifferentiableWithinAt 𝕜 (extCha
rtAt I' y ∘ f ∘ (extChartAt I x).symm) (range I) (extChartAt I x x')
参数：hx : x' in (chartAt H x).source；hy : f x' in (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mdifferentiableWithinAt_iff_of_mem_source`：mdifferentiableWithinAt_iff_o
f_mem_source [IsManifold I 1 M] [IsManifold I' 1 M'] {x' : M} {y : M'} (hx : x' 
in (chartAt H x).source) (hy : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousWithinAt_univ`：continuousWithinAt_univ (f : α -> β) (x : α) : 
ContinuousWithinAt f Set.univ x ↔ ContinuousAt f x
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mdifferentiableAt_iff_of_mem_source [IsManifold I 1 M] [IsManifold I' 1 M']
    {x' : M} {y : M'} (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    MDiffAt f x' ↔
      ContinuousAt f x' ∧
        DifferentiableWithinAt 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (range I)
          (extChartAt I x x') :=
  (mdifferentiableWithinAt_iff_of_mem_source hx hy).trans <| by
    rw [continuousWithinAt_univ, preimage_univ, univ_inter]
/-
**mdifferentiableOn_iff_of_mem_maximalAtlas** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_iff_of_mem_maximalAtlas (he : e in maximalAtlas I 1 M) (
he' : e' in maximalAtlas I' 1 M') (hs : s subseteq e.source) (h2s : MapsTo f s e
'.source) : MDiff[s] f ↔ ContinuousOn f s ∧ DifferentiableOn 𝕜 (e'.extend I' ∘ f
 ∘ (e.extend I).symm) (e.extend I '' s)
参数：he : e in maximalAtlas I 1 M；he' : e' in maximalAtlas I' 1 M'；hs : s subseteq
 e.source；h2s : MapsTo f s e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `mdifferentiableWithinAt_iff_image`：mdifferentiableWithinAt_iff_image {x 
: M} (he : e in maximalAtlas I 1 M) (he' : e' in maximalAtlas I' 1 M') (hs : s s
ubseteq e.source) (hx :…
-/
theorem mdifferentiableOn_iff_of_mem_maximalAtlas (he : e ∈ maximalAtlas I 1 M)
    (he' : e' ∈ maximalAtlas I' 1 M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    MDiff[s] f ↔
      ContinuousOn f s ∧
        DifferentiableOn 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) := by
  simp_rw [ContinuousOn, DifferentiableOn, Set.forall_mem_image, ← forall_and, MDifferentiableOn]
  exact forall₂_congr fun x hx => mdifferentiableWithinAt_iff_image he he' hs (hs hx) (h2s hx)

/-- Differentiability on a set is equivalent to differentiability in the extended charts. -/
/-
**mdifferentiableOn_iff_of_mem_maximalAtlas'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_iff_of_mem_maximalAtlas' (he : e in maximalAtlas I 1 M) 
(he' : e' in maximalAtlas I' 1 M') (hs : s subseteq e.source) (h2s : MapsTo f s 
e'.source) : MDiff[s] f ↔ DifferentiableOn 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).sy
mm) (e.extend I '' s)
参数：he : e in maximalAtlas I 1 M；he' : e' in maximalAtlas I' 1 M'；hs : s subseteq
 e.source；h2s : MapsTo f s e'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `mdifferentiableOn_iff_of_mem_maximalAtlas`：mdifferentiableOn_iff_of_mem_
maximalAtlas (he : e in maximalAtlas I 1 M) (he' : e' in maximalAtlas I' 1 M') (
hs : s subseteq e.source) (h2s …
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OpenPartialHomeomorph.continuousOn_writtenInExtend_iff`：continuousOn_wri
ttenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M -> M'} (hs : s subset
eq f.source) (hmaps : MapsTo g s f'.source) …
· 使用定理 `DifferentiableOn.continuousOn`：DifferentiableOn.continuousOn (h : Differ
entiableOn 𝕜 f s) : ContinuousOn f s
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …

--- 原说明 ---
Differentiability on a set is equivalent to differentiability in the extended ch
arts.
-/
theorem mdifferentiableOn_iff_of_mem_maximalAtlas' (he : e ∈ maximalAtlas I 1 M)
    (he' : e' ∈ maximalAtlas I' 1 M') (hs : s ⊆ e.source) (h2s : MapsTo f s e'.source) :
    MDiff[s] f ↔
      DifferentiableOn 𝕜 (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) :=
  (mdifferentiableOn_iff_of_mem_maximalAtlas he he' hs h2s).trans <| and_iff_right_of_imp fun h ↦
    (e.continuousOn_writtenInExtend_iff hs h2s).1 h.continuousOn

variable [IsManifold I 1 M] [IsManifold I' 1 M']

/-- If the set where you want `f` to be smooth lies entirely in a single chart, and `f` maps it
into a single chart, the smoothness of `f` on that set can be expressed by purely looking in
these charts.
Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹' s` to ensure
that this set lies in `(extChartAt I x).target`. -/
/-
**mdifferentiableOn_iff_of_subset_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_iff_of_subset_source {x : M} {y : M'} (hs : s subseteq (
chartAt H x).source) (h2s : MapsTo f s (chartAt H' y).source) : MDiff[s] f ↔ Con
tinuousOn f s ∧ DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
 (extChartAt I x '' s)
参数：hs : s subseteq (chartAt H x).source；h2s : MapsTo f s (chartAt H' y).source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableOn_iff_of_mem_maximalAtlas`：mdifferentiableOn_iff_of_mem_
maximalAtlas (he : e in maximalAtlas I 1 M) (he' : e' in maximalAtlas I' 1 M') (
hs : s subseteq e.source) (h2s …
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M

--- 原说明 ---
If the set where you want `f` to be smooth lies entirely in a single chart, and 
`f` maps it
into a single chart, the smoothness of `f` on that set can be expressed by purel
y looking in
these charts.
Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹
' s` to ensure
that this set lies in `(extChartAt I x).target`.
-/
theorem mdifferentiableOn_iff_of_subset_source
    {x : M} {y : M'} (hs : s ⊆ (chartAt H x).source) (h2s : MapsTo f s (chartAt H' y).source) :
    MDiff[s] f ↔
      ContinuousOn f s ∧
        DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) :=
  mdifferentiableOn_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

/-- If the set where you want `f` to be smooth lies entirely in a single chart, and `f` maps it
into a single chart, the smoothness of `f` on that set can be expressed by purely looking in
these charts.
Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹' s` to ensure
that this set lies in `(extChartAt I x).target`. -/
/-
**mdifferentiableOn_iff_of_subset_source'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_iff_of_subset_source' {x : M} {y : M'} (hs : s subseteq 
(extChartAt I x).source) (h2s : MapsTo f s (extChartAt I' y).source) : MDiff[s] 
f ↔ DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt
 I x '' s)
参数：hs : s subseteq (extChartAt I x).source；h2s : MapsTo f s (extChartAt I' y).so
urce。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableOn_iff_of_mem_maximalAtlas'`：mdifferentiableOn_iff_of_mem
_maximalAtlas' (he : e in maximalAtlas I 1 M) (he' : e' in maximalAtlas I' 1 M')
 (hs : s subseteq e.source) (h2s…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source

--- 原说明 ---
If the set where you want `f` to be smooth lies entirely in a single chart, and 
`f` maps it
into a single chart, the smoothness of `f` on that set can be expressed by purel
y looking in
these charts.
Note: this lemma uses `extChartAt I x '' s` instead of `(extChartAt I x).symm ⁻¹
' s` to ensure
that this set lies in `(extChartAt I x).target`.
-/
theorem mdifferentiableOn_iff_of_subset_source'
    {x : M} {y : M'} (hs : s ⊆ (extChartAt I x).source)
    (h2s : MapsTo f s (extChartAt I' y).source) :
    MDiff[s] f ↔
        DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) (extChartAt I x '' s) := by
  rw [extChartAt_source] at hs h2s
  exact mdifferentiableOn_iff_of_mem_maximalAtlas' (chart_mem_maximalAtlas x)
    (chart_mem_maximalAtlas y) hs h2s

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart. -/
/-
**mdifferentiableOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_iff : MDiff[s] f ↔ ContinuousOn f s ∧ forall (x : M) (y 
: M'), DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) ((extCha
rtAt I x).target inter (extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' y
).source))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_iff_of_mem_source`：mdifferentiableWithinAt_iff_o
f_mem_source [IsManifold I 1 M] [IsManifold I' 1 M'] {x' : M} {y : M'} (hx : x' 
in (chartAt H x).source) (hy : …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_iff`：liftPropWithi
nAt_iff {f : M -> M'} : LiftPropWithinAt P f s x ↔ ContinuousWithinAt f s x ∧ P 
(chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((c…
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x

--- 原说明 ---
One can reformulate smoothness on a set as continuity on this set, and smoothnes
s in any
extended chart.
-/
theorem mdifferentiableOn_iff :
    MDiff[s] f ↔
      ContinuousOn f s ∧
        ∀ (x : M) (y : M'),
          DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' y).source)) := by
  constructor
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x y z hz => ?_⟩
    simp only [mfld_simps] at hz
    let w := (extChartAt I x).symm z
    have : w ∈ s := by simp only [w, hz, mfld_simps]
    specialize h w this
    have w1 : w ∈ (chartAt H x).source := by simp only [w, hz, mfld_simps]
    have w2 : f w ∈ (chartAt H' y).source := by simp only [w, hz, mfld_simps]
    convert! ((mdifferentiableWithinAt_iff_of_mem_source w1 w2).mp h).2.mono _
    · simp only [w, hz, mfld_simps]
    · mfld_set_tac
  · rintro ⟨hcont, hdiff⟩ x hx
    refine differentiableWithinAt_localInvariantProp.liftPropWithinAt_iff.mpr ?_
    refine ⟨hcont x hx, ?_⟩
    dsimp [DifferentiableWithinAtProp]
    convert! hdiff x (f x) (extChartAt I x x) (by simp only [hx, mfld_simps]) using 1
    mfld_set_tac

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart in the target. -/
/-
**mdifferentiableOn_iff_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_iff_target : MDiff[s] f ↔ ContinuousOn f s ∧ forall y : 
M', MDiff[s inter f ⁻¹' (extChartAt I' y).source] (extChartAt I' y ∘ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsManifold.instOfNatWithTopENat_1`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `IsManifold.instOfNatWithTopENat_2`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `IsManifold.instOfTopWithTopENat`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ModelWithCorners.continuous`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousOn.comp_inter`：ContinuousOn.comp_inter {g : β -> γ} {t : Set β
} (hg : ContinuousOn g t) (hf : ContinuousOn f s) : ContinuousOn (g ∘ f) (s inte
r f ⁻¹' t)
· 使用定理 `PartialHomeomorph.continuousOn_toFun`：∀ {X : Type u_7} {Y : Type u_8} [i
nst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : PartialHomeomo
rph X Y), ContinuousOn (↑s…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
One can reformulate smoothness on a set as continuity on this set, and smoothnes
s in any
extended chart in the target.
-/
theorem mdifferentiableOn_iff_target :
    MDiff[s] f ↔
      ContinuousOn f s ∧
        ∀ y : M', MDiff[s ∩ f ⁻¹' (extChartAt I' y).source] (extChartAt I' y ∘ f) := by
  simp only [mdifferentiableOn_iff, ModelWithCorners.source_eq, chartAt_self_eq,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, extChartAt,
    OpenPartialHomeomorph.extend, Set.preimage_univ, Set.inter_univ, and_congr_right_iff]
  intro h
  constructor
  · refine fun h' y => ⟨?_, fun x _ => h' x y⟩
    have h'' : ContinuousOn _ univ := (ModelWithCorners.continuous I').continuousOn
    convert! (h''.comp_inter (chartAt H' y).continuousOn_toFun).comp_inter h
    simp
  · exact fun h' x y => (h' y).2 x 0

/-- One can reformulate smoothness as continuity and smoothness in any extended chart. -/
/-
**mdifferentiable_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_iff : MDiff f ↔ Continuous f ∧ forall (x : M) (y : M'), Di
fferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm) ((extChartAt I x)
.target inter (extChartAt I x).symm ⁻¹' f ⁻¹' (extChartAt I' y).source)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
One can reformulate smoothness as continuity and smoothness in any extended char
t.
-/
theorem mdifferentiable_iff :
    MDiff f ↔
      Continuous f ∧
        ∀ (x : M) (y : M'),
          DifferentiableOn 𝕜 (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
            ((extChartAt I x).target ∩
              (extChartAt I x).symm ⁻¹' f ⁻¹' (extChartAt I' y).source) := by
  simp [← mdifferentiableOn_univ, mdifferentiableOn_iff, continuousOn_univ]

/-- One can reformulate smoothness as continuity and smoothness in any extended chart in the
target. -/
/-
**mdifferentiable_iff_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_iff_target : MDiff f ↔ Continuous f ∧ forall y : M', MDiff
[f ⁻¹' (extChartAt I' y).source] (extChartAt I' y ∘ f)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableOn_univ`：mdifferentiableOn_univ : MDiff[univ] f ↔ MDiff f
· 使用定理 `mdifferentiableOn_iff_target`：mdifferentiableOn_iff_target : MDiff[s] f 
↔ ContinuousOn f s ∧ forall y : M', MDiff[s inter f ⁻¹' (extChartAt I' y).source
] (extChartAt I' y…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
One can reformulate smoothness as continuity and smoothness in any extended char
t in the
target.
-/
theorem mdifferentiable_iff_target :
    MDiff f ↔
      Continuous f ∧ ∀ y : M',
        MDiff[f ⁻¹' (extChartAt I' y).source] (extChartAt I' y ∘ f) := by
  rw [← mdifferentiableOn_univ, mdifferentiableOn_iff_target]
  simp [continuousOn_univ]

end IsManifold

/-! ### Deducing differentiability from smoothness -/

variable {n : WithTop ℕ∞}

/-
**ContMDiffWithinAt.mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffWithinAt.mdifferentiableWithinAt (hf : CMDiffAt[s] n f x) (hn : n
 != 0) : MDiffAt[s] f x
参数：hf : CMDiffAt[s] n f x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableWithinAt_iff`：mdifferentiableWithinAt_iff : MDiffAt[s] f 
x ↔ ContinuousWithinAt f s x ∧ DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f
 ∘ (extChartAt I …
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `DifferentiableWithinAt.mono`：DifferentiableWithinAt.mono (h : Differenti
ableWithinAt 𝕜 f t x) (st : s subseteq t) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `mdifferentiableWithinAt_inter'`：mdifferentiableWithinAt_inter' (ht : t i
n 𝓝[s] x) : MDiffAt[s inter t] f x ↔ MDiffAt[s] f x
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin`：ContinuousWithinAt.preimage_
mem_nhdsWithin {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝 (f x)) : 
f ⁻¹' t in 𝓝[s] x
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
-/
theorem ContMDiffWithinAt.mdifferentiableWithinAt (hf : CMDiffAt[s] n f x) (hn : n ≠ 0) :
    MDiffAt[s] f x := by
  suffices h : MDiffAt[s ∩ f ⁻¹' (extChartAt I' (f x)).source] f x by
    rwa [mdifferentiableWithinAt_inter'] at h
    apply hf.1.preimage_mem_nhdsWithin
    exact extChartAt_source_mem_nhds (f x)
  rw [mdifferentiableWithinAt_iff]
  exact ⟨hf.1.mono inter_subset_left, (hf.2.differentiableWithinAt hn).mono (by mfld_set_tac)⟩
/-
**ContMDiffAt.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffAt.mdifferentiableAt (hf : CMDiffAt n f x) (hn : n != 0) : MDiffA
t f x
参数：hf : CMDiffAt n f x；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用定理 `ContMDiffWithinAt.mdifferentiableWithinAt`：ContMDiffWithinAt.mdifferenti
ableWithinAt (hf : CMDiffAt[s] n f x) (hn : n != 0) : MDiffAt[s] f x
-/
theorem ContMDiffAt.mdifferentiableAt (hf : CMDiffAt n f x) (hn : n ≠ 0) : MDiffAt f x :=
  mdifferentiableWithinAt_univ.1 <| ContMDiffWithinAt.mdifferentiableWithinAt hf hn
/-
**ContMDiff.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.mdifferentiableAt (hf : CMDiff n f) (hn : n != 0) : MDiffAt f x
参数：hf : CMDiff n f；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
-/
theorem ContMDiff.mdifferentiableAt (hf : CMDiff n f) (hn : n ≠ 0) : MDiffAt f x :=
  hf.contMDiffAt.mdifferentiableAt hn
/-
**ContMDiff.mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.mdifferentiableWithinAt (hf : CMDiff n f) (hn : n != 0) : MDiffA
t[s] f x
参数：hf : CMDiff n f；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
-/
theorem ContMDiff.mdifferentiableWithinAt (hf : CMDiff n f) (hn : n ≠ 0) : MDiffAt[s] f x :=
  (hf.contMDiffAt.mdifferentiableAt hn).mdifferentiableWithinAt
/-
**ContMDiffOn.mdifferentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiffOn.mdifferentiableOn (hf : CMDiff[s] n f) (hn : n != 0) : MDiff[s
] f
参数：hf : CMDiff[s] n f；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffWithinAt.mdifferentiableWithinAt`：ContMDiffWithinAt.mdifferenti
ableWithinAt (hf : CMDiffAt[s] n f x) (hn : n != 0) : MDiffAt[s] f x
-/
theorem ContMDiffOn.mdifferentiableOn (hf : CMDiff[s] n f) (hn : n ≠ 0) : MDiff[s] f :=
  fun x hx => (hf x hx).mdifferentiableWithinAt hn
/-
**ContMDiff.mdifferentiable** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContMDiff.mdifferentiable (hf : CMDiff n f) (hn : n != 0) : MDiff f
参数：hf : CMDiff n f；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
-/
theorem ContMDiff.mdifferentiable (hf : CMDiff n f) (hn : n ≠ 0) : MDiff f :=
  fun x => (hf x).mdifferentiableAt hn
/-
**MDifferentiableOn.continuousOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.continuousOn (h : MDiff[s] f) : ContinuousOn f s
参数：h : MDiff[s] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.continuousWithinAt`：MDifferentiableWithinAt.cont
inuousWithinAt {f : M -> M'} {s : Set M} {x : M} (hf : MDifferentiableWithinAt I
 I' f s x) : ContinuousWithinAt …
-/
theorem MDifferentiableOn.continuousOn (h : MDiff[s] f) : ContinuousOn f s :=
  fun x hx => (h x hx).continuousWithinAt
/-
**MDifferentiable.continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.continuous (h : MDiff f) : Continuous f
参数：h : MDiff f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `MDifferentiableAt.continuousAt`：MDifferentiableAt.continuousAt {f : M ->
 M'} {x : M} (hf : MDifferentiableAt I I' f x) : ContinuousAt f x
-/
theorem MDifferentiable.continuous (h : MDiff f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).continuousAt

/-! ### Deriving continuity from differentiability on manifolds -/

/-
**writtenInExtChartAt_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_comp (h : ContinuousWithinAt f s x) : writtenInExtChar
tAt I I'' x (g ∘ f) =ᶠ[𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt 
I x x)] (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f)
参数：h : ContinuousWithinAt f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `extChartAt_preimage_mem_nhdsWithin`：extChartAt_preimage_mem_nhdsWithin {
x : M} (ht : t in 𝓝[s] x) : (extChartAt I x).symm ⁻¹' t in 𝓝[(extChartAt I x).sy
mm ⁻¹' s inter range I] …
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin`：ContinuousWithinAt.preimage_
mem_nhdsWithin {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝 (f x)) : 
f ⁻¹' t in 𝓝[s] x
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Deriving continuity from differentiability on manifolds
-/
theorem writtenInExtChartAt_comp (h : ContinuousWithinAt f s x) :
    writtenInExtChartAt I I'' x (g ∘ f)
      =ᶠ[𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x x)]
        (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f) := by
  apply
    @Filter.mem_of_superset _ _ (f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source) _
      (extChartAt_preimage_mem_nhdsWithin
        (h.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _)))
  mfld_set_tac

variable {f' f₀' f₁' : TangentSpace% x →L[𝕜] TangentSpace% (f x)}
  {g' : TangentSpace% (f x) →L[𝕜] TangentSpace% (g (f x))}

set_option backward.isDefEq.respectTransparency false in
/-- `UniqueMDiffWithinAt` achieves its goal: it implies the uniqueness of the derivative. -/
protected nonrec theorem UniqueMDiffWithinAt.eq (U : UniqueMDiffAt[s] x)
    (h : HasMFDerivAt[s] f x f') (h₁ : HasMFDerivAt[s] f x f₁') : f' = f₁' := by
  -- `by apply` because the instances can be found in the term but not in the goal.
  apply U.eq h.2 h₁.2

/-
**UniqueMDiffOn.eq** 是 Mathlib 中的一个定理，位于命名空间 `UniqueMDiffOn`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {x : M} {s : Set M}   {f' 
f₁' : TangentSpace I x →L[𝕜] TangentSpace I' (f x)},   UniqueMDiff[s] → x ∈ s → 
HasMFDerivAt[s] f x f' → HasMFDerivAt[s] f x f₁' → f' = f₁'
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{H : Type u_…
-/
protected theorem UniqueMDiffOn.eq (U : UniqueMDiff[s]) (hx : x ∈ s)
    (h : HasMFDerivAt[s] f x f') (h₁ : HasMFDerivAt[s] f x f₁') : f' = f₁' :=
  UniqueMDiffWithinAt.eq (U _ hx) h h₁

/-!
### General lemmas on derivatives of functions between manifolds

We mimic the API for functions between vector spaces
-/

@[simp, mfld_simps]
/-
**mfderivWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x

--- 原说明 ---
### General lemmas on derivatives of functions between manifolds

We mimic the API for functions between vector spaces
-/
theorem mfderivWithin_univ : mfderiv[univ] f = mfderiv% f := by
  ext x : 1
  simp only [mfderivWithin, mfderiv, mfld_simps]
  rw [mdifferentiableWithinAt_univ]

set_option backward.isDefEq.respectTransparency false in
/-
**mfderivWithin_zero_of_not_mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：mfderivWithin_zero_of_not_mdifferentiableWithinAt (h : ¬MDiffAt[s] f x) : 
mfderiv[s] f x = 0
参数：h : ¬MDiffAt[s] f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mfderivWithin_zero_of_not_mdifferentiableWithinAt (h : ¬MDiffAt[s] f x) :
    mfderiv[s] f x = 0 := by
  simp only [mfderivWithin, h, if_neg, not_false_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**mfderiv_zero_of_not_mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_zero_of_not_mdifferentiableAt (h : ¬MDiffAt f x) : mfderiv% f x = 
0
参数：h : ¬MDiffAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mfderiv_zero_of_not_mdifferentiableAt (h : ¬MDiffAt f x) :
    mfderiv% f x = 0 := by simp only [mfderiv, h, if_neg, not_false_iff]

@[nontriviality]
/-
**mdifferentiable_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiable_of_subsingleton [Subsingleton E] : MDiff f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `ModelWithCorners.injective`：injective : Injective I
· 使用定理 `ChartedSpace.discreteTopology`：ChartedSpace.discreteTopology [DiscreteTo
pology H] : DiscreteTopology M
· 使用定理 `Subsingleton.discreteTopology`：∀ {α : Type u} [t : TopologicalSpace α] [
Subsingleton α], DiscreteTopology α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `HasFDerivAt.differentiableAt`：HasFDerivAt.differentiableAt (h : HasFDeri
vAt f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `hasFDerivAt_of_subsingleton`：hasFDerivAt_of_subsingleton [h : Subsinglet
on E] (f : E -> F) (x : E) : HasFDerivAt f (0 : E ->L[𝕜] F) x
-/
theorem mdifferentiable_of_subsingleton [Subsingleton E] : MDiff f := by
  intro x
  have : Subsingleton H := I.injective.subsingleton
  have : DiscreteTopology M := discreteTopology H M
  simp only [mdifferentiableAt_iff, continuous_of_discreteTopology.continuousAt, true_and]
  exact (hasFDerivAt_of_subsingleton _ _).differentiableAt.differentiableWithinAt

@[nontriviality]
/-
**mdifferentiableWithinAt_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_of_subsingleton [Subsingleton E] : MDiffAt[s] f x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `mdifferentiable_of_subsingleton`：mdifferentiable_of_subsingleton [Subsin
gleton E] : MDiff f
-/
theorem mdifferentiableWithinAt_of_subsingleton [Subsingleton E] : MDiffAt[s] f x :=
  (mdifferentiable_of_subsingleton x).mdifferentiableWithinAt

/-- If `f : M → M'` has injective differential at `x` within `s`,
it is `MDifferentiable` at `x` within `s`. -/
/-
**mdifferentiableWithinAt_of_mfderivWithin_injective** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：mdifferentiableWithinAt_of_mfderivWithin_injective (hf : Injective (mfderi
v[s] f x)) : MDiffAt[s] f x
参数：hf : Injective (mfderiv[s] f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_zero_of_not_mdifferentiableWithinAt`：mfderivWithin_zero_of
_not_mdifferentiableWithinAt (h : ¬MDiffAt[s] f x) : mfderiv[s] f x = 0
· 使用定理 `Function.not_injective_const`：∀ {α : Type u_4} {β : Type u_5} [Nontrivia
l α] {b : β}, ¬Function.Injective fun x => b

--- 原说明 ---
If `f : M → M'` has injective differential at `x` within `s`,
it is `MDifferentiable` at `x` within `s`.
-/
lemma mdifferentiableWithinAt_of_mfderivWithin_injective (hf : Injective (mfderiv[s] f x)) :
    MDiffAt[s] f x := by
  nontriviality E
  have : Nontrivial (TangentSpace% x) := inferInstanceAs (Nontrivial E)
  contrapose hf
  rw [mfderivWithin_zero_of_not_mdifferentiableWithinAt hf]
  exact not_injective_const

/-- If `f : M → M'` has injective differential at `x`, it is `MDifferentiable` at `x`. -/
/-
**mdifferentiableAt_of_mfderiv_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_of_mfderiv_injective {f : M -> M'} (hf : Injective (mfde
riv% f x)) : MDiffAt f x
参数：hf : Injective (mfderiv% f x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableWithinAt_of_mfderivWithin_injective`：mdifferentiableWithi
nAt_of_mfderivWithin_injective (hf : Injective (mfderiv[s] f x)) : MDiffAt[s] f 
x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
If `f : M → M'` has injective differential at `x`, it is `MDifferentiable` at `x
`.
-/
lemma mdifferentiableAt_of_mfderiv_injective {f : M → M'} (hf : Injective (mfderiv% f x)) :
    MDiffAt f x := by
  simp only [← mdifferentiableWithinAt_univ, ← mfderivWithin_univ] at hf ⊢
  exact mdifferentiableWithinAt_of_mfderivWithin_injective hf
/-
**mdifferentiableWithinAt_of_isInvertible_mfderivWithin** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：mdifferentiableWithinAt_of_isInvertible_mfderivWithin (hf : (mfderiv[s] f 
x).IsInvertible) : MDiffAt[s] f x
参数：hf : (mfderiv[s] f x).IsInvertible。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableWithinAt_of_mfderivWithin_injective`：mdifferentiableWithi
nAt_of_mfderivWithin_injective (hf : Injective (mfderiv[s] f x)) : MDiffAt[s] f 
x
· 使用定理 `ContinuousLinearMap.IsInvertible.injective`：∀ {R : Type u_1} {M : Type u
_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace M₂]  
 [inst_2 : Semiring R] [inst_3 :…
-/
theorem mdifferentiableWithinAt_of_isInvertible_mfderivWithin (hf : (mfderiv[s] f x).IsInvertible) :
    MDiffAt[s] f x :=
  mdifferentiableWithinAt_of_mfderivWithin_injective hf.injective
/-
**mdifferentiableAt_of_isInvertible_mfderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableAt_of_isInvertible_mfderiv (hf : (mfderiv% f x).IsInvertibl
e) : MDiffAt f x
参数：hf : (mfderiv% f x).IsInvertible。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mdifferentiableAt_of_mfderiv_injective`：mdifferentiableAt_of_mfderiv_inj
ective {f : M -> M'} (hf : Injective (mfderiv% f x)) : MDiffAt f x
· 使用定理 `ContinuousLinearMap.IsInvertible.injective`：∀ {R : Type u_1} {M : Type u
_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace M₂]  
 [inst_2 : Semiring R] [inst_3 :…
-/
theorem mdifferentiableAt_of_isInvertible_mfderiv (hf : (mfderiv% f x).IsInvertible) :
    MDiffAt f x :=
  mdifferentiableAt_of_mfderiv_injective hf.injective
/-
**HasMFDerivWithinAt.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f x f') (hst : s subseteq t) 
: HasMFDerivAt[s] f x f'
参数：h : HasMFDerivAt[t] f x f'；hst : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.mono`：ContinuousWithinAt.mono (h : ContinuousWithinAt
 f t x) (hs : s subseteq t) : ContinuousWithinAt f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f x f') (hst : s ⊆ t) :
    HasMFDerivAt[s] f x f' :=
  ⟨ContinuousWithinAt.mono h.1 hst,
    HasFDerivWithinAt.mono h.2 (inter_subset_inter (preimage_mono hst) (Subset.refl _))⟩
/-
**HasMFDerivAt.hasMFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.hasMFDerivWithinAt (h : HasMFDerivAt% f x f') : HasMFDerivAt[
s] f x f'
参数：h : HasMFDerivAt% f x f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem HasMFDerivAt.hasMFDerivWithinAt (h : HasMFDerivAt% f x f') : HasMFDerivAt[s] f x f' :=
  ⟨ContinuousAt.continuousWithinAt h.1, HasFDerivWithinAt.mono h.2 inter_subset_right⟩
/-
**HasMFDerivWithinAt.mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.mdifferentiableWithinAt (h : HasMFDerivAt[s] f x f') : 
MDiffAt[s] f x
参数：h : HasMFDerivAt[s] f x f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivWithinAt.mdifferentiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x :=
  ⟨h.1, ⟨f', h.2⟩⟩
/-
**HasMFDerivAt.mdifferentiableAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.mdifferentiableAt (h : HasMFDerivAt% f x f') : MDiffAt f x
参数：h : HasMFDerivAt% f x f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mdifferentiableAt_iff`：mdifferentiableAt_iff (f : M -> M') (x : M) : MDi
fferentiableAt I I' f x ↔ ContinuousAt f x ∧ DifferentiableWithinAt 𝕜 (writtenIn
ExtChartAt …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivAt.mdifferentiableAt (h : HasMFDerivAt% f x f') : MDiffAt f x := by
  rw [mdifferentiableAt_iff]
  exact ⟨h.1, ⟨f', h.2⟩⟩

@[simp, mfld_simps]
/-
**hasMFDerivWithinAt_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f x f' ↔ HasMFDerivAt% f x f'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f x f' ↔ HasMFDerivAt% f x f' := by
  simp only [HasMFDerivWithinAt, HasMFDerivAt, continuousWithinAt_univ, mfld_simps]
/-
**hasMFDerivAt_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivAt_unique (h₀ : HasMFDerivAt% f x f₀') (h₁ : HasMFDerivAt% f x f
₁') : f₀' = f₁'
参数：h₀ : HasMFDerivAt% f x f₀'；h₁ : HasMFDerivAt% f x f₁'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffWithinAt.eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{H : Type u_…
· 使用定理 `uniqueMDiffWithinAt_univ`：uniqueMDiffWithinAt_univ : UniqueMDiffAt[(univ
 : Set M)] x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
-/
theorem hasMFDerivAt_unique (h₀ : HasMFDerivAt% f x f₀') (h₁ : HasMFDerivAt% f x f₁') :
    f₀' = f₁' := by
  rw [← hasMFDerivWithinAt_univ] at h₀ h₁
  exact (uniqueMDiffWithinAt_univ I).eq h₀ h₁

set_option backward.isDefEq.respectTransparency false in
/-
**hasMFDerivWithinAt_inter'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_inter' (h : t in 𝓝[s] x) : HasMFDerivAt[s inter t] f x 
f' ↔ HasMFDerivAt[s] f x f'
参数：h : t in 𝓝[s] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasMFDerivWithinAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `extChartAt_preimage_inter_eq`：extChartAt_preimage_inter_eq (x : M) : (ex
tChartAt I x).symm ⁻¹' (s inter t) inter range I = (extChartAt I x).symm ⁻¹' s i
nter range I inter…
· 使用定理 `hasFDerivWithinAt_inter'`：hasFDerivWithinAt_inter' (h : t in 𝓝[s] x) : H
asFDerivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `extChartAt_preimage_mem_nhdsWithin`：extChartAt_preimage_mem_nhdsWithin {
x : M} (ht : t in 𝓝[s] x) : (extChartAt I x).symm ⁻¹' t in 𝓝[(extChartAt I x).sy
mm ⁻¹' s inter range I] …
· 使用定理 `continuousWithinAt_inter'`：continuousWithinAt_inter' (h : t in 𝓝[s] x) :
 ContinuousWithinAt f (s inter t) x ↔ ContinuousWithinAt f s x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasMFDerivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasMFDerivAt[s ∩ t] f x f' ↔ HasMFDerivAt[s] f x f' := by
  rw [HasMFDerivWithinAt, HasMFDerivWithinAt, extChartAt_preimage_inter_eq,
    hasFDerivWithinAt_inter', continuousWithinAt_inter' h]
  exact extChartAt_preimage_mem_nhdsWithin h

set_option backward.isDefEq.respectTransparency false in
/-
**hasMFDerivWithinAt_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_inter (h : t in 𝓝 x) : HasMFDerivAt[s inter t] f x f' ↔
 HasMFDerivAt[s] f x f'
参数：h : t in 𝓝 x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasMFDerivWithinAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `extChartAt_preimage_inter_eq`：extChartAt_preimage_inter_eq (x : M) : (ex
tChartAt I x).symm ⁻¹' (s inter t) inter range I = (extChartAt I x).symm ⁻¹' s i
nter range I inter…
· 使用定理 `hasFDerivWithinAt_inter`：hasFDerivWithinAt_inter (h : t in 𝓝 x) : HasFDe
rivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `extChartAt_preimage_mem_nhds`：extChartAt_preimage_mem_nhds {x : M} (ht :
 t in 𝓝 x) : (extChartAt I x).symm ⁻¹' t in 𝓝 ((extChartAt I x) x)
· 使用定理 `continuousWithinAt_inter`：continuousWithinAt_inter (h : t in 𝓝 x) : Cont
inuousWithinAt f (s inter t) x ↔ ContinuousWithinAt f s x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasMFDerivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasMFDerivAt[s ∩ t] f x f' ↔ HasMFDerivAt[s] f x f' := by
  rw [HasMFDerivWithinAt, HasMFDerivWithinAt, extChartAt_preimage_inter_eq, hasFDerivWithinAt_inter,
    continuousWithinAt_inter h]
  exact extChartAt_preimage_mem_nhds h
/-
**HasMFDerivWithinAt.union** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.union (hs : HasMFDerivAt[s] f x f') (ht : HasMFDerivAt[
t] f x f') : HasMFDerivAt[s union t] f x f'
参数：hs : HasMFDerivAt[s] f x f'；ht : HasMFDerivAt[t] f x f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.union`：ContinuousWithinAt.union (hs : ContinuousWithi
nAt f s x) (ht : ContinuousWithinAt f t x) : ContinuousWithinAt f (s union t) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivWithinAt.union`：HasFDerivWithinAt.union (hs : HasFDerivWithinAt
 f f' s x) (ht : HasFDerivWithinAt f f' t x) : HasFDerivWithinAt f f' (s union t
) x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivWithinAt.union (hs : HasMFDerivAt[s] f x f') (ht : HasMFDerivAt[t] f x f') :
    HasMFDerivAt[s ∪ t] f x f' := by
  constructor
  · exact ContinuousWithinAt.union hs.1 ht.1
  · convert! HasFDerivWithinAt.union hs.2 ht.2 using 1
    simp only [union_inter_distrib_right, preimage_union]
/-
**HasMFDerivWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.mono_of_mem_nhdsWithin (h : HasMFDerivAt[s] f x f') (ht
 : s in 𝓝[t] x) : HasMFDerivAt[t] f x f'
参数：h : HasMFDerivAt[s] f x f'；ht : s in 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `hasMFDerivWithinAt_inter'`：hasMFDerivWithinAt_inter' (h : t in 𝓝[s] x) :
 HasMFDerivAt[s inter t] f x f' ↔ HasMFDerivAt[s] f x f'
· 使用定理 `HasMFDerivWithinAt.mono`：HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f 
x f') (hst : s subseteq t) : HasMFDerivAt[s] f x f'
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem HasMFDerivWithinAt.mono_of_mem_nhdsWithin (h : HasMFDerivAt[s] f x f') (ht : s ∈ 𝓝[t] x) :
    HasMFDerivAt[t] f x f' :=
  (hasMFDerivWithinAt_inter' ht).1 (h.mono inter_subset_right)
/-
**HasMFDerivWithinAt.hasMFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.hasMFDerivAt (h : HasMFDerivAt[s] f x f') (hs : s in 𝓝 
x) : HasMFDerivAt% f x f'
参数：h : HasMFDerivAt[s] f x f'；hs : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
· 使用定理 `hasMFDerivWithinAt_inter`：hasMFDerivWithinAt_inter (h : t in 𝓝 x) : HasM
FDerivAt[s inter t] f x f' ↔ HasMFDerivAt[s] f x f'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem HasMFDerivWithinAt.hasMFDerivAt (h : HasMFDerivAt[s] f x f') (hs : s ∈ 𝓝 x) :
    HasMFDerivAt% f x f' := by
  rwa [← univ_inter s, hasMFDerivWithinAt_inter hs, hasMFDerivWithinAt_univ] at h
/-
**MDifferentiableWithinAt.hasMFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.hasMFDerivWithinAt (h : MDiffAt[s] f x) : HasMFDer
ivAt[s] f x (mfderiv[s] f x)
参数：h : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
-/
theorem MDifferentiableWithinAt.hasMFDerivWithinAt (h : MDiffAt[s] f x) :
    HasMFDerivAt[s] f x (mfderiv[s] f x) := by
  refine ⟨h.1, ?_⟩
  simp only [mfderivWithin, h, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.2
/-
**mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt : MDiffAt[s] f x ↔ e
xists f', HasMFDerivWithinAt I I' f s x f'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
-/
theorem mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt :
    MDiffAt[s] f x ↔ ∃ f', HasMFDerivWithinAt I I' f s x f' := by
  refine ⟨fun h ↦ ⟨mfderiv[s] f x, h.hasMFDerivWithinAt⟩, ?_⟩
  rintro ⟨f', hf'⟩
  exact hf'.mdifferentiableWithinAt
/-
**MDifferentiableWithinAt.mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.mono_of_mem_nhdsWithin (h : MDiffAt[s] f x) {t : S
et M} (hst : s in 𝓝[t] x) : MDiffAt[t] f x
参数：h : MDiffAt[s] f x；hst : s in 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `HasMFDerivWithinAt.mono_of_mem_nhdsWithin`：HasMFDerivWithinAt.mono_of_me
m_nhdsWithin (h : HasMFDerivAt[s] f x f') (ht : s in 𝓝[t] x) : HasMFDerivAt[t] f
 x f'
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem MDifferentiableWithinAt.mono_of_mem_nhdsWithin (h : MDiffAt[s] f x) {t : Set M}
    (hst : s ∈ 𝓝[t] x) : MDiffAt[t] f x :=
  (h.hasMFDerivWithinAt.mono_of_mem_nhdsWithin hst).mdifferentiableWithinAt
/-
**MDifferentiableWithinAt.congr_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.congr_nhds (h : MDiffAt[s] f x) {t : Set M} (hst :
 𝓝[s] x = 𝓝[t] x) : MDiffAt[t] f x
参数：h : MDiffAt[s] f x；hst : 𝓝[s] x = 𝓝[t] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mono_of_mem_nhdsWithin`：MDifferentiableWithinAt.
mono_of_mem_nhdsWithin (h : MDiffAt[s] f x) {t : Set M} (hst : s in 𝓝[t] x) : MD
iffAt[t] f x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem MDifferentiableWithinAt.congr_nhds (h : MDiffAt[s] f x) {t : Set M}
    (hst : 𝓝[s] x = 𝓝[t] x) : MDiffAt[t] f x :=
  h.mono_of_mem_nhdsWithin <| hst ▸ self_mem_nhdsWithin
/-
**mdifferentiableWithinAt_congr_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_congr_nhds {t : Set M} (hst : 𝓝[s] x = 𝓝[t] x) : M
DiffAt[s] f x ↔ MDiffAt[t] f x
参数：hst : 𝓝[s] x = 𝓝[t] x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.congr_nhds`：MDifferentiableWithinAt.congr_nhds (
h : MDiffAt[s] f x) {t : Set M} (hst : 𝓝[s] x = 𝓝[t] x) : MDiffAt[t] f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mdifferentiableWithinAt_congr_nhds {t : Set M} (hst : 𝓝[s] x = 𝓝[t] x) :
    MDiffAt[s] f x ↔ MDiffAt[t] f x :=
  ⟨fun h => h.congr_nhds hst, fun h => h.congr_nhds hst.symm⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MDifferentiableWithinAt.mfderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiab
leWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {x : M} {s : Set M},   MDi
ffAt[s] f x →     mfderiv[s] f x =       fderivWithin 𝕜 (writtenInExtChartAt I I
' x f) (↑(extChartAt I x).symm ⁻¹' s ∩ Set.range ↑I) (↑(extChartAt I x) x)
参数：writtenInExtChartAt I I' x f；↑(extChartAt I x).symm ⁻¹' s ∩ Set.range ↑I；↑(ex
tChartAt I x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem MDifferentiableWithinAt.mfderivWithin (h : MDiffAt[s] f x) :
    mfderiv[s] f x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f :) ((extChartAt I x).symm ⁻¹' s ∩ range I)
        ((extChartAt I x) x) := by
  simp only [mfderivWithin, h, if_pos]
/-
**MDifferentiableAt.hasMFDerivAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.hasMFDerivAt (h : MDiffAt f x) : HasMFDerivAt% f x (mfde
riv% f x)
参数：h : MDiffAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.continuousAt`：MDifferentiableAt.continuousAt {f : M ->
 M'} {x : M} (hf : MDifferentiableAt I I' f x) : ContinuousAt f x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `MDifferentiableAt.differentiableWithinAt_writtenInExtChartAt`：MDifferent
iableAt.differentiableWithinAt_writtenInExtChartAt {f : M -> M'} {x : M} (hf : M
DifferentiableAt I I' f x) : DifferentiableWithinA…
-/
theorem MDifferentiableAt.hasMFDerivAt (h : MDiffAt f x) : HasMFDerivAt% f x (mfderiv% f x) := by
  refine ⟨h.continuousAt, ?_⟩
  simp only [mfderiv, h, mfld_simps]
  exact DifferentiableWithinAt.hasFDerivWithinAt h.differentiableWithinAt_writtenInExtChartAt

set_option backward.isDefEq.respectTransparency false in
/-
**MDifferentiableAt.mfderiv** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiableAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {x : M},   MDiffAt f x → m
fderiv% f x = fderivWithin 𝕜 (writtenInExtChartAt I I' x f) (Set.range ↑I) (↑(ex
tChartAt I x) x)
参数：writtenInExtChartAt I I' x f；Set.range ↑I；↑(extChartAt I x) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem MDifferentiableAt.mfderiv (h : MDiffAt f x) :
    mfderiv% f x =
      fderivWithin 𝕜 (writtenInExtChartAt I I' x f :) (range I) ((extChartAt I x) x) := by
  simp only [mfderiv, h, if_pos]
/-
**HasMFDerivAt.mfderiv** 是 Mathlib 中的一个定理，位于命名空间 `HasMFDerivAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {x : M}   {f' : TangentSpa
ce I x →L[𝕜] TangentSpace I' (f x)}, HasMFDerivAt% f x f' → mfderiv% f x = f'
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasMFDerivAt_unique`：hasMFDerivAt_unique (h₀ : HasMFDerivAt% f x f₀') (h
₁ : HasMFDerivAt% f x f₁') : f₀' = f₁'
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
-/
protected theorem HasMFDerivAt.mfderiv (h : HasMFDerivAt% f x f') : mfderiv% f x = f' :=
  (hasMFDerivAt_unique h h.mdifferentiableAt.hasMFDerivAt).symm
/-
**HasMFDerivWithinAt.mfderivWithin** 是 Mathlib 中的一个定理，位于命名空间 `HasMFDerivWithinAt
`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {x : M} {s : Set M}   {f' 
: TangentSpace I x →L[𝕜] TangentSpace I' (f x)}, HasMFDerivAt[s] f x f' → Unique
MDiffAt[s] x → mfderiv[s] f x = f'
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueMDiffWithinAt.eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] 
{H : Type u_…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
-/
protected theorem HasMFDerivWithinAt.mfderivWithin (h : HasMFDerivAt[s] f x f')
    (hxs : UniqueMDiffAt[s] x) : mfderiv[s] f x = f' := by
  ext
  rw [hxs.eq h h.mdifferentiableWithinAt.hasMFDerivWithinAt]

set_option backward.isDefEq.respectTransparency false in
/-
**HasMFDerivWithinAt.mfderivWithin_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.mfderivWithin_eq_zero (h : HasMFDerivWithinAt I I' f s 
x 0) : mfderiv[s] f x = 0
参数：h : HasMFDerivWithinAt I I' f s x 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `fderivWithin_def`：∀ (𝕜 : Type u_4) [inst : NontriviallyNormedField 𝕜] {E
 : Type u_5} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [inst_3 : 
Topolo…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasMFDerivWithinAt.mfderivWithin_eq_zero (h : HasMFDerivWithinAt I I' f s x 0) :
    mfderiv[s] f x = 0 := by
  simp only [mfld_simps, mfderivWithin, h.mdifferentiableWithinAt, ↓reduceIte]
  simp only [HasMFDerivWithinAt, mfld_simps] at h
  rw [fderivWithin, if_pos]
  exact h.2
/-
**MDifferentiable.mfderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.mfderivWithin (h : MDiffAt f x) (hxs : UniqueMDiffAt[s] x)
 : mfderiv[s] f x = mfderiv% f x
参数：h : MDiffAt f x；hxs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `HasMFDerivAt.hasMFDerivWithinAt`：HasMFDerivAt.hasMFDerivWithinAt (h : Ha
sMFDerivAt% f x f') : HasMFDerivAt[s] f x f'
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem MDifferentiable.mfderivWithin (h : MDiffAt f x) (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] f x = mfderiv% f x := by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact h.hasMFDerivAt.hasMFDerivWithinAt
/-
**mfderivWithin_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_subset (st : s subseteq t) (hs : UniqueMDiffAt[s] x) (h : MD
iffAt[t] f x) : mfderiv[s] f x = mfderiv[t] f x
参数：st : s subseteq t；hs : UniqueMDiffAt[s] x；h : MDiffAt[t] f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `HasMFDerivWithinAt.mono`：HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f 
x f') (hst : s subseteq t) : HasMFDerivAt[s] f x f'
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem mfderivWithin_subset (st : s ⊆ t) (hs : UniqueMDiffAt[s] x) (h : MDiffAt[t] f x) :
    mfderiv[s] f x = mfderiv[t] f x :=
  ((MDifferentiableWithinAt.hasMFDerivWithinAt h).mono st).mfderivWithin hs
/-
**mfderivWithin_inter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_inter (ht : t in 𝓝 x) : mfderiv[s inter t] f x = mfderiv[s] 
f x
参数：ht : t in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] 
{E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H :
 Type u_…
· 使用定理 `extChartAt_preimage_inter_eq`：extChartAt_preimage_inter_eq (x : M) : (ex
tChartAt I x).symm ⁻¹' (s inter t) inter range I = (extChartAt I x).symm ⁻¹' s i
nter range I inter…
· 使用定理 `mdifferentiableWithinAt_inter`：mdifferentiableWithinAt_inter (ht : t in 
𝓝 x) : MDiffAt[s inter t] f x ↔ MDiffAt[s] f x
· 使用定理 `fderivWithin_inter`：fderivWithin_inter (ht : t in 𝓝 x) : fderivWithin 𝕜 
f (s inter t) x = fderivWithin 𝕜 f s x
· 使用定理 `extChartAt_preimage_mem_nhds`：extChartAt_preimage_mem_nhds {x : M} (ht :
 t in 𝓝 x) : (extChartAt I x).symm ⁻¹' t in 𝓝 ((extChartAt I x) x)
-/
theorem mfderivWithin_inter (ht : t ∈ 𝓝 x) : mfderiv[s ∩ t] f x = mfderiv[s] f x := by
  rw [mfderivWithin, mfderivWithin, extChartAt_preimage_inter_eq, mdifferentiableWithinAt_inter ht,
    fderivWithin_inter (extChartAt_preimage_mem_nhds ht)]
/-
**mfderivWithin_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_of_mem_nhds (h : s in 𝓝 x) : mfderiv[s] f x = mfderiv% f x
参数：h : s in 𝓝 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `mfderivWithin_inter`：mfderivWithin_inter (ht : t in 𝓝 x) : mfderiv[s int
er t] f x = mfderiv[s] f x
-/
theorem mfderivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : mfderiv[s] f x = mfderiv% f x := by
  rw [← mfderivWithin_univ, ← univ_inter s, mfderivWithin_inter h]
/-
**mfderivWithin_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderivWithin_of_isOpen (hs : IsOpen s) (hx : x in s) : mfderiv[s] f x = m
fderiv% f x
参数：hs : IsOpen s；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderivWithin_of_mem_nhds`：mfderivWithin_of_mem_nhds (h : s in 𝓝 x) : mf
deriv[s] f x = mfderiv% f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
-/
lemma mfderivWithin_of_isOpen (hs : IsOpen s) (hx : x ∈ s) : mfderiv[s] f x = mfderiv% f x :=
  mfderivWithin_of_mem_nhds (hs.mem_nhds hx)

set_option backward.isDefEq.respectTransparency false in
/-
**hasMFDerivWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_insert {y : M} : HasMFDerivAt[insert y s] f x f' ↔ HasM
FDerivAt[s] f x f'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.t1Space`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {H : Type u_…
· 使用定理 `HasMFDerivWithinAt.mono`：HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f 
x f') (hst : s subseteq t) : HasMFDerivAt[s] f x f'
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasMFDerivWithinAt.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E]
 {H : Type u_…
· 使用定理 `ContinuousWithinAt.insert`：∀ {α : Type u_1} {β : Type u_2} [inst : Topol
ogicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α}   {x : α}, 
ContinuousWithi…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFDerivWithinAt_inter'`：hasFDerivWithinAt_inter' (h : t in 𝓝[s] x) : H
asFDerivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `HasFDerivWithinAt.mono`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField
 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [ins
t_3 : Topolo…
· 使用定理 `HasFDerivWithinAt.insert`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : AddCommGroup E]   [inst_2 : _root_.Module 𝕜 E] [i
nst_3 : Topolo…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PartialEquiv.eq_symm_apply`：eq_symm_apply {x : α} {y : β} (hx : x in e.s
ource) (hy : y in e.target) : x = e.symm y ↔ e x = y
· 使用定理 `HasMFDerivWithinAt.mono_of_mem_nhdsWithin`：HasMFDerivWithinAt.mono_of_me
m_nhdsWithin (h : HasMFDerivAt[s] f x f') (ht : s in 𝓝[t] x) : HasMFDerivAt[t] f
 x f'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nhdsWithin_insert_of_ne`：nhdsWithin_insert_of_ne [T1Space X] {x y : X} {
s : Set X} (hxy : x != y) : 𝓝[insert y s] x = 𝓝[s] x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem hasMFDerivWithinAt_insert {y : M} :
    HasMFDerivAt[insert y s] f x f' ↔ HasMFDerivAt[s] f x f' := by
  have : T1Space M := I.t1Space M
  refine ⟨fun h => h.mono <| subset_insert y s, fun hf ↦ ?_⟩
  rcases eq_or_ne x y with rfl | h
  · rw [HasMFDerivWithinAt] at hf ⊢
    refine ⟨hf.1.insert, ?_⟩
    have : (extChartAt I x).target ∈
        𝓝[(extChartAt I x).symm ⁻¹' insert x s ∩ range I] (extChartAt I x) x :=
      nhdsWithin_mono _ inter_subset_right (extChartAt_target_mem_nhdsWithin x)
    rw [← hasFDerivWithinAt_inter' this]
    apply hf.2.insert.mono
    rintro z ⟨⟨hz, h2z⟩, h'z⟩
    simp only [mem_inter_iff, mem_preimage, mem_insert_iff, mem_range] at hz h2z ⊢
    rcases hz with xz | h'z
    · left
      have : x ∈ (extChartAt I x).source := mem_extChartAt_source x
      exact (((extChartAt I x).eq_symm_apply this h'z).1 xz.symm).symm
    · exact Or.inr ⟨h'z, h2z⟩
  · apply hf.mono_of_mem_nhdsWithin ?_
    simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]

alias ⟨HasMFDerivWithinAt.of_insert, HasMFDerivWithinAt.insert'⟩ := hasMFDerivWithinAt_insert
/-
**HasMFDerivWithinAt.insert** 是 Mathlib 中的一个定理，位于命名空间 `HasMFDerivWithinAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {x : M} {s : Set M}   {f' 
: TangentSpace I x →L[𝕜] TangentSpace I' (f x)}, HasMFDerivAt[s] f x f' → HasMFD
erivAt[insert x s] f x f'
参数：f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.insert'`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
-/
protected theorem HasMFDerivWithinAt.insert (h : HasMFDerivAt[s] f x f') :
    HasMFDerivAt[insert x s] f x f' :=
  h.insert'
/-
**hasMFDerivWithinAt_sdiff_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_sdiff_singleton (y : M) : HasMFDerivAt[s \ {y}] f x f' 
↔ HasMFDerivAt[s] f x f'
参数：y : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasMFDerivWithinAt_insert`：hasMFDerivWithinAt_insert {y : M} : HasMFDeri
vAt[insert y s] f x f' ↔ HasMFDerivAt[s] f x f'
· 使用引理 `Set.insert_sdiff_singleton`：insert_sdiff_singleton : insert a (s \ {a}) 
= insert a s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hasMFDerivWithinAt_sdiff_singleton (y : M) :
    HasMFDerivAt[s \ {y}] f x f' ↔ HasMFDerivAt[s] f x f' := by
  rw [← hasMFDerivWithinAt_insert, insert_sdiff_singleton, hasMFDerivWithinAt_insert]

@[deprecated (since := "2026-06-03")]
alias hasMFDerivWithinAt_diff_singleton := hasMFDerivWithinAt_sdiff_singleton
/-
**mfderivWithin_eq_mfderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_eq_mfderiv (hs : UniqueMDiffAt[s] x) (h : MDiffAt f x) : mfd
eriv[s] f x = mfderiv% f x
参数：hs : UniqueMDiffAt[s] x；h : MDiffAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `mfderivWithin_subset`：mfderivWithin_subset (st : s subseteq t) (hs : Uni
queMDiffAt[s] x) (h : MDiffAt[t] f x) : mfderiv[s] f x = mfderiv[t] f x
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
-/
theorem mfderivWithin_eq_mfderiv (hs : UniqueMDiffAt[s] x) (h : MDiffAt f x) :
    mfderiv[s] f x = mfderiv% f x := by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_subset (subset_univ _) hs h.mdifferentiableWithinAt
/-
**mdifferentiableWithinAt_insert_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_insert_self : MDiffAt[insert x s] f x ↔ MDiffAt[s]
 f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mono`：MDifferentiableWithinAt.mono (hst : s subs
eteq t) (h : MDiffAt[t] f x) : MDiffAt[s] f x
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `HasMFDerivWithinAt.insert`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem mdifferentiableWithinAt_insert_self : MDiffAt[insert x s] f x ↔ MDiffAt[s] f x :=
  ⟨fun h ↦ h.mono (subset_insert x s), fun h ↦ h.hasMFDerivWithinAt.insert.mdifferentiableWithinAt⟩
/-
**mdifferentiableWithinAt_insert** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_insert {y : M} : MDiffAt[insert y s] f x ↔ MDiffAt
[s] f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `mdifferentiableWithinAt_insert_self`：mdifferentiableWithinAt_insert_self
 : MDiffAt[insert x s] f x ↔ MDiffAt[s] f x
· 使用定理 `ModelWithCorners.t1Space`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {H : Type u_…
· 使用定理 `mdifferentiableWithinAt_congr_nhds`：mdifferentiableWithinAt_congr_nhds {
t : Set M} (hst : 𝓝[s] x = 𝓝[t] x) : MDiffAt[s] f x ↔ MDiffAt[t] f x
· 使用定理 `nhdsWithin_insert_of_ne`：nhdsWithin_insert_of_ne [T1Space X] {x y : X} {
s : Set X} (hxy : x != y) : 𝓝[insert y s] x = 𝓝[s] x
-/
theorem mdifferentiableWithinAt_insert {y : M} : MDiffAt[insert y s] f x ↔ MDiffAt[s] f x := by
  rcases eq_or_ne x y with (rfl | h)
  · exact mdifferentiableWithinAt_insert_self
  have : T1Space M := I.t1Space M
  apply mdifferentiableWithinAt_congr_nhds
  exact nhdsWithin_insert_of_ne h

alias ⟨MDifferentiableWithinAt.of_insert, MDifferentiableWithinAt.insert'⟩ :=
mdifferentiableWithinAt_insert
/-
**MDifferentiableWithinAt.insert** 是 Mathlib 中的一个定理，位于命名空间 `MDifferentiableWithi
nAt`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_3} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_4}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] {E' : Type u_5} [inst_6 : NormedAddCo
mmGroup E']   [inst_7 : NormedSpace 𝕜 E'] {H' : Type u_6} [inst_8 : TopologicalS
pace H'] {I' : ModelWithCorners 𝕜 E' H'}   {M' : Type u_7} [inst_9 : Topological
Space M'] [inst_10 : ChartedSpace H' M'] {f : M → M'} {x : M} {s : Set M},   MDi
ffAt[s] f x → MDiffAt[insert x s] f x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.insert'`：∀ {𝕜 : Type u_1} [inst : NontriviallyNo
rmedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {H : Type u_…
-/
protected theorem MDifferentiableWithinAt.insert (h : MDiffAt[s] f x) : MDiffAt[insert x s] f x :=
  h.insert'

/-! ### Being differentiable on a union of open sets can be tested on each set -/

section mdifferentiableOn_union

/-- If a function is differentiable on two open sets, it is also differentiable on their union. -/
/-
**MDifferentiableOn.union_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.union_of_isOpen (hf : MDiff[s] f) (hf' : MDiff[t] f) (hs
 : IsOpen s) (ht : IsOpen t) : MDiff[s union t] f
参数：hf : MDiff[s] f；hf' : MDiff[t] f；hs : IsOpen s；ht : IsOpen t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `MDifferentiableWithinAt.mdifferentiableAt`：MDifferentiableWithinAt.mdiff
erentiableAt (h : MDiffAt[s] f x) (hs : s in 𝓝 x) : MDiffAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is differentiable on two open sets, it is also differentiable on t
heir union.
-/
lemma MDifferentiableOn.union_of_isOpen
    (hf : MDiff[s] f) (hf' : MDiff[t] f) (hs : IsOpen s) (ht : IsOpen t) : MDiff[s ∪ t] f := by
  intro x hx
  obtain (hx | hx) := hx
  · exact (hf x hx).mdifferentiableAt (hs.mem_nhds hx) |>.mdifferentiableWithinAt
  · exact (hf' x hx).mdifferentiableAt (ht.mem_nhds hx) |>.mdifferentiableWithinAt

/-- A function is differentiable on two open sets iff it is differentiable on their union. -/
/-
**mdifferentiableOn_union_iff_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) : MD
iff[s union t] f ↔ MDiff[s] f ∧ MDiff[t] f
参数：hs : IsOpen s；ht : IsOpen t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableOn.mono`：MDifferentiableOn.mono (h : MDiff[t] f) (st : s 
subseteq t) : MDiff[s] f
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用引理 `MDifferentiableOn.union_of_isOpen`：MDifferentiableOn.union_of_isOpen (hf
 : MDiff[s] f) (hf' : MDiff[t] f) (hs : IsOpen s) (ht : IsOpen t) : MDiff[s unio
n t] f

--- 原说明 ---
A function is differentiable on two open sets iff it is differentiable on their 
union.
-/
lemma mdifferentiableOn_union_iff_of_isOpen (hs : IsOpen s) (ht : IsOpen t) :
    MDiff[s ∪ t] f ↔ MDiff[s] f ∧ MDiff[t] f :=
  ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right⟩,
    fun ⟨hfs, hft⟩ ↦ MDifferentiableOn.union_of_isOpen hfs hft hs ht⟩
/-
**mdifferentiable_of_mdifferentiableOn_union_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：mdifferentiable_of_mdifferentiableOn_union_of_isOpen (hf : MDiff[s] f) (hf
' : MDiff[t] f) (hst : s union t = univ) (hs : IsOpen s) (ht : IsOpen t) : MDiff
 f
参数：hf : MDiff[s] f；hf' : MDiff[t] f；hst : s union t = univ；hs : IsOpen s；ht : Is
Open t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableOn_univ`：mdifferentiableOn_univ : MDiff[univ] f ↔ MDiff f
· 使用引理 `MDifferentiableOn.union_of_isOpen`：MDifferentiableOn.union_of_isOpen (hf
 : MDiff[s] f) (hf' : MDiff[t] f) (hs : IsOpen s) (ht : IsOpen t) : MDiff[s unio
n t] f
-/
lemma mdifferentiable_of_mdifferentiableOn_union_of_isOpen (hf : MDiff[s] f) (hf' : MDiff[t] f)
    (hst : s ∪ t = univ) (hs : IsOpen s) (ht : IsOpen t) : MDiff f := by
  rw [← mdifferentiableOn_univ, ← hst]
  exact hf.union_of_isOpen hf' hs ht

/-- If a function is differentiable on open sets `s i`, it is differentiable on their union. -/
/-
**MDifferentiableOn.iUnion_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.iUnion_of_isOpen {ι : Type*} {s : ι -> Set M} (hf : fora
ll i : ι, MDiff[s i] f) (hs : forall i, IsOpen (s i)) : MDiff[⋃ i, s i] f
参数：hf : forall i : ι, MDiff[s i] f；hs : forall i, IsOpen (s i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `MDifferentiableOn.mdifferentiableAt`：MDifferentiableOn.mdifferentiableAt
 (h : MDiff[s] f) (hx : s in 𝓝 x) : MDiffAt f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x

--- 原说明 ---
If a function is differentiable on open sets `s i`, it is differentiable on thei
r union.
-/
lemma MDifferentiableOn.iUnion_of_isOpen
    {ι : Type*} {s : ι → Set M} (hf : ∀ i : ι, MDiff[s i] f) (hs : ∀ i, IsOpen (s i)) :
    MDiff[⋃ i, s i] f := by
  rintro x ⟨si, ⟨i, rfl⟩, hxsi⟩
  exact (hf i).mdifferentiableAt ((hs i).mem_nhds hxsi) |>.mdifferentiableWithinAt

/-- A function is differentiable on a union of open sets `s i`
iff it is differentiable on each `s i`. -/
/-
**mdifferentiableOn_iUnion_iff_of_isOpen** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι -> Set M} (hs : 
forall i, IsOpen (s i)) : MDiff[⋃ i, s i] f ↔ forall i : ι, MDiff[s i] f
参数：hs : forall i, IsOpen (s i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableOn.mono`：MDifferentiableOn.mono (h : MDiff[t] f) (st : s 
subseteq t) : MDiff[s] f
· 使用定理 `Set.subset_iUnion_of_subset`：subset_iUnion_of_subset {s : Set α} {t : ι 
-> Set α} (i : ι) (h : s subseteq t i) : s subseteq ⋃ i, t i
· 使用引理 `MDifferentiableOn.iUnion_of_isOpen`：MDifferentiableOn.iUnion_of_isOpen {
ι : Type*} {s : ι -> Set M} (hf : forall i : ι, MDiff[s i] f) (hs : forall i, Is
Open (s i)) : MDiff[⋃ i,…

--- 原说明 ---
A function is differentiable on a union of open sets `s i`
iff it is differentiable on each `s i`.
-/
lemma mdifferentiableOn_iUnion_iff_of_isOpen {ι : Type*} {s : ι → Set M} (hs : ∀ i, IsOpen (s i)) :
    MDiff[⋃ i, s i] f ↔ ∀ i : ι, MDiff[s i] f :=
  ⟨fun h i ↦ h.mono <| subset_iUnion_of_subset i fun _ a ↦ a,
   fun h ↦ MDifferentiableOn.iUnion_of_isOpen h hs⟩
/-
**mdifferentiable_of_mdifferentiableOn_iUnion_of_isOpen** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：mdifferentiable_of_mdifferentiableOn_iUnion_of_isOpen {ι : Type*} {s : ι -
> Set M} (hf : forall i : ι, MDiff[s i] f) (hs : forall i, IsOpen (s i)) (hs' : 
⋃ i, s i = univ) : MDiff f
参数：hf : forall i : ι, MDiff[s i] f；hs : forall i, IsOpen (s i)；hs' : ⋃ i, s i = 
univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableOn_univ`：mdifferentiableOn_univ : MDiff[univ] f ↔ MDiff f
· 使用引理 `MDifferentiableOn.iUnion_of_isOpen`：MDifferentiableOn.iUnion_of_isOpen {
ι : Type*} {s : ι -> Set M} (hf : forall i : ι, MDiff[s i] f) (hs : forall i, Is
Open (s i)) : MDiff[⋃ i,…
-/
lemma mdifferentiable_of_mdifferentiableOn_iUnion_of_isOpen {ι : Type*} {s : ι → Set M}
    (hf : ∀ i : ι, MDiff[s i] f) (hs : ∀ i, IsOpen (s i)) (hs' : ⋃ i, s i = univ) : MDiff f := by
  rw [← mdifferentiableOn_univ, ← hs']
  exact MDifferentiableOn.iUnion_of_isOpen hf hs

end mdifferentiableOn_union

/-! ### Deriving continuity from differentiability on manifolds -/

/-
**HasMFDerivWithinAt.continuousWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.continuousWithinAt (h : HasMFDerivAt[s] f x f') : Conti
nuousWithinAt f s x
参数：h : HasMFDerivAt[s] f x f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
### Deriving continuity from differentiability on manifolds
-/
theorem HasMFDerivWithinAt.continuousWithinAt (h : HasMFDerivAt[s] f x f') :
    ContinuousWithinAt f s x :=
  h.1
/-
**HasMFDerivAt.continuousAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.continuousAt (h : HasMFDerivAt% f x f') : ContinuousAt f x
参数：h : HasMFDerivAt% f x f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem HasMFDerivAt.continuousAt (h : HasMFDerivAt% f x f') : ContinuousAt f x :=
  h.1
/-
**tangentMapWithin_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMapWithin_subset {p : TangentBundle I M} (st : s subseteq t) (hs : 
UniqueMDiffAt[s] p.1) (h : MDiffAt[t] f p.1) : tangentMap[s] f p = tangentMap[t]
 f p
参数：st : s subseteq t；hs : UniqueMDiffAt[s] p.1；h : MDiffAt[t] f p.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_subset`：mfderivWithin_subset (st : s subseteq t) (hs : Uni
queMDiffAt[s] x) (h : MDiffAt[t] f x) : mfderiv[s] f x = mfderiv[t] f x
-/
theorem tangentMapWithin_subset
    {p : TangentBundle I M} (st : s ⊆ t) (hs : UniqueMDiffAt[s] p.1) (h : MDiffAt[t] f p.1) :
    tangentMap[s] f p = tangentMap[t] f p := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_subset st hs h]
/-
**tangentMapWithin_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMapWithin_univ : tangentMap[(univ : Set M)] f = tangentMap% f
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
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tangentMapWithin_univ : tangentMap[(univ : Set M)] f = tangentMap% f := by
  ext p : 1
  simp only [tangentMapWithin, tangentMap, mfld_simps]
/-
**tangentMapWithin_eq_tangentMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMapWithin_eq_tangentMap {p : TangentBundle I M} (hs : UniqueMDiffAt
[s] p.1) (h : MDiffAt f p.1) : tangentMap[s] f p = tangentMap% f p
参数：hs : UniqueMDiffAt[s] p.1；h : MDiffAt f p.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tangentMapWithin_univ`：tangentMapWithin_univ : tangentMap[(univ : Set M)
] f = tangentMap% f
· 使用定理 `tangentMapWithin_subset`：tangentMapWithin_subset {p : TangentBundle I M}
 (st : s subseteq t) (hs : UniqueMDiffAt[s] p.1) (h : MDiffAt[t] f p.1) : tangen
tMap[s] f p =…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
-/
theorem tangentMapWithin_eq_tangentMap {p : TangentBundle I M} (hs : UniqueMDiffAt[s] p.1)
    (h : MDiffAt f p.1) : tangentMap[s] f p = tangentMap% f p := by
  rw [← mdifferentiableWithinAt_univ] at h
  rw [← tangentMapWithin_univ]
  exact tangentMapWithin_subset (subset_univ _) hs h

@[simp, mfld_simps]
/-
**tangentMapWithin_proj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMapWithin_proj {p : TangentBundle I M} : (tangentMap[s] f p).proj =
 f p.proj
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tangentMapWithin_proj {p : TangentBundle I M} : (tangentMap[s] f p).proj = f p.proj := rfl

@[simp, mfld_simps]
/-
**tangentMapWithin_snd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tangentMapWithin_snd {X : TangentSpace% x} : (tangentMap[s] f X).2 = (mfde
riv[s] f x) X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tangentMapWithin_snd {X : TangentSpace% x} : (tangentMap[s] f X).2 = (mfderiv[s] f x) X := rfl

@[simp, mfld_simps]
/-
**tangentMap_proj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMap_proj {p : TangentBundle I M} : (tangentMap% f p).proj = f p.pro
j
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tangentMap_proj {p : TangentBundle I M} : (tangentMap% f p).proj = f p.proj := rfl

@[simp, mfld_simps]
/-
**tangentMap_snd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tangentMap_snd {X : TangentSpace% x} : (tangentMap% f X).2 = (mfderiv% f x
) X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tangentMap_snd {X : TangentSpace% x} : (tangentMap% f X).2 = (mfderiv% f x) X := rfl

/-- If two sets coincide locally around `x`, except maybe at a point `y`, then their
preimage under `extChartAt x` coincide locally, except maybe at `extChartAt I x x`. -/
/-
**preimage_extChartAt_eventuallyEq_compl_singleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_extChartAt_eventuallyEq_compl_singleton (y : M) (h : s =ᶠ[𝓝[{y}ᶜ]
 x] t) : ((extChartAt I x).symm ⁻¹' s inter range I : Set E) =ᶠ[𝓝[{extChartAt I 
x x}ᶜ] (extChartAt I x x)] ((extChartAt I x).symm ⁻¹' t inter range I : Set E)
参数：y : M；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.t1Space`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {H : Type u_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nhdsWithin_iff_exists_mem_nhds_inter`：mem_nhdsWithin_iff_exists_mem_
nhds_inter {t : Set α} {a : α} {s : Set α} : t in 𝓝[s] a ↔ exists u in 𝓝 a, u in
ter s subseteq t
· 使用引理 `nhdsWithin_compl_singleton_le`：nhdsWithin_compl_singleton_le [T1Space X]
 (x y : X) : 𝓝[{x}ᶜ] x <= 𝓝[{y}ᶜ] x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `nhdsWithin_union`：nhdsWithin_union (a : α) (s t : Set α) : 𝓝[s union t] 
a = 𝓝[s] a ⊔ 𝓝[t] a
· 使用定理 `Filter.union_mem_sup`：union_mem_sup {f g : Filter α} {s t : Set α} (hs :
 s in f) (ht : t in g) : s union t in f ⊔ g
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `continuousAt_extChartAt_symm`：continuousAt_extChartAt_symm (x : M) : Con
tinuousAt (extChartAt I x).symm ((extChartAt I x) x)
· 使用定理 `extChartAt_to_inv`：extChartAt_to_inv (x : M) : (extChartAt I x).symm ((e
xtChartAt I x) x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `PartialEquiv.eq_symm_apply`：eq_symm_apply {x : α} {y : β} (hx : x in e.s
ource) (hy : y in e.target) : x = e.symm y ↔ e x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If two sets coincide locally around `x`, except maybe at a point `y`, then their
preimage under `extChartAt x` coincide locally, except maybe at `extChartAt I x 
x`.
-/
theorem preimage_extChartAt_eventuallyEq_compl_singleton (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E) =ᶠ[𝓝[{extChartAt I x x}ᶜ] (extChartAt I x x)]
    ((extChartAt I x).symm ⁻¹' t ∩ range I : Set E) := by
  have : T1Space M := I.t1Space M
  obtain ⟨u, u_mem, hu⟩ : ∃ u ∈ 𝓝 x, u ∩ {x}ᶜ ⊆ {y | (y ∈ s) = (y ∈ t)} :=
    mem_nhdsWithin_iff_exists_mem_nhds_inter.1 (nhdsWithin_compl_singleton_le x y h)
  rw [← extChartAt_to_inv (I := I) x] at u_mem
  have B : (extChartAt I x).target ∪ (range I)ᶜ ∈ 𝓝 (extChartAt I x x) := by
    rw [← nhdsWithin_univ, ← union_compl_self (range I), nhdsWithin_union]
    apply Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin x) self_mem_nhdsWithin
  apply mem_nhdsWithin_iff_exists_mem_nhds_inter.2
    ⟨_, Filter.inter_mem ((continuousAt_extChartAt_symm x).preimage_mem_nhds u_mem) B, ?_⟩
  rintro z ⟨hz, h'z⟩
  simp only [eq_iff_iff, mem_ofPred_eq]
  change z ∈ (extChartAt I x).symm ⁻¹' s ∩ range I ↔ z ∈ (extChartAt I x).symm ⁻¹' t ∩ range I
  by_cases hIz : z ∈ range I
  · simp only [mem_inter_iff, mem_preimage, mem_union, mem_compl_iff, hIz, not_true_eq_false,
      or_false, and_true] at hz ⊢
    rw [← eq_iff_iff]
    apply hu ⟨hz.1, ?_⟩
    push _ ∈ _ at h'z ⊢
    rw [eq_comm, (extChartAt I x).eq_symm_apply (by simp) hz.2]
    exact Ne.symm h'z
  · simp [hIz]

/-! ### Congruence lemmas for derivatives on manifolds -/

/-- If two sets coincide locally, except maybe at a point, then it is equivalent to have a manifold
derivative within one or the other. -/
/-
**hasMFDerivWithinAt_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : HasMFDeriv
At[s] f x f' ↔ HasMFDerivAt[t] f x f'
参数：y : M；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModelWithCorners.t1Space`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {H : Type u_…
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `continuousWithinAt_congr_set'`：continuousWithinAt_congr_set' [Topologica
lSpace Y] [T1Space X] {x : X} {s t : Set X} {f : X -> Y} (y : X) (h : s =ᶠ[𝓝[{y}
ᶜ] x] t) : Continuo…
· 使用定理 `hasFDerivWithinAt_congr_set'`：hasFDerivWithinAt_congr_set' [T1Space E] (
y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : HasFDerivWithinAt f f' s x ↔ HasFDerivWithinAt 
f f' t x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `preimage_extChartAt_eventuallyEq_compl_singleton`：preimage_extChartAt_ev
entuallyEq_compl_singleton (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : ((extChartAt I x).s
ymm ⁻¹' s inter range I : Set E) =ᶠ[𝓝[…

--- 原说明 ---
If two sets coincide locally, except maybe at a point, then it is equivalent to 
have a manifold
derivative within one or the other.
-/
theorem hasMFDerivWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    HasMFDerivAt[s] f x f' ↔ HasMFDerivAt[t] f x f' := by
  have : T1Space M := I.t1Space M
  simp only [HasMFDerivWithinAt]
  refine and_congr ?_ ?_
  · exact continuousWithinAt_congr_set' _ h
  · apply hasFDerivWithinAt_congr_set' (extChartAt I x x)
    exact preimage_extChartAt_eventuallyEq_compl_singleton y h
/-
**hasMFDerivWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasMFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) : HasMFDerivAt[s] f x f' ↔ 
HasMFDerivAt[t] f x f'
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasMFDerivWithinAt_congr_set'`：hasMFDerivWithinAt_congr_set' (y : M) (h 
: s =ᶠ[𝓝[{y}ᶜ] x] t) : HasMFDerivAt[s] f x f' ↔ HasMFDerivAt[t] f x f'
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem hasMFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) :
    HasMFDerivAt[s] f x f' ↔ HasMFDerivAt[t] f x f' :=
  hasMFDerivWithinAt_congr_set' x <| h.filter_mono inf_le_left

/-- If two sets coincide around a point (except possibly at a single point `y`), then it is
equivalent to be differentiable within one or the other set. -/
/-
**mdifferentiableWithinAt_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : MDiff
At[s] f x ↔ MDiffAt[t] f x
参数：y : M；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasMFDerivWithinAt_congr_set'`：hasMFDerivWithinAt_congr_set' (y : M) (h 
: s =ᶠ[𝓝[{y}ᶜ] x] t) : HasMFDerivAt[s] f x f' ↔ HasMFDerivAt[t] f x f'

--- 原说明 ---
If two sets coincide around a point (except possibly at a single point `y`), the
n it is
equivalent to be differentiable within one or the other set.
-/
theorem mdifferentiableWithinAt_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    MDiffAt[s] f x ↔ MDiffAt[t] f x := by
  simp only [mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt]
  exact exists_congr fun _ => hasMFDerivWithinAt_congr_set' _ h
/-
**mdifferentiableWithinAt_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) : MDiffAt[s] f x ↔ MDi
ffAt[t] f x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `hasMFDerivWithinAt_congr_set`：hasMFDerivWithinAt_congr_set (h : s =ᶠ[𝓝 x
] t) : HasMFDerivAt[s] f x f' ↔ HasMFDerivAt[t] f x f'
-/
theorem mdifferentiableWithinAt_congr_set (h : s =ᶠ[𝓝 x] t) : MDiffAt[s] f x ↔ MDiffAt[t] f x := by
  simp only [mdifferentiableWithinAt_iff_exists_hasMFDerivWithinAt]
  exact exists_congr fun _ => hasMFDerivWithinAt_congr_set h

/-- If two sets coincide locally, except maybe at a point, then derivatives within these sets
are the same. -/
/-
**mfderivWithin_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : mfderiv[s] f x 
= mfderiv[t] f x
参数：y : M；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mdifferentiableWithinAt_congr_set'`：mdifferentiableWithinAt_congr_set' (
y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : MDiffAt[s] f x ↔ MDiffAt[t] f x
· 使用定理 `fderivWithin_congr_set'`：fderivWithin_congr_set' [T1Space E] (y : E) (h 
: s =ᶠ[𝓝[{y}ᶜ] x] t) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `preimage_extChartAt_eventuallyEq_compl_singleton`：preimage_extChartAt_ev
entuallyEq_compl_singleton (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : ((extChartAt I x).s
ymm ⁻¹' s inter range I : Set E) =ᶠ[𝓝[…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If two sets coincide locally, except maybe at a point, then derivatives within t
hese sets
are the same.
-/
theorem mfderivWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    mfderiv[s] f x = mfderiv[t] f x := by
  by_cases hx : MDiffAt[s] f x
  · simp only [mfderivWithin, hx, (mdifferentiableWithinAt_congr_set' y h).1 hx, ↓reduceIte]
    apply fderivWithin_congr_set' (extChartAt I x x)
    exact preimage_extChartAt_eventuallyEq_compl_singleton y h
  · simp [mfderivWithin, hx, ← mdifferentiableWithinAt_congr_set' y h]

/-- If two sets coincide locally, then derivatives within these sets
are the same. -/
/-
**mfderivWithin_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : mfderiv[s] f x = mfderiv[t] f 
x
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderivWithin_congr_set'`：mfderivWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{
y}ᶜ] x] t) : mfderiv[s] f x = mfderiv[t] f x
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
If two sets coincide locally, then derivatives within these sets
are the same.
-/
theorem mfderivWithin_congr_set (h : s =ᶠ[𝓝 x] t) : mfderiv[s] f x = mfderiv[t] f x :=
  mfderivWithin_congr_set' x <| h.filter_mono inf_le_left

/-- If two sets coincide locally, except maybe at a point, then derivatives within these sets
coincide locally. -/
/-
**mfderivWithin_eventually_congr_set'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_eventually_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : fora
llᶠ y in 𝓝 x, mfderiv[s] f y = mfderiv[t] f y
参数：y : M；h : s =ᶠ[𝓝[{y}ᶜ] x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhds_nhdsWithin`：eventually_nhds_nhdsWithin {a : α} {s : Set 
α} {p : α -> Prop} : (forallᶠ y in 𝓝 a, forallᶠ x in 𝓝[s] y, p x) ↔ forallᶠ x in
 𝓝[s] a, p x
· 使用定理 `mfderivWithin_congr_set'`：mfderivWithin_congr_set' (y : M) (h : s =ᶠ[𝓝[{
y}ᶜ] x] t) : mfderiv[s] f x = mfderiv[t] f x

--- 原说明 ---
If two sets coincide locally, except maybe at a point, then derivatives within t
hese sets
coincide locally.
-/
theorem mfderivWithin_eventually_congr_set' (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    ∀ᶠ y in 𝓝 x, mfderiv[s] f y = mfderiv[t] f y :=
  (eventually_nhds_nhdsWithin.2 h).mono fun _ => mfderivWithin_congr_set' y

/-- If two sets coincide locally, then derivatives within these sets coincide locally. -/
/-
**mfderivWithin_eventually_congr_set** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) : forallᶠ y in 𝓝 x, m
fderiv[s] f y = mfderiv[t] f y
参数：h : s =ᶠ[𝓝 x] t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderivWithin_eventually_congr_set'`：mfderivWithin_eventually_congr_set'
 (y : M) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) : forallᶠ y in 𝓝 x, mfderiv[s] f y = mfderiv[t]
 f y
· 使用定理 `Filter.EventuallyEq.filter_mono`：∀ {α : Type u} {β : Type v} {l l' : Fil
ter α} {f g : α → β}, f =ᶠ[l] g → l' ≤ l → f =ᶠ[l'] g
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a

--- 原说明 ---
If two sets coincide locally, then derivatives within these sets coincide locall
y.
-/
theorem mfderivWithin_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
    ∀ᶠ y in 𝓝 x, mfderiv[s] f y = mfderiv[t] f y :=
  mfderivWithin_eventually_congr_set' x <| h.filter_mono inf_le_left
/-
**HasMFDerivAt.congr_mfderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.congr_mfderiv (h : HasMFDerivAt% f x f') (h' : f' = f₁') : Ha
sMFDerivAt% f x f₁'
参数：h : HasMFDerivAt% f x f'；h' : f' = f₁'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasMFDerivAt.congr_mfderiv (h : HasMFDerivAt% f x f') (h' : f' = f₁') :
    HasMFDerivAt% f x f₁' :=
  h' ▸ h
/-
**HasMFDerivWithinAt.congr_mfderiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.congr_mfderiv (h : HasMFDerivAt[s] f x f') (h' : f' = f
₁') : HasMFDerivAt[s] f x f₁'
参数：h : HasMFDerivAt[s] f x f'；h' : f' = f₁'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem HasMFDerivWithinAt.congr_mfderiv (h : HasMFDerivAt[s] f x f') (h' : f' = f₁') :
    HasMFDerivAt[s] f x f₁' :=
  h' ▸ h
/-
**HasMFDerivWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.congr_of_eventuallyEq (h : HasMFDerivAt[s] f x f') (h₁ 
: f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasMFDerivAt[s] f₁ x f'
参数：h : HasMFDerivAt[s] f x f'；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.congr_of_eventuallyEq`：ContinuousWithinAt.congr_of_ev
entuallyEq (h : ContinuousWithinAt f s x) (h₁ : g =ᶠ[𝓝[s] x] f) (hx : g x = f x)
 : ContinuousWithinAt g s x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HasFDerivWithinAt.congr_of_eventuallyEq`：HasFDerivWithinAt.congr_of_even
tuallyEq (h : HasFDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : HasFDerivWithinAt f₁ f' …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `extChartAt_preimage_mem_nhdsWithin`：extChartAt_preimage_mem_nhdsWithin {
x : M} (ht : t in 𝓝[s] x) : (extChartAt I x).symm ⁻¹' t in 𝓝[(extChartAt I x).sy
mm ⁻¹' s inter range I] …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
-/
theorem HasMFDerivWithinAt.congr_of_eventuallyEq
    (h : HasMFDerivAt[s] f x f') (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    HasMFDerivAt[s] f₁ x f' := by
  refine ⟨ContinuousWithinAt.congr_of_eventuallyEq h.1 h₁ hx, ?_⟩
  apply HasFDerivWithinAt.congr_of_eventuallyEq h.2
  · have :
      (extChartAt I x).symm ⁻¹' {y | f₁ y = f y} ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin h₁
    apply Filter.mem_of_superset this fun y => _
    simp +contextual only [hx, mfld_simps]
  · simp only [hx, mfld_simps]
/-
**HasMFDerivWithinAt.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.congr_mono (h : HasMFDerivAt[s] f x f') (ht : forall x 
in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t subseteq s) : HasMFDerivAt[t] f₁ x f
'
参数：h : HasMFDerivAt[s] f x f'；ht : forall x in t, f₁ x = f x；hx : f₁ x = f x；h₁ 
: t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.congr_of_eventuallyEq`：HasMFDerivWithinAt.congr_of_ev
entuallyEq (h : HasMFDerivAt[s] f x f') (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : HasMFDerivAt[s] f₁ x f'
· 使用定理 `HasMFDerivWithinAt.mono`：HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f 
x f') (hst : s subseteq t) : HasMFDerivAt[s] f x f'
· 使用定理 `Filter.mem_inf_of_right`：mem_inf_of_right {f g : Filter α} {s : Set α} (
h : s in g) : s in f ⊓ g
-/
theorem HasMFDerivWithinAt.congr_mono
    (h : HasMFDerivAt[s] f x f') (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) :
    HasMFDerivAt[t] f₁ x f' :=
  (h.mono h₁).congr_of_eventuallyEq (Filter.mem_inf_of_right ht) hx

set_option backward.isDefEq.respectTransparency false in
/-
**HasMFDerivAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.congr_of_eventuallyEq (h : HasMFDerivAt% f x f') (h₁ : f₁ =ᶠ[
𝓝 x] f) : HasMFDerivAt% f₁ x f'
参数：h : HasMFDerivAt% f x f'；h₁ : f₁ =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
· 使用定理 `HasMFDerivWithinAt.congr_of_eventuallyEq`：HasMFDerivWithinAt.congr_of_ev
entuallyEq (h : HasMFDerivAt[s] f x f') (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : HasMFDerivAt[s] f₁ x f'
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
-/
theorem HasMFDerivAt.congr_of_eventuallyEq (h : HasMFDerivAt% f x f') (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasMFDerivAt% f₁ x f' := by
  rw [← hasMFDerivWithinAt_univ] at h ⊢
  apply h.congr_of_eventuallyEq _ (mem_of_mem_nhds h₁ :)
  rwa [nhdsWithin_univ]
/-
**mdifferentiableWithinAt_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_congr (h₁ : forall y in s, f₁ y = f y) (hx : f₁ x 
= f x) : MDiffAt[s] f₁ x ↔ MDiffAt[s] f x
参数：h₁ : forall y in s, f₁ y = f y；hx : f₁ x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff`：liftPro
pWithinAt_congr_iff (h₁ : forall y in s, g' y = g y) (hx : g' x = g x) : LiftPro
pWithinAt P g' s x ↔ LiftPropWithinAt P g s x
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
-/
theorem mdifferentiableWithinAt_congr (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
    MDiffAt[s] f₁ x ↔ MDiffAt[s] f x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff h₁ hx
/-
**MDifferentiableWithinAt.congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.congr_of_mem (h : MDiffAt[s] f x) (h₁ : forall y i
n s, f₁ y = f y) (hx : x in s) : MDiffAt[s] f₁ x
参数：h : MDiffAt[s] f x；h₁ : forall y in s, f₁ y = f y；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_of_mem`：lift
PropWithinAt_congr_of_mem (h : LiftPropWithinAt P g s x) (h₁ : forall y in s, g'
 y = g y) (hx : x in s) : LiftPropWithinAt P g' s x
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
-/
theorem MDifferentiableWithinAt.congr_of_mem (h : MDiffAt[s] f x) (h₁ : ∀ y ∈ s, f₁ y = f y)
    (hx : x ∈ s) : MDiffAt[s] f₁ x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_of_mem h h₁ hx
/-
**mdifferentiableWithinAt_congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableWithinAt_congr_of_mem (h₁ : forall y in s, f₁ y = f y) (hx 
: x in s) : MDiffAt[s] f₁ x ↔ MDiffAt[s] f x
参数：h₁ : forall y in s, f₁ y = f y；hx : x in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff_of_mem`：
liftPropWithinAt_congr_iff_of_mem (h₁ : forall y in s, g' y = g y) (hx : x in s)
 : LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
-/
theorem mdifferentiableWithinAt_congr_of_mem (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
    MDiffAt[s] f₁ x ↔ MDiffAt[s] f x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_mem h₁ hx
/-
**Filter.EventuallyEq.mdifferentiablefWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.mdifferentiablefWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (h
x : f₁ x = f x) : MDiffAt[s] f₁ x ↔ MDiffAt[s] f x
参数：h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropWithinAt_congr_iff_of_event
uallyEq`：liftPropWithinAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx :
 g' x = g x) : LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
-/
theorem Filter.EventuallyEq.mdifferentiablefWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    MDiffAt[s] f₁ x ↔ MDiffAt[s] f x :=
  differentiableWithinAt_localInvariantProp.liftPropWithinAt_congr_iff_of_eventuallyEq h₁ hx
/-
**MDifferentiableWithinAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.congr_of_eventuallyEq (h : MDiffAt[s] f x) (h₁ : f
₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : MDiffAt[s] f₁ x
参数：h : MDiffAt[s] f x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `HasMFDerivWithinAt.congr_of_eventuallyEq`：HasMFDerivWithinAt.congr_of_ev
entuallyEq (h : HasMFDerivAt[s] f x f') (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x)
 : HasMFDerivAt[s] f₁ x f'
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem MDifferentiableWithinAt.congr_of_eventuallyEq (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : MDiffAt[s] f₁ x :=
  (h.hasMFDerivWithinAt.congr_of_eventuallyEq h₁ hx).mdifferentiableWithinAt
/-
**MDifferentiableWithinAt.congr_of_eventuallyEq_of_mem** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MDifferentiableWithinAt.congr_of_eventuallyEq_of_mem (h : MDiffAt[s] f x) 
(h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : MDiffAt[s] f₁ x
参数：h : MDiffAt[s] f x；h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.congr_of_eventuallyEq`：MDifferentiableWithinAt.c
ongr_of_eventuallyEq (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : MDiffAt[s] f₁ x
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
-/
theorem MDifferentiableWithinAt.congr_of_eventuallyEq_of_mem
    (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : MDiffAt[s] f₁ x :=
  h.congr_of_eventuallyEq h₁ (mem_of_mem_nhdsWithin hx h₁ :)
/-
**MDifferentiableWithinAt.congr_of_eventuallyEq_insert** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MDifferentiableWithinAt.congr_of_eventuallyEq_insert (h : MDiffAt[s] f x) 
(h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : MDiffAt[s] f₁ x
参数：h : MDiffAt[s] f x；h₁ : f₁ =ᶠ[𝓝[insert x s] x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.of_insert`：∀ {𝕜 : Type u_1} [inst : Nontrivially
NormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Normed
Space 𝕜 E] {H : Type u_…
· 使用定理 `MDifferentiableWithinAt.congr_of_eventuallyEq_of_mem`：MDifferentiableWit
hinAt.congr_of_eventuallyEq_of_mem (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (
hx : x in s) : MDiffAt[s] f₁ x
· 使用定理 `MDifferentiableWithinAt.insert`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {H : Type u_…
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem MDifferentiableWithinAt.congr_of_eventuallyEq_insert
    (h : MDiffAt[s] f x) (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) : MDiffAt[s] f₁ x :=
  (h.insert.congr_of_eventuallyEq_of_mem h₁ (mem_insert x s)).of_insert
/-
**Filter.EventuallyEq.mdifferentiableWithinAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.mdifferentiableWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx
 : f₁ x = f x) : MDiffAt[s] f x ↔ MDiffAt[s] f₁ x
参数：h₁ : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.mdifferentiablefWithinAt_iff`：Filter.EventuallyEq.md
ifferentiablefWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : MDiffAt[s]
 f₁ x ↔ MDiffAt[s] f x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Filter.EventuallyEq.mdifferentiableWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    MDiffAt[s] f x ↔ MDiffAt[s] f₁ x :=
  mdifferentiablefWithinAt_iff h₁.symm hx.symm
/-
**MDifferentiableWithinAt.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.congr_mono (h : MDiffAt[s] f x) (ht : forall x in 
t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t subseteq s) : MDiffAt[t] f₁ x
参数：h : MDiffAt[s] f x；ht : forall x in t, f₁ x = f x；hx : f₁ x = f x；h₁ : t subs
eteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `HasMFDerivWithinAt.congr_mono`：HasMFDerivWithinAt.congr_mono (h : HasMFD
erivAt[s] f x f') (ht : forall x in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t sub
seteq s) : HasMFDer…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem MDifferentiableWithinAt.congr_mono
    (h : MDiffAt[s] f x) (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) :
    MDiffAt[t] f₁ x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx h₁).mdifferentiableWithinAt
/-
**MDifferentiableWithinAt.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.congr (h : MDiffAt[s] f x) (ht : forall x in s, f₁
 x = f x) (hx : f₁ x = f x) : MDiffAt[s] f₁ x
参数：h : MDiffAt[s] f x；ht : forall x in s, f₁ x = f x；hx : f₁ x = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `HasMFDerivWithinAt.congr_mono`：HasMFDerivWithinAt.congr_mono (h : HasMFD
erivAt[s] f x f') (ht : forall x in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t sub
seteq s) : HasMFDer…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
-/
theorem MDifferentiableWithinAt.congr
    (h : MDiffAt[s] f x) (ht : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) :
    MDiffAt[s] f₁ x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt ht hx (Subset.refl _)).mdifferentiableWithinAt

/-- Version of `MDifferentiableWithinAt.congr` where `x` need not be contained in `s`,
but `f` and `f₁` are equal on a set containing both. -/
/-
**MDifferentiableWithinAt.congr'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.congr' (h : MDiffAt[s] f x) (ht : forall x in t, f
₁ x = f x) (hst : s subseteq t) (hxt : x in t) : MDiffAt[s] f₁ x
参数：h : MDiffAt[s] f x；ht : forall x in t, f₁ x = f x；hst : s subseteq t；hxt : x 
in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.congr`：MDifferentiableWithinAt.congr (h : MDiffA
t[s] f x) (ht : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : MDiffAt[s] f₁ x

--- 原说明 ---
Version of `MDifferentiableWithinAt.congr` where `x` need not be contained in `s
`,
but `f` and `f₁` are equal on a set containing both.
-/
theorem MDifferentiableWithinAt.congr'
    (h : MDiffAt[s] f x) (ht : ∀ x ∈ t, f₁ x = f x) (hst : s ⊆ t) (hxt : x ∈ t) : MDiffAt[s] f₁ x :=
  h.congr (fun _y hy ↦ ht _y (hst hy)) (ht x hxt)
/-
**Filter.EventuallyEq.mdifferentiableAt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.mdifferentiableAt_iff (h₁ : f₁ =ᶠ[𝓝 x] f) : MDiffAt f₁
 x ↔ MDiffAt f x
参数：h₁ : f₁ =ᶠ[𝓝 x] f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropAt_congr_iff_of_eventuallyE
q`：liftPropAt_congr_iff_of_eventuallyEq (h₁ : g' =ᶠ[𝓝 x] g) : LiftPropAt P g' x 
↔ LiftPropAt P g x
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
-/
theorem Filter.EventuallyEq.mdifferentiableAt_iff (h₁ : f₁ =ᶠ[𝓝 x] f) :
    MDiffAt f₁ x ↔ MDiffAt f x :=
  differentiableWithinAt_localInvariantProp.liftPropAt_congr_iff_of_eventuallyEq h₁
/-
**MDifferentiableOn.congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.congr (h : MDiff[s] f) (h₁ : forall y in s, f₁ y = f y) 
: MDiff[s] f₁
参数：h : MDiff[s] f；h₁ : forall y in s, f₁ y = f y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_congr`：liftPropOn_congr 
(h : LiftPropOn P g s) (h₁ : forall y in s, g' y = g y) : LiftPropOn P g' s
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
-/
theorem MDifferentiableOn.congr (h : MDiff[s] f) (h₁ : ∀ y ∈ s, f₁ y = f y) : MDiff[s] f₁ :=
  differentiableWithinAt_localInvariantProp.liftPropOn_congr h h₁
/-
**mdifferentiableOn_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mdifferentiableOn_congr (h₁ : forall y in s, f₁ y = f y) : MDiff[s] f₁ ↔ M
Diff[s] f
参数：h₁ : forall y in s, f₁ y = f y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StructureGroupoid.LocalInvariantProp.liftPropOn_congr_iff`：liftPropOn_co
ngr_iff (h₁ : forall y in s, g' y = g y) : LiftPropOn P g' s ↔ LiftPropOn P g s
· 使用定理 `differentiableWithinAt_localInvariantProp`：differentiableWithinAt_localI
nvariantProp : (contDiffGroupoid 1 I).LocalInvariantProp (contDiffGroupoid 1 I')
 (DifferentiableWithinAtProp I …
-/
theorem mdifferentiableOn_congr (h₁ : ∀ y ∈ s, f₁ y = f y) : MDiff[s] f₁ ↔ MDiff[s] f :=
  differentiableWithinAt_localInvariantProp.liftPropOn_congr_iff h₁
/-
**MDifferentiableOn.congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.congr_mono (h : MDiff[s] f) (h' : forall x in t, f₁ x = 
f x) (h₁ : t subseteq s) : MDiff[t] f₁
参数：h : MDiff[s] f；h' : forall x in t, f₁ x = f x；h₁ : t subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.congr_mono`：MDifferentiableWithinAt.congr_mono (
h : MDiffAt[s] f x) (ht : forall x in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t s
ubseteq s) : MDiffAt[t] …
-/
theorem MDifferentiableOn.congr_mono (h : MDiff[s] f) (h' : ∀ x ∈ t, f₁ x = f x) (h₁ : t ⊆ s) :
    MDiff[t] f₁ := fun x hx =>
  (h x (h₁ hx)).congr_mono h' (h' x hx) h₁
/-
**MDifferentiableAt.congr_of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.congr_of_eventuallyEq (h : MDiffAt f x) (hL : f₁ =ᶠ[𝓝 x]
 f) : MDiffAt f₁ x
参数：h : MDiffAt f x；hL : f₁ =ᶠ[𝓝 x] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `HasMFDerivAt.congr_of_eventuallyEq`：HasMFDerivAt.congr_of_eventuallyEq (
h : HasMFDerivAt% f x f') (h₁ : f₁ =ᶠ[𝓝 x] f) : HasMFDerivAt% f₁ x f'
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem MDifferentiableAt.congr_of_eventuallyEq (h : MDiffAt f x) (hL : f₁ =ᶠ[𝓝 x] f) :
    MDiffAt f₁ x :=
  (h.hasMFDerivAt.congr_of_eventuallyEq hL).mdifferentiableAt
/-
**MDifferentiableWithinAt.mfderivWithin_congr_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.mfderivWithin_congr_mono (h : MDiffAt[s] f x) (hs 
: forall x in t, f₁ x = f x) (hx : f₁ x = f x) (hxt : UniqueMDiffAt[t] x) (h₁ : 
t subseteq s) : mfderiv[t] f₁ x = mfderiv[s] f x
参数：h : MDiffAt[s] f x；hs : forall x in t, f₁ x = f x；hx : f₁ x = f x；hxt : Uniqu
eMDiffAt[t] x；h₁ : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `HasMFDerivWithinAt.congr_mono`：HasMFDerivWithinAt.congr_mono (h : HasMFD
erivAt[s] f x f') (ht : forall x in t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t sub
seteq s) : HasMFDer…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem MDifferentiableWithinAt.mfderivWithin_congr_mono (h : MDiffAt[s] f x)
    (hs : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : UniqueMDiffAt[t] x) (h₁ : t ⊆ s) :
    mfderiv[t] f₁ x = mfderiv[s] f x :=
  (HasMFDerivWithinAt.congr_mono h.hasMFDerivWithinAt hs hx h₁).mfderivWithin hxt
/-
**MDifferentiableWithinAt.mfderivWithin_mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.mfderivWithin_mono (h : MDiffAt[s] f x) (hxt : Uni
queMDiffAt[t] x) (h₁ : t subseteq s) : mfderiv[t] f x = mfderiv[s] f x
参数：h : MDiffAt[s] f x；hxt : UniqueMDiffAt[t] x；h₁ : t subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mfderivWithin_congr_mono`：MDifferentiableWithinA
t.mfderivWithin_congr_mono (h : MDiffAt[s] f x) (hs : forall x in t, f₁ x = f x)
 (hx : f₁ x = f x) (hxt : UniqueMDiffA…
-/
theorem MDifferentiableWithinAt.mfderivWithin_mono
    (h : MDiffAt[s] f x) (hxt : UniqueMDiffAt[t] x) (h₁ : t ⊆ s) :
    mfderiv[t] f x = mfderiv[s] f x :=
  h.mfderivWithin_congr_mono (fun _ _ ↦ rfl) rfl hxt h₁
/-
**MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin** 是 Mathlib 中的一个定
理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin (h : MDiffAt[
s] f x) (hxt : UniqueMDiffAt[t] x) (h₁ : s in 𝓝[t] x) : mfderiv[t] f x = mfderiv
[s] f x
参数：h : MDiffAt[s] f x；hxt : UniqueMDiffAt[t] x；h₁ : s in 𝓝[t] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `HasMFDerivWithinAt.mono_of_mem_nhdsWithin`：HasMFDerivWithinAt.mono_of_me
m_nhdsWithin (h : HasMFDerivAt[s] f x f') (ht : s in 𝓝[t] x) : HasMFDerivAt[t] f
 x f'
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin
    (h : MDiffAt[s] f x) (hxt : UniqueMDiffAt[t] x) (h₁ : s ∈ 𝓝[t] x) :
    mfderiv[t] f x = mfderiv[s] f x :=
  (HasMFDerivWithinAt.mono_of_mem_nhdsWithin h.hasMFDerivWithinAt h₁).mfderivWithin hxt

set_option backward.isDefEq.respectTransparency false in
/-
**Filter.EventuallyEq.mfderivWithin_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.mfderivWithin_eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f
 x) : mfderiv[s] f₁ x = mfderiv[s] f x
参数：hL : f₁ =ᶠ[𝓝[s] x] f；hx : f₁ x = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.EventuallyEq.mdifferentiableWithinAt_iff`：Filter.EventuallyEq.mdi
fferentiableWithinAt_iff (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : MDiffAt[s] f
 x ↔ MDiffAt[s] f₁ x
· 使用定理 `Filter.EventuallyEq.fderivWithin_eq`：Filter.EventuallyEq.fderivWithin_eq
 (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin
 𝕜 f s x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `extChartAt_preimage_mem_nhdsWithin`：extChartAt_preimage_mem_nhdsWithin {
x : M} (ht : t in 𝓝[s] x) : (extChartAt I x).symm ⁻¹' t in 𝓝[(extChartAt I x).sy
mm ⁻¹' s inter range I] …
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Filter.EventuallyEq.mfderivWithin_eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
    mfderiv[s] f₁ x = mfderiv[s] f x := by
  by_cases h : MDiffAt[s] f x
  · unfold mfderivWithin
    simp only [h, (hL.mdifferentiableWithinAt_iff hx).1 h, ↓reduceIte, writtenInExtChartAt]
    apply Filter.EventuallyEq.fderivWithin_eq; swap
    · simp [hx]
    filter_upwards [extChartAt_preimage_mem_nhdsWithin (I := I) hL] with y hy
    simp only [preimage_ofPred_eq, mem_ofPred_eq] at hy
    simp [-extChartAt, hy, hx]
  · unfold mfderivWithin
    rw [if_neg h, if_neg]
    rwa [← hL.mdifferentiableWithinAt_iff hx]
/-
**Filter.EventuallyEq.mfderivWithin_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.mfderivWithin_eq_of_mem (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : x
 in s) : mfderiv[s] f₁ x = mfderiv[s] f x
参数：hL : f₁ =ᶠ[𝓝[s] x] f；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.mfderivWithin_eq`：Filter.EventuallyEq.mfderivWithin_
eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : mfderiv[s] f₁ x = mfderiv[s] f x
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
-/
theorem Filter.EventuallyEq.mfderivWithin_eq_of_mem (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
    mfderiv[s] f₁ x = mfderiv[s] f x :=
  hL.mfderivWithin_eq (mem_of_mem_nhdsWithin hx hL :)
/-
**mfderivWithin_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_congr (hL : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : m
fderiv[s] f₁ x = mfderiv[s] f x
参数：hL : forall x in s, f₁ x = f x；hx : f₁ x = f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.mfderivWithin_eq`：Filter.EventuallyEq.mfderivWithin_
eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : mfderiv[s] f₁ x = mfderiv[s] f x
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem mfderivWithin_congr (hL : ∀ x ∈ s, f₁ x = f x) (hx : f₁ x = f x) :
    mfderiv[s] f₁ x = mfderiv[s] f x :=
  Filter.EventuallyEq.mfderivWithin_eq (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx
/-
**mfderivWithin_congr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_congr_of_mem (hL : forall x in s, f₁ x = f x) (hx : x in s) 
: mfderiv[s] f₁ x = mfderiv[s] f x
参数：hL : forall x in s, f₁ x = f x；hx : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.mfderivWithin_eq_of_mem`：Filter.EventuallyEq.mfderiv
Within_eq_of_mem (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : x in s) : mfderiv[s] f₁ x = mfderi
v[s] f x
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem mfderivWithin_congr_of_mem (hL : ∀ x ∈ s, f₁ x = f x) (hx : x ∈ s) :
    mfderiv[s] f₁ x = mfderiv[s] f x :=
  Filter.EventuallyEq.mfderivWithin_eq_of_mem (Filter.eventuallyEq_of_mem self_mem_nhdsWithin hL) hx
/-
**tangentMapWithin_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMapWithin_congr (h : forall x in s, f x = f₁ x) (p : TangentBundle 
I M) (hp : p.1 in s) : tangentMap[s] f p = tangentMap[s] f₁ p
参数：h : forall x in s, f x = f₁ x；p : TangentBundle I M；hp : p.1 in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Bundle.TotalSpace.ext`：∀ {B : Type u_1} {F : Type u_4} {E : B → Type u_5
} {x y : Bundle.TotalSpace F E},   x.proj = y.proj → x.snd ≍ y.snd → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tangentMapWithin.eq_1`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 
𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {
H : Type u_…
· 使用定理 `mfderivWithin_congr`：mfderivWithin_congr (hL : forall x in s, f₁ x = f x
) (hx : f₁ x = f x) : mfderiv[s] f₁ x = mfderiv[s] f x
-/
theorem tangentMapWithin_congr (h : ∀ x ∈ s, f x = f₁ x) (p : TangentBundle I M) (hp : p.1 ∈ s) :
    tangentMap[s] f p = tangentMap[s] f₁ p := by
  refine TotalSpace.ext (h p.1 hp) ?_
  rw [tangentMapWithin, h p.1 hp, tangentMapWithin, mfderivWithin_congr h (h _ hp)]
/-
**Filter.EventuallyEq.mfderiv_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.EventuallyEq.mfderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) : mfderiv% f₁ x = mfder
iv% f x
参数：hL : f₁ =ᶠ[𝓝 x] f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhds`：mem_of_mem_nhds : s in 𝓝 x -> x in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `Filter.EventuallyEq.mfderivWithin_eq`：Filter.EventuallyEq.mfderivWithin_
eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : mfderiv[s] f₁ x = mfderiv[s] f x
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
-/
theorem Filter.EventuallyEq.mfderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) : mfderiv% f₁ x = mfderiv% f x := by
  have A : f₁ x = f x := (mem_of_mem_nhds hL :)
  rw [← mfderivWithin_univ, ← mfderivWithin_univ]
  rw [← nhdsWithin_univ] at hL
  exact hL.mfderivWithin_eq A

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `TangentSpace I' (f x)` is
definitionally equal to `E'`. -/
/-
**mfderiv_congr_point** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_congr_point {x' : M} (h : x = x') : @Eq (E ->L[𝕜] E') (mfderiv% f 
x) (mfderiv% f x')
参数：h : x = x'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A congruence lemma for `mfderiv`, (ab)using the fact that `TangentSpace I' (f x)
` is
definitionally equal to `E'`.
-/
theorem mfderiv_congr_point {x' : M} (h : x = x') :
    @Eq (E →L[𝕜] E') (mfderiv% f x) (mfderiv% f x') := by subst h; rfl

/-- A congruence lemma for `mfderiv`, (ab)using the fact that `TangentSpace I' (f x)` is
definitionally equal to `E'`. -/
/-
**mfderiv_congr** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_congr {f' : M -> M'} (h : f = f') : @Eq (E ->L[𝕜] E') (mfderiv% f 
x) (mfderiv% f' x)
参数：h : f = f'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A congruence lemma for `mfderiv`, (ab)using the fact that `TangentSpace I' (f x)
` is
definitionally equal to `E'`.
-/
theorem mfderiv_congr {f' : M → M'} (h : f = f') :
    @Eq (E →L[𝕜] E') (mfderiv% f x) (mfderiv% f' x) := by subst h; rfl

/-! ### Composition lemmas -/

variable (x)

set_option backward.isDefEq.respectTransparency false in
/-
**HasMFDerivWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivWithinAt.comp (hg : HasMFDerivAt[u] g (f x) g') (hf : HasMFDeriv
At[s] f x f') (hst : s subseteq f ⁻¹' u) : HasMFDerivAt[s] (g ∘ f) x (g'.comp f'
)
参数：hg : HasMFDerivAt[u] g (f x) g'；hf : HasMFDerivAt[s] f x f'；hst : s subseteq 
f ⁻¹' u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousWithinAt.comp`：ContinuousWithinAt.comp {g : β -> γ} {t : Set β
} (hg : ContinuousWithinAt g t (f x)) (hf : ContinuousWithinAt f s x) (h : MapsT
o f s t) : Co…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `extChartAt_preimage_mem_nhdsWithin`：extChartAt_preimage_mem_nhdsWithin {
x : M} (ht : t in 𝓝[s] x) : (extChartAt I x).symm ⁻¹' t in 𝓝[(extChartAt I x).sy
mm ⁻¹' s inter range I] …
· 使用定理 `ContinuousWithinAt.preimage_mem_nhdsWithin`：ContinuousWithinAt.preimage_
mem_nhdsWithin {t : Set β} (h : ContinuousWithinAt f s x) (ht : t in 𝓝 (f x)) : 
f ⁻¹' t in 𝓝[s] x
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasFDerivWithinAt_inter'`：hasFDerivWithinAt_inter' (h : t in 𝓝[s] x) : H
asFDerivWithinAt f f' (s inter t) x ↔ HasFDerivWithinAt f f' s x
· 使用定理 `extChartAt_preimage_inter_eq`：extChartAt_preimage_inter_eq (x : M) : (ex
tChartAt I x).symm ⁻¹' (s inter t) inter range I = (extChartAt I x).symm ⁻¹' s i
nter range I inter…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasFDerivWithinAt.comp`：HasFDerivWithinAt.comp {g : F -> G} {g' : F ->L[
𝕜] G} {t : Set F} (hg : HasFDerivWithinAt g g' t (f x)) (hf : HasFDerivWithinAt 
f f' s x) (h…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `HasFDerivWithinAt.congr_of_eventuallyEq`：HasFDerivWithinAt.congr_of_even
tuallyEq (h : HasFDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f 
x) : HasFDerivWithinAt f₁ f' …
· 使用定理 `writtenInExtChartAt_comp`：writtenInExtChartAt_comp (h : ContinuousWithin
At f s x) : writtenInExtChartAt I I'' x (g ∘ f) =ᶠ[𝓝[(extChartAt I x).symm ⁻¹' s
 inter range I…
-/
theorem HasMFDerivWithinAt.comp (hg : HasMFDerivAt[u] g (f x) g')
    (hf : HasMFDerivAt[s] f x f') (hst : s ⊆ f ⁻¹' u) :
    HasMFDerivAt[s] (g ∘ f) x (g'.comp f') := by
  refine ⟨ContinuousWithinAt.comp hg.1 hf.1 hst, ?_⟩
  have A :
    HasFDerivWithinAt (writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f)
      (ContinuousLinearMap.comp g' f' : E →L[𝕜] E'') ((extChartAt I x).symm ⁻¹' s ∩ range I)
      ((extChartAt I x) x) := by
    have :
      (extChartAt I x).symm ⁻¹' f ⁻¹' (extChartAt I' (f x)).source ∈
        𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
      extChartAt_preimage_mem_nhdsWithin
        (hf.1.preimage_mem_nhdsWithin (extChartAt_source_mem_nhds _))
    unfold HasMFDerivWithinAt at *
    rw [← hasFDerivWithinAt_inter' this, ← extChartAt_preimage_inter_eq] at hf ⊢
    have : writtenInExtChartAt I I' x f ((extChartAt I x) x) = (extChartAt I' (f x)) (f x) := by
      simp only [mfld_simps]
    rw [← this] at hg
    apply HasFDerivWithinAt.comp ((extChartAt I x) x) hg.2 hf.2 _
    intro y hy
    simp only [mfld_simps] at hy
    have : f (((chartAt H x).symm : H → M) (I.symm y)) ∈ u := hst hy.1.1
    simp only [hy, this, mfld_simps]
  apply A.congr_of_eventuallyEq (writtenInExtChartAt_comp hf.1)
  simp only [mfld_simps]

/-- The **chain rule for manifolds**. -/
/-
**HasMFDerivAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.comp (hg : HasMFDerivAt% g (f x) g') (hf : HasMFDerivAt% f x 
f') : HasMFDerivAt% (g ∘ f) x (g'.comp f')
参数：hg : HasMFDerivAt% g (f x) g'；hf : HasMFDerivAt% f x f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
· 使用定理 `HasMFDerivWithinAt.comp`：HasMFDerivWithinAt.comp (hg : HasMFDerivAt[u] g
 (f x) g') (hf : HasMFDerivAt[s] f x f') (hst : s subseteq f ⁻¹' u) : HasMFDeriv
At[s] (g ∘ f)…
· 使用定理 `HasMFDerivWithinAt.mono`：HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f 
x f') (hst : s subseteq t) : HasMFDerivAt[s] f x f'
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.subset_preimage_univ`：subset_preimage_univ {s : Set α} : s subseteq 
f ⁻¹' univ

--- 原说明 ---
The **chain rule for manifolds**.
-/
theorem HasMFDerivAt.comp (hg : HasMFDerivAt% g (f x) g') (hf : HasMFDerivAt% f x f') :
    HasMFDerivAt% (g ∘ f) x (g'.comp f') := by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ
/-
**HasMFDerivAt.comp_hasMFDerivWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasMFDerivAt.comp_hasMFDerivWithinAt (hg : HasMFDerivAt% g (f x) g') (hf :
 HasMFDerivAt[s] f x f') : HasMFDerivAt[s] (g ∘ f) x (g'.comp f')
参数：hg : HasMFDerivAt% g (f x) g'；hf : HasMFDerivAt[s] f x f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.comp`：HasMFDerivWithinAt.comp (hg : HasMFDerivAt[u] g
 (f x) g') (hf : HasMFDerivAt[s] f x f') (hst : s subseteq f ⁻¹' u) : HasMFDeriv
At[s] (g ∘ f)…
· 使用定理 `HasMFDerivWithinAt.mono`：HasMFDerivWithinAt.mono (h : HasMFDerivAt[t] f 
x f') (hst : s subseteq t) : HasMFDerivAt[s] f x f'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hasMFDerivWithinAt_univ`：hasMFDerivWithinAt_univ : HasMFDerivAt[univ] f 
x f' ↔ HasMFDerivAt% f x f'
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Set.subset_preimage_univ`：subset_preimage_univ {s : Set α} : s subseteq 
f ⁻¹' univ
-/
theorem HasMFDerivAt.comp_hasMFDerivWithinAt (hg : HasMFDerivAt% g (f x) g')
    (hf : HasMFDerivAt[s] f x f') : HasMFDerivAt[s] (g ∘ f) x (g'.comp f') := by
  rw [← hasMFDerivWithinAt_univ] at *
  exact HasMFDerivWithinAt.comp x (hg.mono (subset_univ _)) hf subset_preimage_univ
/-
**MDifferentiableWithinAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.comp (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f 
x) (h : s subseteq f ⁻¹' u) : MDifferentiableWithinAt I I'' (g ∘ f) s x
参数：hg : MDiffAt[u] g (f x)；hf : MDiffAt[s] f x；h : s subseteq f ⁻¹' u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ChartedSpace.LiftPropWithinAt.prop`：∀ {H : Type u_1} {M : Type u_2} {H' 
: Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 : TopologicalS
pace M] [inst_2 : Charte…
· 使用定理 `ChartedSpace.LiftPropWithinAt.continuousWithinAt`：∀ {H : Type u_1} {M : 
Type u_2} {H' : Type u_3} {M' : Type u_4} [inst : TopologicalSpace H]   [inst_1 
: TopologicalSpace M] [inst_2 : Charte…
· 使用定理 `HasMFDerivWithinAt.mdifferentiableWithinAt`：HasMFDerivWithinAt.mdifferen
tiableWithinAt (h : HasMFDerivAt[s] f x f') : MDiffAt[s] f x
· 使用定理 `HasMFDerivWithinAt.comp`：HasMFDerivWithinAt.comp (hg : HasMFDerivAt[u] g
 (f x) g') (hf : HasMFDerivAt[s] f x f') (hst : s subseteq f ⁻¹' u) : HasMFDeriv
At[s] (g ∘ f)…
-/
theorem MDifferentiableWithinAt.comp (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x)
    (h : s ⊆ f ⁻¹' u) : MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  rcases hf.2 with ⟨f', hf'⟩
  have F : HasMFDerivAt[s] f x f' := ⟨hf.1, hf'⟩
  rcases hg.2 with ⟨g', hg'⟩
  have G : HasMFDerivAt[u] g (f x) g' := ⟨hg.1, hg'⟩
  exact (HasMFDerivWithinAt.comp x G F h).mdifferentiableWithinAt
/-
**MDifferentiableWithinAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.comp_of_eq {y : M'} (hg : MDiffAt[u] g y) (hf : MD
iffAt[s] f x) (h : s subseteq f ⁻¹' u) (hy : f x = y) : MDiffAt[s] (g ∘ f) x
参数：hg : MDiffAt[u] g y；hf : MDiffAt[s] f x；h : s subseteq f ⁻¹' u；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.comp`：MDifferentiableWithinAt.comp (hg : MDiffAt
[u] g (f x)) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) : MDifferentiableWit
hinAt I I'' (g ∘ f…
-/
theorem MDifferentiableWithinAt.comp_of_eq
    {y : M'} (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x) (h : s ⊆ f ⁻¹' u) (hy : f x = y) :
    MDiffAt[s] (g ∘ f) x := by
  subst hy; exact hg.comp _ hf h
/-
**MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin (hg : MDiffAt[u] g
 (f x)) (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) : MDiffAt[s] (g ∘ f) x
参数：hg : MDiffAt[u] g (f x)；hf : MDiffAt[s] f x；h : f ⁻¹' u in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.mono_of_mem_nhdsWithin`：MDifferentiableWithinAt.
mono_of_mem_nhdsWithin (h : MDiffAt[s] f x) {t : Set M} (hst : s in 𝓝[t] x) : MD
iffAt[t] f x
· 使用定理 `MDifferentiableWithinAt.comp`：MDifferentiableWithinAt.comp (hg : MDiffAt
[u] g (f x)) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) : MDifferentiableWit
hinAt I I'' (g ∘ f…
· 使用定理 `MDifferentiableWithinAt.mono`：MDifferentiableWithinAt.mono (hst : s subs
eteq t) (h : MDiffAt[t] f x) : MDiffAt[s] f x
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin
    (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x) (h : f ⁻¹' u ∈ 𝓝[s] x) : MDiffAt[s] (g ∘ f) x :=
  (hg.comp _ (hf.mono inter_subset_right) inter_subset_left).mono_of_mem_nhdsWithin
    (Filter.inter_mem h self_mem_nhdsWithin)
/-
**MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq {y : M'} (hg
 : MDiffAt[u] g y) (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) (hy : f x = y) 
: MDifferentiableWithinAt I I'' (g ∘ f) s x
参数：hg : MDiffAt[u] g y；hf : MDiffAt[s] f x；h : f ⁻¹' u in 𝓝[s] x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin`：MDifferentiable
WithinAt.comp_of_preimage_mem_nhdsWithin (hg : MDiffAt[u] g (f x)) (hf : MDiffAt
[s] f x) (h : f ⁻¹' u in 𝓝[s] x) : MDiffAt[s]…
-/
theorem MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin_of_eq
    {y : M'} (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x) (h : f ⁻¹' u ∈ 𝓝[s] x) (hy : f x = y) :
    MDifferentiableWithinAt I I'' (g ∘ f) s x := by
  subst hy; exact MDifferentiableWithinAt.comp_of_preimage_mem_nhdsWithin _ hg hf h
/-
**MDifferentiableAt.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : MDiffAt
 (g ∘ f) x
参数：hg : MDiffAt g (f x)；hf : MDiffAt f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mdifferentiableAt`：HasMFDerivAt.mdifferentiableAt (h : HasM
FDerivAt% f x f') : MDiffAt f x
· 使用定理 `HasMFDerivAt.comp`：HasMFDerivAt.comp (hg : HasMFDerivAt% g (f x) g') (hf
 : HasMFDerivAt% f x f') : HasMFDerivAt% (g ∘ f) x (g'.comp f')
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem MDifferentiableAt.comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : MDiffAt (g ∘ f) x :=
  (hg.hasMFDerivAt.comp x hf.hasMFDerivAt).mdifferentiableAt
/-
**MDifferentiableAt.comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.comp_of_eq {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x
) (hy : f x = y) : MDiffAt (g ∘ f) x
参数：hg : MDiffAt g y；hf : MDiffAt f x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
-/
theorem MDifferentiableAt.comp_of_eq {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y) :
    MDiffAt (g ∘ f) x := by
  subst hy; exact hg.comp _ hf
/-
**MDifferentiableAt.comp_mdifferentiableWithinAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableAt.comp_mdifferentiableWithinAt (hg : MDiffAt g (f x)) (hf 
: MDiffAt[s] f x) : MDiffAt[s] (g ∘ f) x
参数：hg : MDiffAt g (f x)；hf : MDiffAt[s] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.comp`：MDifferentiableWithinAt.comp (hg : MDiffAt
[u] g (f x)) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) : MDifferentiableWit
hinAt I I'' (g ∘ f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableWithinAt_univ`：mdifferentiableWithinAt_univ : MDiffAt[uni
v] f x ↔ MDiffAt f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem MDifferentiableAt.comp_mdifferentiableWithinAt
    (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s] (g ∘ f) x := by
  rw [← mdifferentiableWithinAt_univ] at hg
  exact hg.comp _ hf (by simp)
/-
**MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq {y : M'} (hg : MDiffA
t g y) (hf : MDiffAt[s] f x) (hy : f x = y) : MDiffAt[s] (g ∘ f) x
参数：hg : MDiffAt g y；hf : MDiffAt[s] f x；hy : f x = y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp_mdifferentiableWithinAt`：MDifferentiableAt.comp_m
differentiableWithinAt (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) : MDiffAt[s]
 (g ∘ f) x
-/
theorem MDifferentiableAt.comp_mdifferentiableWithinAt_of_eq
    {y : M'} (hg : MDiffAt g y) (hf : MDiffAt[s] f x) (hy : f x = y) : MDiffAt[s] (g ∘ f) x := by
  subst hy; exact hg.comp_mdifferentiableWithinAt _ hf
/-
**mfderivWithin_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_comp (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x) (h : s 
subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] (g ∘ f) x = (mfderiv[u
] g (f x)).comp (mfderiv[s] f x)
参数：hg : MDiffAt[u] g (f x)；hf : MDiffAt[s] f x；h : s subseteq f ⁻¹' u；hxs : Uniq
ueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivWithinAt.mfderivWithin`：∀ {𝕜 : Type u_1} [inst : NontriviallyN
ormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {H : Type u_…
· 使用定理 `HasMFDerivWithinAt.comp`：HasMFDerivWithinAt.comp (hg : HasMFDerivAt[u] g
 (f x) g') (hf : HasMFDerivAt[s] f x f') (hst : s subseteq f ⁻¹' u) : HasMFDeriv
At[s] (g ∘ f)…
· 使用定理 `MDifferentiableWithinAt.hasMFDerivWithinAt`：MDifferentiableWithinAt.hasM
FDerivWithinAt (h : MDiffAt[s] f x) : HasMFDerivAt[s] f x (mfderiv[s] f x)
-/
theorem mfderivWithin_comp
    (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x) (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (g ∘ f) x = (mfderiv[u] g (f x)).comp (mfderiv[s] f x) := by
  apply HasMFDerivWithinAt.mfderivWithin _ hxs
  exact HasMFDerivWithinAt.comp x hg.hasMFDerivWithinAt hf.hasMFDerivWithinAt h
/-
**mfderivWithin_comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_comp_of_eq {x : M} {y : M'} (hg : MDiffAt[u] g y) (hf : MDif
fAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
 mfderiv[s] (g ∘ f) x = (mfderiv[u] g y).comp (mfderiv[s] f x)
参数：hg : MDiffAt[u] g y；hf : MDiffAt[s] f x；h : s subseteq f ⁻¹' u；hxs : UniqueMD
iffAt[s] x；hy : f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderivWithin_comp`：mfderivWithin_comp (hg : MDiffAt[u] g (f x)) (hf : M
DiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] 
(g ∘ f) …
-/
theorem mfderivWithin_comp_of_eq {x : M} {y : M'} (hg : MDiffAt[u] g y)
    (hf : MDiffAt[s] f x) (h : s ⊆ f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
    mfderiv[s] (g ∘ f) x = (mfderiv[u] g y).comp (mfderiv[s] f x) := by
  subst hy; exact mfderivWithin_comp x hg hf h hxs
/-
**mfderivWithin_comp_of_preimage_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderivWithin_comp_of_preimage_mem_nhdsWithin (hg : MDiffAt[u] g (f x)) (h
f : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) (hxs : UniqueMDiffAt[s] x) : mfderiv
[s] (g ∘ f) x = (mfderiv[u] g (f x)).comp (mfderiv[s] f x)
参数：hg : MDiffAt[u] g (f x)；hf : MDiffAt[s] f x；h : f ⁻¹' u in 𝓝[s] x；hxs : Uniqu
eMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin`：MDifferent
iableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin (h : MDiffAt[s] f x) (hxt : U
niqueMDiffAt[t] x) (h₁ : s in 𝓝[t] x) : mfderiv[t]…
· 使用定理 `MDifferentiableWithinAt.comp`：MDifferentiableWithinAt.comp (hg : MDiffAt
[u] g (f x)) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) : MDifferentiableWit
hinAt I I'' (g ∘ f…
· 使用定理 `MDifferentiableWithinAt.mono`：MDifferentiableWithinAt.mono (hst : s subs
eteq t) (h : MDiffAt[t] f x) : MDiffAt[s] f x
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_comp`：mfderivWithin_comp (hg : MDiffAt[u] g (f x)) (hf : M
DiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] 
(g ∘ f) …
· 使用定理 `UniqueMDiffWithinAt.inter'`：UniqueMDiffWithinAt.inter' (hs : UniqueMDiff
At[s] x) (ht : t in 𝓝[s] x) : UniqueMDiffAt[s inter t] x
-/
theorem mfderivWithin_comp_of_preimage_mem_nhdsWithin (hg : MDiffAt[u] g (f x))
    (hf : MDiffAt[s] f x) (h : f ⁻¹' u ∈ 𝓝[s] x) (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (g ∘ f) x = (mfderiv[u] g (f x)).comp (mfderiv[s] f x) := by
  have A : s ∩ f ⁻¹' u ∈ 𝓝[s] x := Filter.inter_mem self_mem_nhdsWithin h
  have B : mfderiv[s] (g ∘ f) x = mfderiv[s ∩ f ⁻¹' u] (g ∘ f) x := by
    apply MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin _ hxs A
    exact hg.comp _ (hf.mono inter_subset_left) inter_subset_right
  have C : mfderiv[s] f x = mfderiv[s ∩ f ⁻¹' u] f x :=
    MDifferentiableWithinAt.mfderivWithin_mono_of_mem_nhdsWithin (hf.mono inter_subset_left) hxs A
  rw [B, C]
  exact mfderivWithin_comp _ hg (hf.mono inter_subset_left) inter_subset_right (hxs.inter' h)
/-
**mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq {y : M'} (hg : MDiffAt
[u] g y) (hf : MDiffAt[s] f x) (h : f ⁻¹' u in 𝓝[s] x) (hxs : UniqueMDiffAt[s] x
) (hy : f x = y) : mfderiv[s] (g ∘ f) x = (mfderiv[u] g y).comp (mfderiv[s] f x)
参数：hg : MDiffAt[u] g y；hf : MDiffAt[s] f x；h : f ⁻¹' u in 𝓝[s] x；hxs : UniqueMDi
ffAt[s] x；hy : f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderivWithin_comp_of_preimage_mem_nhdsWithin`：mfderivWithin_comp_of_pre
image_mem_nhdsWithin (hg : MDiffAt[u] g (f x)) (hf : MDiffAt[s] f x) (h : f ⁻¹' 
u in 𝓝[s] x) (hxs : UniqueMDiffAt[s…
-/
theorem mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq {y : M'}
    (hg : MDiffAt[u] g y) (hf : MDiffAt[s] f x) (h : f ⁻¹' u ∈ 𝓝[s] x) (hxs : UniqueMDiffAt[s] x)
    (hy : f x = y) : mfderiv[s] (g ∘ f) x = (mfderiv[u] g y).comp (mfderiv[s] f x) := by
  subst hy; exact mfderivWithin_comp_of_preimage_mem_nhdsWithin _ hg hf h hxs
/-
**mfderiv_comp_mfderivWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_comp_mfderivWithin (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x) (h
xs : UniqueMDiffAt[s] x) : mfderiv[s] (g ∘ f) x = (mfderiv% g (f x)).comp (mfder
iv[s] f x)
参数：hg : MDiffAt g (f x)；hf : MDiffAt[s] f x；hxs : UniqueMDiffAt[s] x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mfderivWithin_univ`：mfderivWithin_univ : mfderiv[univ] f = mfderiv% f
· 使用定理 `mfderivWithin_comp`：mfderivWithin_comp (hg : MDiffAt[u] g (f x)) (hf : M
DiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] 
(g ∘ f) …
· 使用定理 `MDifferentiableAt.mdifferentiableWithinAt`：MDifferentiableAt.mdifferenti
ableWithinAt (h : MDiffAt f x) : MDiffAt[s] f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem mfderiv_comp_mfderivWithin (hg : MDiffAt g (f x)) (hf : MDiffAt[s] f x)
    (hxs : UniqueMDiffAt[s] x) :
    mfderiv[s] (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv[s] f x) := by
  rw [← mfderivWithin_univ]
  exact mfderivWithin_comp _ hg.mdifferentiableWithinAt hf (by simp) hxs
/-
**mfderiv_comp_mfderivWithin_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_comp_mfderivWithin_of_eq {x : M} {y : M'} (hg : MDiffAt g y) (hf :
 MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) : mfderiv[s] (g ∘ f) 
x = (mfderiv% g y).comp (mfderiv[s] f x)
参数：hg : MDiffAt g y；hf : MDiffAt[s] f x；hxs : UniqueMDiffAt[s] x；hy : f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderiv_comp_mfderivWithin`：mfderiv_comp_mfderivWithin (hg : MDiffAt g (
f x)) (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] (g ∘ f) x = 
(mfderiv% g (f x…
-/
theorem mfderiv_comp_mfderivWithin_of_eq {x : M} {y : M'} (hg : MDiffAt g y)
    (hf : MDiffAt[s] f x) (hxs : UniqueMDiffAt[s] x) (hy : f x = y) :
    mfderiv[s] (g ∘ f) x = (mfderiv% g y).comp (mfderiv[s] f x) := by
  subst hy; exact mfderiv_comp_mfderivWithin x hg hf hxs
/-
**mfderiv_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : mfderiv% (g ∘ f) 
x = (mfderiv% g (f x)).comp (mfderiv% f x)
参数：hg : MDiffAt g (f x)；hf : MDiffAt f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasMFDerivAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜
] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H
 : Type u_…
· 使用定理 `HasMFDerivAt.comp`：HasMFDerivAt.comp (hg : HasMFDerivAt% g (f x) g') (hf
 : HasMFDerivAt% f x f') : HasMFDerivAt% (g ∘ f) x (g'.comp f')
· 使用定理 `MDifferentiableAt.hasMFDerivAt`：MDifferentiableAt.hasMFDerivAt (h : MDif
fAt f x) : HasMFDerivAt% f x (mfderiv% f x)
-/
theorem mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) :
    mfderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x) := by
  apply HasMFDerivAt.mfderiv
  exact HasMFDerivAt.comp x hg.hasMFDerivAt hf.hasMFDerivAt
/-
**mfderiv_comp_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_comp_of_eq {x : M} {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) 
(hy : f x = y) : mfderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x)
参数：hg : MDiffAt g y；hf : MDiffAt f x；hy : f x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderiv_comp`：mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : m
fderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x)
-/
theorem mfderiv_comp_of_eq {x : M} {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y) :
    mfderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x) := by
  subst hy; exact mfderiv_comp x hg hf
/-
**mfderiv_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_comp_apply (hg : MDiffAt g (f x)) (hf : MDiffAt f x) (v : TangentS
pace% x) : mfderiv% (g ∘ f) x v = (mfderiv% g (f x)) ((mfderiv% f x) v)
参数：hg : MDiffAt g (f x)；hf : MDiffAt f x；v : TangentSpace% x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_comp`：mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : m
fderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x)
-/
theorem mfderiv_comp_apply (hg : MDiffAt g (f x)) (hf : MDiffAt f x) (v : TangentSpace% x) :
    mfderiv% (g ∘ f) x v = (mfderiv% g (f x)) ((mfderiv% f x) v) := by
  rw [mfderiv_comp _ hg hf]
  rfl
/-
**mfderiv_comp_apply_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mfderiv_comp_apply_of_eq {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (h
y : f x = y) (v : TangentSpace% x) : mfderiv% (g ∘ f) x v = (mfderiv% g y) ((mfd
eriv% f x) v)
参数：hg : MDiffAt g y；hf : MDiffAt f x；hy : f x = y；v : TangentSpace% x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mfderiv_comp_apply`：mfderiv_comp_apply (hg : MDiffAt g (f x)) (hf : MDif
fAt f x) (v : TangentSpace% x) : mfderiv% (g ∘ f) x v = (mfderiv% g (f x)) ((mfd
eriv% f …
-/
theorem mfderiv_comp_apply_of_eq
    {y : M'} (hg : MDiffAt g y) (hf : MDiffAt f x) (hy : f x = y) (v : TangentSpace% x) :
    mfderiv% (g ∘ f) x v = (mfderiv% g y) ((mfderiv% f x) v) := by
  subst hy; exact mfderiv_comp_apply _ hg hf v
/-
**MDifferentiableOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiableOn.comp (hg : MDiff[u] g) (hf : MDiff[s] f) (st : s subsete
q f ⁻¹' u) : MDiff[s] (g ∘ f)
参数：hg : MDiff[u] g；hf : MDiff[s] f；st : s subseteq f ⁻¹' u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableWithinAt.comp`：MDifferentiableWithinAt.comp (hg : MDiffAt
[u] g (f x)) (hf : MDiffAt[s] f x) (h : s subseteq f ⁻¹' u) : MDifferentiableWit
hinAt I I'' (g ∘ f…
-/
theorem MDifferentiableOn.comp (hg : MDiff[u] g) (hf : MDiff[s] f) (st : s ⊆ f ⁻¹' u) :
    MDiff[s] (g ∘ f) := fun x hx =>
  MDifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st
/-
**MDifferentiable.comp_mdifferentiableOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.comp_mdifferentiableOn (hg : MDiff g) (hf : MDiff[s] f) : 
MDiff[s] (g ∘ f)
参数：hg : MDiff g；hf : MDiff[s] f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableOn.comp`：MDifferentiableOn.comp (hg : MDiff[u] g) (hf : M
Diff[s] f) (st : s subseteq f ⁻¹' u) : MDiff[s] (g ∘ f)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mdifferentiableOn_univ`：mdifferentiableOn_univ : MDiff[univ] f ↔ MDiff f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem MDifferentiable.comp_mdifferentiableOn (hg : MDiff g) (hf : MDiff[s] f) :
    MDiff[s] (g ∘ f) := by
  rw [← mdifferentiableOn_univ] at hg
  exact hg.comp hf (by simp)
/-
**MDifferentiable.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MDifferentiable.comp (hg : MDiff g) (hf : MDiff f) : MDiff (g ∘ f)
参数：hg : MDiff g；hf : MDiff f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MDifferentiableAt.comp`：MDifferentiableAt.comp (hg : MDiffAt g (f x)) (h
f : MDiffAt f x) : MDiffAt (g ∘ f) x
-/
theorem MDifferentiable.comp (hg : MDiff g) (hf : MDiff f) : MDiff (g ∘ f) :=
  fun x => MDifferentiableAt.comp x (hg (f x)) (hf x)
/-
**tangentMapWithin_comp_at** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMapWithin_comp_at (p : TangentBundle I M) (hg : MDiffAt[u] g (f p.1
)) (hf : MDiffAt[s] f p.1) (h : s subseteq f ⁻¹' u) (hps : UniqueMDiffAt[s] p.1)
 : tangentMap[s] (g ∘ f) p = tangentMap[u] g (tangentMap[s] f p)
参数：p : TangentBundle I M；hg : MDiffAt[u] g (f p.1)；hf : MDiffAt[s] f p.1；h : s s
ubseteq f ⁻¹' u；hps : UniqueMDiffAt[s] p.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderivWithin_comp`：mfderivWithin_comp (hg : MDiffAt[u] g (f x)) (hf : M
DiffAt[s] f x) (h : s subseteq f ⁻¹' u) (hxs : UniqueMDiffAt[s] x) : mfderiv[s] 
(g ∘ f) …
-/
theorem tangentMapWithin_comp_at (p : TangentBundle I M) (hg : MDiffAt[u] g (f p.1))
    (hf : MDiffAt[s] f p.1) (h : s ⊆ f ⁻¹' u) (hps : UniqueMDiffAt[s] p.1) :
    tangentMap[s] (g ∘ f) p = tangentMap[u] g (tangentMap[s] f p) := by
  simp only [tangentMapWithin, mfld_simps]
  rw [mfderivWithin_comp p.1 hg hf h hps]
  rfl
/-
**tangentMap_comp_at** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMap_comp_at (p : TangentBundle I M) (hg : MDiffAt g (f p.1)) (hf : 
MDiffAt f p.1) : tangentMap% (g ∘ f) p = tangentMap% g (tangentMap% f p)
参数：p : TangentBundle I M；hg : MDiffAt g (f p.1)；hf : MDiffAt f p.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mfderiv_comp`：mfderiv_comp (hg : MDiffAt g (f x)) (hf : MDiffAt f x) : m
fderiv% (g ∘ f) x = (mfderiv% g (f x)).comp (mfderiv% f x)
-/
theorem tangentMap_comp_at (p : TangentBundle I M) (hg : MDiffAt g (f p.1)) (hf : MDiffAt f p.1) :
    tangentMap% (g ∘ f) p = tangentMap% g (tangentMap% f p) := by
  simp only [tangentMap, mfld_simps]
  rw [mfderiv_comp p.1 hg hf]
  rfl
/-
**tangentMap_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMap_comp (hg : MDiff g) (hf : MDiff f) : tangentMap% (g ∘ f) = tang
entMap% g ∘ tangentMap% f
参数：hg : MDiff g；hf : MDiff f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tangentMap_comp_at`：tangentMap_comp_at (p : TangentBundle I M) (hg : MDi
ffAt g (f p.1)) (hf : MDiffAt f p.1) : tangentMap% (g ∘ f) p = tangentMap% g (ta
ngentMap…
-/
theorem tangentMap_comp (hg : MDiff g) (hf : MDiff f) :
    tangentMap% (g ∘ f) = tangentMap% g ∘ tangentMap% f := by
  ext p : 1; exact tangentMap_comp_at _ (hg _) (hf _)

end DerivativesProperties

