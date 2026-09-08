/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Geometry.Manifold.Notation

/-! # Tangent bundles

This file defines the tangent bundle as a `C^n` vector bundle.

Let `M` be a manifold with model `I` on `(E, H)`. The tangent space `TangentSpace I (x : M)` has
already been defined as a type synonym for `E`, and the tangent bundle `TangentBundle I M` as an
abbrev of `Bundle.TotalSpace E (TangentSpace I : M → Type _)`.

In this file, when `M` is `C^1`, we construct a vector bundle structure
on `TangentBundle I M` using the `VectorBundleCore` construction indexed by the charts of `M`
with fibers `E`. Given two charts `i, j : OpenPartialHomeomorph M H`, the coordinate change
between `i` and `j` at a point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`.
This defines a vector bundle `TangentBundle` with fibers `TangentSpace`.

## Main definitions and results

* `tangentBundleCore I M` is the vector bundle core for the tangent bundle over `M`.

* When `M` is a `C^{n+1}` manifold, `TangentBundle I M` has a `C^n` vector bundle
  structure over `M`. In particular, it is a topological space, a vector bundle, a fiber bundle,
  and a `C^n` manifold.
-/

@[expose] public section


open Bundle Set IsManifold OpenPartialHomeomorph ContinuousLinearMap

open scoped Manifold Topology Bundle ContDiff

noncomputable section

section General

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ∞ω} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Auxiliary lemma for tangent spaces: the derivative of a coordinate change between two charts is
  `C^n` on its source. -/
/-
**contDiffOn_fderiv_coord_change** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_fderiv_coord_change [IsManifold I (n + 1) M] (i j : atlas H M) 
: ContDiffOn 𝕜 n (fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I))
 ((i.1.extend I).symm ≫ j.1.extend I).source
参数：n + 1；i j : atlas H M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] {a b c : α
} [inst : LE α], a = b → b ⊆ c → a ⊆ c
· 使用引理 `ModelWithCorners.extendCoordChange_source`：extendCoordChange_source : (I
.extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `ContDiffWithinAt.mono`：ContDiffWithinAt.mono (h : ContDiffWithinAt 𝕜 n f
 s x) {t : Set E} (hst : t subseteq s) : ContDiffWithinAt 𝕜 n f t x
· 使用定理 `ContDiffWithinAt.fderivWithin_right`：ContDiffWithinAt.fderivWithin_right
 (hf : ContDiffWithinAt 𝕜 n f s x₀) (hs : UniqueDiffOn 𝕜 s) (hmn : m + 1 <= n) (
hx₀s : x₀ in s) : ContDif…
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用引理 `ModelWithCorners.contDiffOn_extendCoordChange`：contDiffOn_extendCoordCha
nge (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) : ContDiffOn
 𝕜 n (I.extendCoordChange e e') (I.…
· 使用定理 `IsManifold.subset_maximalAtlas`：subset_maximalAtlas [IsManifold I n M] :
 atlas H M subseteq maximalAtlas I n M
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `ModelWithCorners.extendCoordChange_source_mem_nhdsWithin`：extendCoordCha
nge_source_mem_nhdsWithin {x : E} (hx : x in (I.extendCoordChange e e').source) 
: (I.extendCoordChange e e').source in 𝓝[range…
· 使用定理 `ModelWithCorners.uniqueDiffOn`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
Auxiliary lemma for tangent spaces: the derivative of a coordinate change betwee
n two charts is
  `C^n` on its source.
-/
theorem contDiffOn_fderiv_coord_change [IsManifold I (n + 1) M]
    (i j : atlas H M) :
    ContDiffOn 𝕜 n (fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I))
      ((i.1.extend I).symm ≫ j.1.extend I).source := by
  have h : ((i.1.extend I).symm ≫ j.1.extend I).source ⊆ range I := by
    refine I.extendCoordChange_source.trans_subset ?_; apply image_subset_range
  intro x hx
  refine (ContDiffWithinAt.fderivWithin_right ?_ I.uniqueDiffOn le_rfl
    <| h hx).mono h
  refine (I.contDiffOn_extendCoordChange (subset_maximalAtlas i.2)
    (subset_maximalAtlas j.2) x hx).mono_of_mem_nhdsWithin ?_
  exact I.extendCoordChange_source_mem_nhdsWithin hx

open IsManifold

variable [IsManifold I 1 M] [IsManifold I' 1 M']

variable (I M) in
/-- Let `M` be a `C^1` manifold with model `I` on `(E, H)`.
Then `tangentBundleCore I M` is the vector bundle core for the tangent bundle over `M`.
It is indexed by the atlas of `M`, with fiber `E` and its change of coordinates from the chart `i`
to the chart `j` at point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`. -/
@[simps indexAt coordChange]
/-
**tangentBundleCore** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tangentBundleCore : VectorBundleCore 𝕜 M E (atlas H M) where baseSet i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce

--- 原说明 ---
Let `M` be a `C^1` manifold with model `I` on `(E, H)`.
Then `tangentBundleCore I M` is the vector bundle core for the tangent bundle ov
er `M`.
It is indexed by the atlas of `M`, with fiber `E` and its change of coordinates 
from the chart `i`
to the chart `j` at point `x : M` is the derivative of the composite
```
  I.symm   i.symm    j     I
E -----> H -----> M --> H --> E
```
within the set `range I ⊆ E` at `I (i x) : E`.
-/
def tangentBundleCore : VectorBundleCore 𝕜 M E (atlas H M) where
  baseSet i := i.1.source
  isOpen_baseSet i := i.1.open_source
  indexAt := achart H
  mem_baseSet_at := mem_chart_source H
  coordChange i j x :=
    fderivWithin 𝕜 (j.1.extend I ∘ (i.1.extend I).symm) (range I) (i.1.extend I x)
  coordChange_self i x hx v := by
    rw [Filter.EventuallyEq.fderivWithin_eq, fderivWithin_fun_id, ContinuousLinearMap.id_apply]
    · exact I.uniqueDiffWithinAt_image
    · filter_upwards [i.1.extend_target_mem_nhdsWithin hx] with y hy
      exact (i.1.extend I).right_inv hy
    · simp_rw [Function.comp_apply, i.1.extend_left_inv hx]
  continuousOn_coordChange i j := by
    have : IsManifold I (0 + 1) M := by simpa
    refine (contDiffOn_fderiv_coord_change (n := 0) i j).continuousOn.comp
      (i.1.continuousOn_extend.mono ?_) ?_
    · rw [i.1.extend_source]; exact inter_subset_left
    exact mapsTo_iff_image_subset.2 (i.1.extend_image_source_inter j.1).subset
  coordChange_comp := by
    have : IsManifold I (0 + 1) M := by simpa
    rintro i j k x ⟨⟨hxi, hxj⟩, hxk⟩ v
    rw [fderivWithin_fderivWithin, Filter.EventuallyEq.fderivWithin_eq]
    · have := i.1.extend_preimage_mem_nhds (I := I) hxi (j.1.extend_source_mem_nhds (I := I) hxj)
      filter_upwards [nhdsWithin_le_nhds this] with y hy
      simp_rw [Function.comp_apply, (j.1.extend I).left_inv hy]
    · simp_rw [Function.comp_apply, i.1.extend_left_inv hxi, j.1.extend_left_inv hxj]
    · exact (I.contDiffWithinAt_extendCoordChange' (subset_maximalAtlas j.2)
        (subset_maximalAtlas k.2) hxj hxk).differentiableWithinAt one_ne_zero
    · exact (I.contDiffWithinAt_extendCoordChange' (subset_maximalAtlas i.2)
        (subset_maximalAtlas j.2) hxi hxj).differentiableWithinAt one_ne_zero
    · intro x _; exact mem_range_self _
    · exact I.uniqueDiffWithinAt_image
    · rw [Function.comp_apply, i.1.extend_left_inv hxi]

/-- `simp`-normal form is `tangentBundleCore_localTriv_baseSet`. -/
/-
**tangentBundleCore_baseSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentBundleCore_baseSet (i) : (tangentBundleCore I M).baseSet i = i.1.so
urce
参数：i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`simp`-normal form is `tangentBundleCore_localTriv_baseSet`.
-/
theorem tangentBundleCore_baseSet (i) : (tangentBundleCore I M).baseSet i = i.1.source := rfl

@[simp]
/-
**tangentBundleCore_localTriv_baseSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentBundleCore_localTriv_baseSet (i) : ((tangentBundleCore I M).localTr
iv i).baseSet = i.1.source
参数：i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tangentBundleCore_localTriv_baseSet (i) :
    ((tangentBundleCore I M).localTriv i).baseSet = i.1.source := rfl
/-
**tangentBundleCore_coordChange_achart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentBundleCore_coordChange_achart (x x' z : M) : (tangentBundleCore I M
).coordChange (achart H x) (achart H x') z = fderivWithin 𝕜 (extChartAt I x' ∘ (
extChartAt I x).symm) (range I) (extChartAt I x z)
参数：x x' z : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tangentBundleCore_coordChange_achart (x x' z : M) :
    (tangentBundleCore I M).coordChange (achart H x) (achart H x') z =
      fderivWithin 𝕜 (extChartAt I x' ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) :=
  rfl

section tangentCoordChange

variable (I) in
/-- In a manifold `M`, given two preferred charts indexed by `x y : M`, `tangentCoordChange I x y`
is the family of derivatives of the corresponding change-of-coordinates map. It takes junk values
outside the intersection of the sources of the two charts.

Note that this definition takes advantage of the fact that `tangentBundleCore` has the same base
sets as the preferred charts of the base manifold. -/
/-
**tangentCoordChange** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：tangentCoordChange (x y : M) : M -> E ->L[𝕜] E
参数：x y : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a manifold `M`, given two preferred charts indexed by `x y : M`, `tangentCoor
dChange I x y`
is the family of derivatives of the corresponding change-of-coordinates map. It 
takes junk values
outside the intersection of the sources of the two charts.

Note that this definition takes advantage of the fact that `tangentBundleCore` h
as the same base
sets as the preferred charts of the base manifold.
-/
abbrev tangentCoordChange (x y : M) : M → E →L[𝕜] E :=
  (tangentBundleCore I M).coordChange (achart H x) (achart H y)
/-
**tangentCoordChange_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tangentCoordChange_def {x y z : M} : tangentCoordChange I x y z = fderivWi
thin 𝕜 (extChartAt I y ∘ (extChartAt I x).symm) (range I) (extChartAt I x z)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tangentCoordChange_def {x y z : M} : tangentCoordChange I x y z =
    fderivWithin 𝕜 (extChartAt I y ∘ (extChartAt I x).symm) (range I) (extChartAt I x z) := rfl
/-
**tangentCoordChange_self** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tangentCoordChange_self {x z : M} {v : E} (h : z in (extChartAt I x).sourc
e) : tangentCoordChange I x x z v = v
参数：h : z in (extChartAt I x).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.coordChange_self`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [
inst_2 : NormedSpace R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tangentBundleCore_baseSet`：tangentBundleCore_baseSet (i) : (tangentBundl
eCore I M).baseSet i = i.1.source
· 使用定理 `coe_achart`：coe_achart (x : M) : (achart H x : OpenPartialHomeomorph M H
) = chartAt H x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
lemma tangentCoordChange_self {x z : M} {v : E} (h : z ∈ (extChartAt I x).source) :
    tangentCoordChange I x x z v = v := by
  apply (tangentBundleCore I M).coordChange_self
  rw [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h
/-
**tangentCoordChange_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tangentCoordChange_comp {w x y z : M} {v : E} (h : z in (extChartAt I w).s
ource inter (extChartAt I x).source inter (extChartAt I y).source) : tangentCoor
dChange I x y z (tangentCoordChange I w x z v) = tangentCoordChange I w y z v
参数：h : z in (extChartAt I w).source inter (extChartAt I x).source inter (extChar
tAt I y).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.coordChange_comp`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [
inst_2 : NormedSpace R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
lemma tangentCoordChange_comp {w x y z : M} {v : E}
    (h : z ∈ (extChartAt I w).source ∩ (extChartAt I x).source ∩ (extChartAt I y).source) :
    tangentCoordChange I x y z (tangentCoordChange I w x z v) = tangentCoordChange I w y z v := by
  apply (tangentBundleCore I M).coordChange_comp
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]
  exact h
/-
**hasFDerivWithinAt_tangentCoordChange** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasFDerivWithinAt_tangentCoordChange {x y z : M} (h : z in (extChartAt I x
).source inter (extChartAt I y).source) : HasFDerivWithinAt ((extChartAt I y) ∘ 
(extChartAt I x).symm) (tangentCoordChange I x y z) (range I) (extChartAt I x z)
参数：h : z in (extChartAt I x).source inter (extChartAt I y).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.trans_source''`：trans_source'' : (e.trans e').source = e.sy
mm '' (e.target inter e'.source)
· 使用定理 `PartialEquiv.symm_symm`：symm_symm : e.symm.symm = e
· 使用定理 `PartialEquiv.symm_target`：symm_target : e.symm.target = e.source
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `DifferentiableWithinAt.hasFDerivWithinAt`：DifferentiableWithinAt.hasFDer
ivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasFDerivWithinAt f (fderivWit
hin 𝕜 f s x) s x
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `contDiffWithinAt_ext_coord_change`：contDiffWithinAt_ext_coord_change [Is
Manifold I n M] (x x' : M) {y : E} (hy : y in ((extChartAt I x').symm ≫ extChart
At I x).source) : ContD…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma hasFDerivWithinAt_tangentCoordChange {x y z : M}
    (h : z ∈ (extChartAt I x).source ∩ (extChartAt I y).source) :
    HasFDerivWithinAt ((extChartAt I y) ∘ (extChartAt I x).symm) (tangentCoordChange I x y z)
      (range I) (extChartAt I x z) :=
  have h' : extChartAt I x z ∈ ((extChartAt I x).symm ≫ (extChartAt I y)).source := by
    rw [PartialEquiv.trans_source'', PartialEquiv.symm_symm, PartialEquiv.symm_target]
    exact mem_image_of_mem _ h
  ((contDiffWithinAt_ext_coord_change y x h').differentiableWithinAt one_ne_zero).hasFDerivWithinAt
/-
**continuousOn_tangentCoordChange** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：continuousOn_tangentCoordChange (x y : M) : ContinuousOn (tangentCoordChan
ge I x y) ((extChartAt I x).source inter (extChartAt I y).source)
参数：x y : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `VectorBundleCore.continuousOn_coordChange`：∀ {R : Type u_1} {B : Type u_
2} {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGrou
p F]   [inst_2 : NormedSpace R …
-/
lemma continuousOn_tangentCoordChange (x y : M) : ContinuousOn (tangentCoordChange I x y)
    ((extChartAt I x).source ∩ (extChartAt I y).source) := by
  convert! (tangentBundleCore I M).continuousOn_coordChange (achart H x) (achart H y) <;>
  simp only [tangentBundleCore_baseSet, coe_achart, ← extChartAt_source I]

end tangentCoordChange

local notation "TM" => TangentBundle I M

section TangentBundleInstances

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace TM :=
  inferInstanceAs <| TopologicalSpace (tangentBundleCore I M).TotalSpace
/-
**TangentSpace.fiberBundle** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：TangentSpace.fiberBundle : FiberBundle E (TangentSpace I : M -> Type _)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance TangentSpace.fiberBundle : FiberBundle E (TangentSpace I : M → Type _) :=
  inferInstanceAs <| FiberBundle E (tangentBundleCore I M).Fiber
/-
**TangentSpace.vectorBundle** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：TangentSpace.vectorBundle : VectorBundle 𝕜 E (TangentSpace I : M -> Type _
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance TangentSpace.vectorBundle : VectorBundle 𝕜 E (TangentSpace I : M → Type _) :=
  inferInstanceAs <| VectorBundle 𝕜 E (tangentBundleCore I M).Fiber

namespace TangentBundle

/-
**TangentBundle.chartAt** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_4} [inst_3 : T
opologicalSpace H] {I : ModelWithCorners 𝕜 E H} {M : Type u_6}   [inst_4 : Topol
ogicalSpace M] [inst_5 : ChartedSpace H M] [inst_6 : IsManifold I 1 M] (p : Tang
entBundle I M),   chartAt (ModelProd H E) p =     ((tangentBundleCore I M).toFib
erBundleCore.localTriv (achart H p.proj)).trans       ((chartAt H p.proj).prod (
OpenPartialHomeomorph.refl E))
参数：p : TangentBundle I M；ModelProd H E；(tangentBundleCore I M).toFiberBundleCore
.localTriv (achart H p.proj)；(chartAt H p.proj).prod (OpenPartialHomeomorph.refl
 E)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem chartAt (p : TM) :
    chartAt (ModelProd H E) p =
      ((tangentBundleCore I M).toFiberBundleCore.localTriv
        (achart H p.1)).toOpenPartialHomeomorph ≫ₕ
        (chartAt H p.1).prod (OpenPartialHomeomorph.refl E) :=
  rfl
/-
**TangentBundle.chartAt_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle`
。
形式化陈述：chartAt_toPartialEquiv (p : TM) : (chartAt (ModelProd H E) p).toPartialEqu
iv = (tangentBundleCore I M).toFiberBundleCore.localTrivAsPartialEquiv (achart H
 p.1) ≫ (chartAt H p.1).toPartialEquiv.prod (PartialEquiv.refl E)
参数：p : TM。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem chartAt_toPartialEquiv (p : TM) :
    (chartAt (ModelProd H E) p).toPartialEquiv =
      (tangentBundleCore I M).toFiberBundleCore.localTrivAsPartialEquiv (achart H p.1) ≫
        (chartAt H p.1).toPartialEquiv.prod (PartialEquiv.refl E) :=
  rfl
/-
**TangentBundle.trivializationAt_eq_localTriv** 是 Mathlib 中的一个定理，位于命名空间 `Tangent
Bundle`。
形式化陈述：trivializationAt_eq_localTriv (x : M) : trivializationAt E (TangentSpace I
) x = (tangentBundleCore I M).toFiberBundleCore.localTriv (achart H x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trivializationAt_eq_localTriv (x : M) :
    trivializationAt E (TangentSpace I) x =
      (tangentBundleCore I M).toFiberBundleCore.localTriv (achart H x) :=
  rfl

@[simp, mfld_simps]
/-
**TangentBundle.trivializationAt_source** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle
`。
形式化陈述：trivializationAt_source (x : M) : (trivializationAt E (TangentSpace I) x).
source = π E (TangentSpace I) ⁻¹' (chartAt H x).source
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trivializationAt_source (x : M) :
    (trivializationAt E (TangentSpace I) x).source =
      π E (TangentSpace I) ⁻¹' (chartAt H x).source :=
  rfl

@[simp, mfld_simps]
/-
**TangentBundle.trivializationAt_target** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle
`。
形式化陈述：trivializationAt_target (x : M) : (trivializationAt E (TangentSpace I) x).
target = (chartAt H x).source ×ˢ univ
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trivializationAt_target (x : M) :
    (trivializationAt E (TangentSpace I) x).target = (chartAt H x).source ×ˢ univ :=
  rfl

@[simp, mfld_simps]
/-
**TangentBundle.trivializationAt_baseSet** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundl
e`。
形式化陈述：trivializationAt_baseSet (x : M) : (trivializationAt E (TangentSpace I) x)
.baseSet = (chartAt H x).source
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trivializationAt_baseSet (x : M) :
    (trivializationAt E (TangentSpace I) x).baseSet = (chartAt H x).source :=
  rfl
/-
**TangentBundle.trivializationAt_apply** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle`
。
形式化陈述：trivializationAt_apply (x : M) (z : TM) : trivializationAt E (TangentSpace
 I) x z = (z.1, fderivWithin 𝕜 ((chartAt H x).extend I ∘ ((chartAt H z.1).extend
 I).symm) (range I) ((chartAt H z.1).extend I z.1) z.2)
参数：x : M；z : TM。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trivializationAt_apply (x : M) (z : TM) :
    trivializationAt E (TangentSpace I) x z =
      (z.1, fderivWithin 𝕜 ((chartAt H x).extend I ∘ ((chartAt H z.1).extend I).symm) (range I)
        ((chartAt H z.1).extend I z.1) z.2) :=
  rfl

@[simp, mfld_simps]
/-
**TangentBundle.trivializationAt_fst** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle`。
形式化陈述：trivializationAt_fst (x : M) (z : TM) : (trivializationAt E (TangentSpace 
I) x z).1 = z.1
参数：x : M；z : TM。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trivializationAt_fst (x : M) (z : TM) : (trivializationAt E (TangentSpace I) x z).1 = z.1 :=
  rfl

@[simp, mfld_simps]
/-
**TangentBundle.mem_chart_source_iff** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle`。
形式化陈述：mem_chart_source_iff (p q : TM) : p in (chartAt (ModelProd H E) q).source 
↔ p.1 in (chartAt H q.1).source
参数：p q : TM。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundle.chartedSpace_chartAt`：FiberBundle.chartedSpace_chartAt (x : 
TotalSpace F E) : chartAt (ModelProd HB F) x = (trivializationAt F E x.proj).toO
penPartialHomeomorph ≫…
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_chart_source_iff (p q : TM) :
    p ∈ (chartAt (ModelProd H E) q).source ↔ p.1 ∈ (chartAt H q.1).source := by
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
/-
**TangentBundle.mem_chart_target_iff** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle`。
形式化陈述：mem_chart_target_iff (p : H × E) (q : TM) : p in (chartAt (ModelProd H E) 
q).target ↔ p.1 in (chartAt H q.1).target
参数：p : H × E；q : TM。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FiberBundle.chartedSpace_chartAt`：FiberBundle.chartedSpace_chartAt (x : 
TotalSpace F E) : chartAt (ModelProd HB F) x = (trivializationAt F E x.proj).toO
penPartialHomeomorph ≫…
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `PartialEquiv.prod_symm`：prod_symm (e : PartialEquiv α β) (e' : PartialEq
uiv γ δ) : (e.prod e').symm = e.symm.prod e'.symm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
theorem mem_chart_target_iff (p : H × E) (q : TM) :
    p ∈ (chartAt (ModelProd H E) q).target ↔ p.1 ∈ (chartAt H q.1).target := by
  /- porting note: was
  simp +contextual only [FiberBundle.chartedSpace_chartAt,
    and_iff_left_iff_imp, mfld_simps]
  -/
  simp only [FiberBundle.chartedSpace_chartAt, mfld_simps]
  rw [PartialEquiv.prod_symm]
  simp +contextual only [and_iff_left_iff_imp, mfld_simps]

@[simp, mfld_simps]
/-
**TangentBundle.coe_chartAt_fst** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle`。
形式化陈述：coe_chartAt_fst (p q : TM) : ((chartAt (ModelProd H E) q) p).1 = chartAt H
 q.1 p.1
参数：p q : TM。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_chartAt_fst (p q : TM) : ((chartAt (ModelProd H E) q) p).1 = chartAt H q.1 p.1 :=
  rfl

@[simp, mfld_simps]
/-
**TangentBundle.coe_chartAt_symm_fst** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle`。
形式化陈述：coe_chartAt_symm_fst (p : H × E) (q : TM) : ((chartAt (ModelProd H E) q).s
ymm p).1 = ((chartAt H q.1).symm : H -> M) p.1
参数：p : H × E；q : TM。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_chartAt_symm_fst (p : H × E) (q : TM) :
    ((chartAt (ModelProd H E) q).symm p).1 = ((chartAt H q.1).symm : H → M) p.1 :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The trivialization of the tangent space can be expressed in terms of the tangent bundle core.
To write it as the manifold derivative of `extChartAt`, see
`TangentBundle.continuousLinearMapAt_trivializationAt`.

Use with care as it abuses the defeq `TangentSpace I b = E`. -/
/-
**TangentBundle.continuousLinearMapAt_trivializationAt_eq_core** 是 Mathlib 中的一个定
理，位于命名空间 `TangentBundle`。
形式化陈述：continuousLinearMapAt_trivializationAt_eq_core {b₀ b : M} (hb : b in (char
tAt H b₀).source) : (trivializationAt E (TangentSpace I) b₀).continuousLinearMap
At 𝕜 b = (tangentBundleCore I M).coordChange (achart H b) (achart H b₀) b
参数：hb : b in (chartAt H b₀).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorBundleCore.vectorBundle`：∀ {R : Type u_1} {B : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [inst
_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.trivializationAt_continuousLinearMapAt`：∀ {R : Type u_1
} {B : Type u_2} {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : Nor
medAddCommGroup F]   [inst_2 : NormedSpace R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tangentBundleCore_indexAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `tangentBundleCore_coordChange`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The trivialization of the tangent space can be expressed in terms of the tangent
 bundle core.
To write it as the manifold derivative of `extChartAt`, see
`TangentBundle.continuousLinearMapAt_trivializationAt`.

Use with care as it abuses the defeq `TangentSpace I b = E`.
-/
theorem continuousLinearMapAt_trivializationAt_eq_core {b₀ b : M} (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).continuousLinearMapAt 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b) (achart H b₀) b := by
  simp [hb]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse trivialization of the tangent space can be expressed in terms of the tangent bundle
core. To write it as the manifold derivative of `(extChartAt I b₀).symm`, see
`TangentBundle.symmL_trivializationAt`.

Use with care as it abuses the defeq `TangentSpace I b = E`. -/
/-
**TangentBundle.symmL_trivializationAt_eq_core** 是 Mathlib 中的一个定理，位于命名空间 `Tangen
tBundle`。
形式化陈述：symmL_trivializationAt_eq_core {b₀ b : M} (hb : b in (chartAt H b₀).source
) : (trivializationAt E (TangentSpace I) b₀).symmL 𝕜 b = (tangentBundleCore I M)
.coordChange (achart H b₀) (achart H b) b
参数：hb : b in (chartAt H b₀).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorBundleCore.vectorBundle`：∀ {R : Type u_1} {B : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [inst
_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.trivializationAt_symmL`：∀ {R : Type u_1} {B : Type u_2}
 {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup 
F]   [inst_2 : NormedSpace R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tangentBundleCore_indexAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `tangentBundleCore_coordChange`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The inverse trivialization of the tangent space can be expressed in terms of the
 tangent bundle
core. To write it as the manifold derivative of `(extChartAt I b₀).symm`, see
`TangentBundle.symmL_trivializationAt`.

Use with care as it abuses the defeq `TangentSpace I b = E`.
-/
theorem symmL_trivializationAt_eq_core {b₀ b : M} (hb : b ∈ (chartAt H b₀).source) :
    (trivializationAt E (TangentSpace I) b₀).symmL 𝕜 b =
      (tangentBundleCore I M).coordChange (achart H b₀) (achart H b) b := by
  simp [hb]

/-! The lemmas below have high priority because `simp` simplifies the LHS to `.id _ _`;
we prefer `1` as the simp-normal form. -/
@[simp high, mfld_simps]
/-
**TangentBundle.coordChange_model_space** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle
`。
形式化陈述：coordChange_model_space (b b' x : F) : (tangentBundleCore 𝓘(𝕜, F) F).coord
Change (achart F b) (achart F b') x = 1
参数：b b' x : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `tangentBundleCore_coordChange`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `fderivWithin_id`：fderivWithin_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] 
[T2Space E] (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = .id 𝕜 E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `uniqueDiffWithinAt_univ`：uniqueDiffWithinAt_univ : UniqueDiffWithinAt 𝕜 
univ x
· 使用定理 `NormedField.nhdsNE_neBot`：nhdsNE_neBot (x : α) : NeBot (𝓝[!=] x)

--- 原说明 ---
The lemmas below have high priority because `simp` simplifies the LHS to `.id _ 
_`;
we prefer `1` as the simp-normal form.
-/
theorem coordChange_model_space (b b' x : F) :
    (tangentBundleCore 𝓘(𝕜, F) F).coordChange (achart F b) (achart F b') x = 1 := by
  simpa only [tangentBundleCore_coordChange, mfld_simps] using!
    fderivWithin_id uniqueDiffWithinAt_univ

@[simp high, mfld_simps]
/-
**TangentBundle.symmL_model_space** 是 Mathlib 中的一个定理，位于命名空间 `TangentBundle`。
形式化陈述：symmL_model_space (b b' : F) : (trivializationAt F (TangentSpace 𝓘(𝕜, F)) 
b).symmL 𝕜 b' = (1 : F ->L[𝕜] F)
参数：b b' : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TangentBundle.symmL_trivializationAt_eq_core`：symmL_trivializationAt_eq_
core {b₀ b : M} (hb : b in (chartAt H b₀).source) : (trivializationAt E (Tangent
Space I) b₀).symmL 𝕜 b = (tangentB…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `TangentBundle.coordChange_model_space`：coordChange_model_space (b b' x :
 F) : (tangentBundleCore 𝓘(𝕜, F) F).coordChange (achart F b) (achart F b') x = 1
-/
theorem symmL_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).symmL 𝕜 b' = (1 : F →L[𝕜] F) := by
  rw [TangentBundle.symmL_trivializationAt_eq_core, coordChange_model_space]
  apply mem_univ

@[simp high, mfld_simps]
/-
**TangentBundle.continuousLinearMapAt_model_space** 是 Mathlib 中的一个定理，位于命名空间 `Tan
gentBundle`。
形式化陈述：continuousLinearMapAt_model_space (b b' : F) : (trivializationAt F (Tangen
tSpace 𝓘(𝕜, F)) b).continuousLinearMapAt 𝕜 b' = (1 : F ->L[𝕜] F)
参数：b b' : F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `trivialization_linear`：∀ (R : Type u_1) {B : Type u_2} {F : Type u_3} {E
 : B → Type u_4} [inst : NontriviallyNormedField R]   [inst_1 : (x : B) → AddCom
mMonoid (E …
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TangentBundle.continuousLinearMapAt_trivializationAt_eq_core`：continuous
LinearMapAt_trivializationAt_eq_core {b₀ b : M} (hb : b in (chartAt H b₀).source
) : (trivializationAt E (TangentSpace I) b₀).conti…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `TangentBundle.coordChange_model_space`：coordChange_model_space (b b' x :
 F) : (tangentBundleCore 𝓘(𝕜, F) F).coordChange (achart F b) (achart F b') x = 1
-/
theorem continuousLinearMapAt_model_space (b b' : F) :
    (trivializationAt F (TangentSpace 𝓘(𝕜, F)) b).continuousLinearMapAt 𝕜 b' = (1 : F →L[𝕜] F) := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core, coordChange_model_space]
  apply mem_univ

end TangentBundle

omit [IsManifold I 1 M] in
/-
**tangentBundleCore.isContMDiff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tangentBundleCore.isContMDiff [h : IsManifold I (n + 1) M] : haveI : IsMan
ifold I 1 M
参数：n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsManifold.of_le`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `contMDiffOn_iff_source_of_mem_maximalAtlas`：contMDiffOn_iff_source_of_me
m_maximalAtlas (he : e in maximalAtlas I n M) (hs : s subseteq e.source) : ContM
DiffOn I I' n f s ↔ ContMDiffOn …
· 使用定理 `IsManifold.subset_maximalAtlas`：subset_maximalAtlas [IsManifold I n M] :
 atlas H M subseteq maximalAtlas I n M
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `contMDiffOn_iff_contDiffOn`：contMDiffOn_iff_contDiffOn {f : E -> E'} {s 
: Set E} : ContMDiffOn 𝓘(𝕜, E) 𝓘(𝕜, E') n f s ↔ ContDiffOn 𝕜 n f s
· 使用定理 `ContDiffOn.mono`：ContDiffOn.mono (h : ContDiffOn 𝕜 n f s) {t : Set E} (h
st : t subseteq s) : ContDiffOn 𝕜 n f t
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用定理 `contDiffOn_fderiv_coord_change`：contDiffOn_fderiv_coord_change [IsManifo
ld I (n + 1) M] (i j : atlas H M) : ContDiffOn 𝕜 n (fderivWithin 𝕜 (j.1.extend I
 ∘ (i.1.extend I).sy…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tangentBundleCore_coordChange`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PartialEquiv.trans_source'`：trans_source' : (e.trans e').source = e.sour
ce inter e ⁻¹' (e.target inter e'.source)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `OpenPartialHomeomorph.extend_image_source_inter`：∀ {𝕜 : Type u_1} {E : T
ype u_2} {M : Type u_3} {H : Type u_4} [inst : NontriviallyNormedField 𝕜]   [ins
t_1 : NormedAddCommGroup E] [inst_2 :…
-/
lemma tangentBundleCore.isContMDiff [h : IsManifold I (n + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    (tangentBundleCore I M).IsContMDiff I n := by
  have : IsManifold I n M := .of_le (n := n + 1) (le_self_add)
  refine ⟨fun i j => ?_⟩
  rw [contMDiffOn_iff_source_of_mem_maximalAtlas (subset_maximalAtlas i.2),
    contMDiffOn_iff_contDiffOn]
  · refine ((contDiffOn_fderiv_coord_change (I := I) i j).congr fun x hx => ?_).mono ?_
    · rw [PartialEquiv.trans_source'] at hx
      simp_rw [Function.comp_apply, tangentBundleCore_coordChange, (i.1.extend I).right_inv hx.1]
    · exact (i.1.extend_image_source_inter j.1).subset
  · apply inter_subset_left

omit [IsManifold I 1 M] in
/-
**TangentBundle.contMDiffVectorBundle** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TangentBundle.contMDiffVectorBundle [h : IsManifold I (n + 1) M] : haveI :
 IsManifold I 1 M
参数：n + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsManifold.of_le`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `WithTop.canonicallyOrderedAdd`：∀ {α : Type u} [inst : Add α] [inst_1 : P
reorder α] [CanonicallyOrderedAdd α], CanonicallyOrderedAdd (WithTop α)
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用引理 `tangentBundleCore.isContMDiff`：tangentBundleCore.isContMDiff [h : IsMani
fold I (n + 1) M] : haveI : IsManifold I 1 M
-/
lemma TangentBundle.contMDiffVectorBundle [h : IsManifold I (n + 1) M] :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : (tangentBundleCore I M).IsContMDiff I n := tangentBundleCore.isContMDiff
  exact (tangentBundleCore I M).instContMDiffVectorBundle

omit [IsManifold I 1 M] in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : IsManifold I ∞ M] :
    ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I := by
  have : IsManifold I (∞ + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsManifold I ω M] :
    ContMDiffVectorBundle ω E (TangentSpace I : M → Type _) I :=
  TangentBundle.contMDiffVectorBundle

omit [IsManifold I 1 M] in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : IsManifold I 2 M] :
    ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I := by
  have : IsManifold I (1 + 1) M := h
  exact TangentBundle.contMDiffVectorBundle

end TangentBundleInstances

/-! ## The tangent bundle to the model space -/

set_option backward.isDefEq.respectTransparency false in
@[simp, mfld_simps]
/-
**trivializationAt_model_space_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：trivializationAt_model_space_apply (p : TangentBundle I H) (x : H) : trivi
alizationAt E (TangentSpace I) x p = (p.1, p.2)
参数：p : TangentBundle I H；x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `fderivWithin_congr'`：fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x in s
) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `fderivWithin_id`：fderivWithin_id [ContinuousAdd E] [ContinuousSMul 𝕜 E] 
[T2Space E] (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = .id 𝕜 E
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ModelWithCorners.uniqueDiffWithinAt_image`：uniqueDiffWithinAt_image {x :
 H} : UniqueDiffWithinAt 𝕜 (range I) (I x)

--- 原说明 ---
## The tangent bundle to the model space
-/
theorem trivializationAt_model_space_apply (p : TangentBundle I H) (x : H) :
    trivializationAt E (TangentSpace I) x p = (p.1, p.2) := by
  simp only [TangentBundle.trivializationAt_apply]
  have : fderivWithin 𝕜 (↑I ∘ ↑I.symm) (range I) (I p.proj) =
      fderivWithin 𝕜 id (range I) (I p.proj) :=
    fderivWithin_congr' (fun y hy ↦ by simp [hy]) (mem_range_self p.proj)
  simp [this, fderivWithin_id (ModelWithCorners.uniqueDiffWithinAt_image I)]

set_option backward.isDefEq.respectTransparency false in
/-- In the tangent bundle to the model space, the charts are just the canonical identification
between a product type and a sigma type, a.k.a. `TotalSpace.toProd`. -/
@[simp, mfld_simps]
/-
**tangentBundle_model_space_chartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentBundle_model_space_chartAt (p : TangentBundle I H) : (chartAt (Mode
lProd H E) p).toPartialEquiv = (TotalSpace.toProd H E).toPartialEquiv
参数：p : TangentBundle I H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
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
· 使用定理 `ModelProd.ext`：ModelProd.ext {x y : ModelProd H H'} (h₁ : x.1 = y.1) (h₂
 : x.2 = y.2) : x = y
· 使用定理 `VectorBundleCore.coordChange_self`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [
inst_2 : NormedSpace R …
· 使用定理 `mem_achart_source`：mem_achart_source (x : M) : x in (achart H x).1.sourc
e
· 使用定理 `Bundle.TotalSpace.ext`：∀ {B : Type u_1} {F : Type u_4} {E : B → Type u_5
} {x y : Bundle.TotalSpace F E},   x.proj = y.proj → x.snd ≍ y.snd → x = y
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `FiberBundleCore.open_source'`：open_source' (i : ι) : IsOpen (Z.localTriv
AsPartialEquiv i).source
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `VectorBundleCore.toFiberBundleCore_baseSet`：∀ {R : Type u_1} {B : Type u
_2} {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGro
up F]   [inst_2 : NormedSpace R …
· 使用定理 `PartialEquiv.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} (toFun toFun
_1 : α → β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : 
invFun = invFun_…
· 使用定理 `PartialHomeomorph.mk.congr_simp`：∀ {X : Type u_7} {Y : Type u_8} [inst :
 TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (toPartialEquiv toPartialEq
uiv_1 : PartialEquiv …
· 使用定理 `OpenPartialHomeomorph.mk.congr_simp`：∀ {X : Type u_7} {Y : Type u_8} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (toPartialHomeomorph to
PartialHomeomorph_1 : Par…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `VectorBundleCore.toFiberBundleCore_indexAt`：∀ {R : Type u_1} {B : Type u
_2} {F : Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGro
up F]   [inst_2 : NormedSpace R …
· 使用定理 `PartialEquiv.refl_prod_refl`：refl_prod_refl : (PartialEquiv.refl α).prod
 (PartialEquiv.refl β) = PartialEquiv.refl (α × β)
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `Equiv.toPartialEquiv_source`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β)
, e.toPartialEquiv.source = Set.univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the tangent bundle to the model space, the charts are just the canonical iden
tification
between a product type and a sigma type, a.k.a. `TotalSpace.toProd`.
-/
theorem tangentBundle_model_space_chartAt (p : TangentBundle I H) :
    (chartAt (ModelProd H E) p).toPartialEquiv = (TotalSpace.toProd H E).toPartialEquiv := by
  ext x : 1
  · ext; · rfl
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  · ext; · rfl
    apply heq_of_eq
    exact (tangentBundleCore I H).coordChange_self (achart _ x.1) x.1 (mem_achart_source H x.1) x.2
  simp_rw [TangentBundle.chartAt, FiberBundleCore.localTriv,
    FiberBundleCore.localTrivAsPartialEquiv, VectorBundleCore.toFiberBundleCore_baseSet,
    tangentBundleCore_baseSet]
  simp only [mfld_simps]

@[simp, mfld_simps]
/-
**tangentBundle_model_space_coe_chartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentBundle_model_space_coe_chartAt (p : TangentBundle I H) : ⇑(chartAt 
(ModelProd H E) p) = TotalSpace.toProd H E
参数：p : TangentBundle I H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.coe_toPartialEquiv`：coe_toPartialEquiv : (e.toPart
ialEquiv : X -> Y) = e
· 使用定理 `tangentBundle_model_space_chartAt`：tangentBundle_model_space_chartAt (p 
: TangentBundle I H) : (chartAt (ModelProd H E) p).toPartialEquiv = (TotalSpace.
toProd H E).toPartialEq…
-/
theorem tangentBundle_model_space_coe_chartAt (p : TangentBundle I H) :
    ⇑(chartAt (ModelProd H E) p) = TotalSpace.toProd H E := by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv, tangentBundle_model_space_chartAt]; rfl

@[simp, mfld_simps]
/-
**tangentBundle_model_space_coe_chartAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentBundle_model_space_coe_chartAt_symm (p : TangentBundle I H) : ((cha
rtAt (ModelProd H E) p).symm : ModelProd H E -> TangentBundle I H) = (TotalSpace
.toProd H E).symm
参数：p : TangentBundle I H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.coe_toPartialEquiv`：coe_toPartialEquiv : (e.toPart
ialEquiv : X -> Y) = e
· 使用定理 `OpenPartialHomeomorph.symm_toPartialEquiv`：symm_toPartialEquiv : e.symm.
toPartialEquiv = e.toPartialEquiv.symm
· 使用定理 `tangentBundle_model_space_chartAt`：tangentBundle_model_space_chartAt (p 
: TangentBundle I H) : (chartAt (ModelProd H E) p).toPartialEquiv = (TotalSpace.
toProd H E).toPartialEq…
-/
theorem tangentBundle_model_space_coe_chartAt_symm (p : TangentBundle I H) :
    ((chartAt (ModelProd H E) p).symm : ModelProd H E → TangentBundle I H) =
      (TotalSpace.toProd H E).symm := by
  rw [← OpenPartialHomeomorph.coe_toPartialEquiv, OpenPartialHomeomorph.symm_toPartialEquiv,
    tangentBundle_model_space_chartAt]; rfl
/-
**tangentBundleCore_coordChange_model_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentBundleCore_coordChange_model_space (x x' z : H) : (tangentBundleCor
e I H).coordChange (achart H x) (achart H x') z = ContinuousLinearMap.id 𝕜 E
参数：x x' z : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
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
· 使用定理 `VectorBundleCore.coordChange_self`：∀ {R : Type u_1} {B : Type u_2} {F : 
Type u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [
inst_2 : NormedSpace R …
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem tangentBundleCore_coordChange_model_space (x x' z : H) :
    (tangentBundleCore I H).coordChange (achart H x) (achart H x') z =
    ContinuousLinearMap.id 𝕜 E := by
  ext v; exact (tangentBundleCore I H).coordChange_self (achart _ z) z (mem_univ _) v

set_option backward.isDefEq.respectTransparency false in
variable (I) in
/-- The canonical identification between the tangent bundle to the model space and the product,
as a homeomorphism. For the diffeomorphism version, see `tangentBundleModelSpaceDiffeomorph`. -/
/-
**tangentBundleModelSpaceHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical identification between the tangent bundle to the model space and t
he product,
as a homeomorphism. For the diffeomorphism version, see `tangentBundleModelSpace
Diffeomorph`.
-/
def tangentBundleModelSpaceHomeomorph : TangentBundle I H ≃ₜ ModelProd H E :=
  { TotalSpace.toProd H E with
    continuous_toFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p) := by
        rw [← continuousOn_univ]
        convert! (chartAt (ModelProd H E) p).continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this
    continuous_invFun := by
      let p : TangentBundle I H := ⟨I.symm (0 : E), (0 : E)⟩
      have : Continuous (chartAt (ModelProd H E) p).symm := by
        rw [← continuousOn_univ]
        convert! (chartAt (ModelProd H E) p).symm.continuousOn
        simp only [mfld_simps]
      simpa only [mfld_simps] using this }

@[simp, mfld_simps]
/-
**tangentBundleModelSpaceHomeomorph_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentBundleModelSpaceHomeomorph_coe : (tangentBundleModelSpaceHomeomorph
 I : TangentBundle I H -> ModelProd H E) = TotalSpace.toProd H E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem tangentBundleModelSpaceHomeomorph_coe :
    (tangentBundleModelSpaceHomeomorph I : TangentBundle I H → ModelProd H E) =
      TotalSpace.toProd H E :=
  rfl

@[simp, mfld_simps]
/-
**tangentBundleModelSpaceHomeomorph_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentBundleModelSpaceHomeomorph_coe_symm : ((tangentBundleModelSpaceHome
omorph I).symm : ModelProd H E -> TangentBundle I H) = (TotalSpace.toProd H E).s
ymm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem tangentBundleModelSpaceHomeomorph_coe_symm :
    ((tangentBundleModelSpaceHomeomorph I).symm : ModelProd H E → TangentBundle I H) =
      (TotalSpace.toProd H E).symm :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**contMDiff_tangentBundleModelSpaceHomeomorph** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_tangentBundleModelSpaceHomeomorph : ContMDiff I.tangent (I.prod 
𝓘(𝕜, E)) n (tangentBundleModelSpaceHomeomorph I : TangentBundle I H -> ModelProd
 H E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
· 使用定理 `contMDiff_iff`：contMDiff_iff [IsManifold I n M] [IsManifold I' n M'] : C
ontMDiff I I' n f ↔ Continuous f ∧ forall (x : M) (y : M'), ContDiffOn 𝕜 n (extC
har…
· 使用定理 `instContMDiffVectorBundleOfTopWithTopENat`：∀ {𝕜 : Type u_1} {B : Type u_
2} (F : Type u_4) (E : B → Type u_6) [inst : NontriviallyNormedField 𝕜] {EB : Ty
pe u_7}   [inst_1 : NormedAddCo…
· 使用定理 `instContMDiffVectorBundleTopWithTopENatTangentSpaceOfIsManifold`：∀ {𝕜 : 
Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddC
ommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用定理 `contDiffOn_id`：contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `tangentBundle_model_space_chartAt`：tangentBundle_model_space_chartAt (p 
: TangentBundle I H) : (chartAt (ModelProd H E) p).toPartialEquiv = (TotalSpace.
toProd H E).toPartialEq…
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `Equiv.toPartialEquiv_target`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β)
, e.toPartialEquiv.target = Set.univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Equiv.toPartialEquiv_symm_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α 
≃ β), ↑e.toPartialEquiv.symm = ⇑e.symm
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `PartialEquiv.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} (toFun toFun
_1 : α → β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : 
invFun = invFun_…
（共 33 条，此处仅展示前 30 条）
-/
theorem contMDiff_tangentBundleModelSpaceHomeomorph :
    ContMDiff I.tangent (I.prod 𝓘(𝕜, E)) n
    (tangentBundleModelSpaceHomeomorph I : TangentBundle I H → ModelProd H E) := by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y ↦ ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, TotalSpace.toProd, Equiv.coe_fn_symm_mk, forall_exists_index,
    Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simp [PartialEquiv.prod]

set_option backward.isDefEq.respectTransparency false in
/-
**contMDiff_tangentBundleModelSpaceHomeomorph_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contMDiff_tangentBundleModelSpaceHomeomorph_symm : ContMDiff I.tangent I.t
angent n ((tangentBundleModelSpaceHomeomorph I).symm : ModelProd H E -> TangentB
undle I H)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
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
· 使用定理 `contMDiff_iff`：contMDiff_iff [IsManifold I n M] [IsManifold I' n M'] : C
ontMDiff I I' n f ↔ Continuous f ∧ forall (x : M) (y : M'), ContDiffOn 𝕜 n (extC
har…
· 使用定理 `instContMDiffVectorBundleOfTopWithTopENat`：∀ {𝕜 : Type u_1} {B : Type u_
2} (F : Type u_4) (E : B → Type u_6) [inst : NontriviallyNormedField 𝕜] {EB : Ty
pe u_7}   [inst_1 : NormedAddCo…
· 使用定理 `instContMDiffVectorBundleTopWithTopENatTangentSpaceOfIsManifold`：∀ {𝕜 : 
Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddC
ommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Type u_…
· 使用定理 `Homeomorph.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y), Continuous ⇑h
· 使用定理 `ContDiffOn.congr`：ContDiffOn.congr (h : ContDiffOn 𝕜 n f s) (h₁ : forall
 x in s, f₁ x = f x) : ContDiffOn 𝕜 n f₁ s
· 使用定理 `contDiffOn_id`：contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `tangentBundle_model_space_chartAt`：tangentBundle_model_space_chartAt (p 
: TangentBundle I H) : (chartAt (ModelProd H E) p).toPartialEquiv = (TotalSpace.
toProd H E).toPartialEq…
· 使用定理 `Equiv.toPartialEquiv_source`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β)
, e.toPartialEquiv.source = Set.univ
· 使用定理 `Equiv.toPartialEquiv_apply`：∀ {α : Type u_1} {β : Type u_2} (e : α ≃ β),
 ↑e.toPartialEquiv = ⇑e
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `PartialEquiv.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} (toFun toFun
_1 : α → β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : 
invFun = invFun_…
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
-/
theorem contMDiff_tangentBundleModelSpaceHomeomorph_symm :
    ContMDiff I.tangent I.tangent n
    ((tangentBundleModelSpaceHomeomorph I).symm : ModelProd H E → TangentBundle I H) := by
  apply contMDiff_iff.2 ⟨Homeomorph.continuous _, fun x y ↦ ?_⟩
  apply contDiffOn_id.congr
  simp only [mfld_simps, mem_range, TotalSpace.toProd, Equiv.coe_fn_symm_mk, forall_exists_index,
    Prod.forall, Prod.mk.injEq]
  rintro a b x rfl
  simpa [PartialEquiv.prod] using ⟨rfl, rfl⟩

set_option backward.isDefEq.respectTransparency false in
variable (H I) in
/-- In the tangent bundle to the model space, the second projection is `C^n`. -/
/-
**contMDiff_snd_tangentBundle_modelSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_snd_tangentBundle_modelSpace : ContMDiff I.tangent 𝓘(𝕜, E) n (fu
n (p : TangentBundle I H) => p.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ContMDiff.comp`：ContMDiff.comp {g : M' -> M''} (hg : ContMDiff I' I'' n 
g) (hf : ContMDiff I I' n f) : ContMDiff I I'' n (g ∘ f)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `chartedSpaceSelf_prod`：chartedSpaceSelf_prod : prodChartedSpace H H H' H
' = chartedSpaceSelf (H × H')
· 使用定理 `contMDiff_snd`：contMDiff_snd : ContMDiff (I.prod J) J n (@Prod.snd M N)
· 使用定理 `contMDiff_tangentBundleModelSpaceHomeomorph`：contMDiff_tangentBundleMode
lSpaceHomeomorph : ContMDiff I.tangent (I.prod 𝓘(𝕜, E)) n (tangentBundleModelSpa
ceHomeomorph I : TangentBundle I …

--- 原说明 ---
In the tangent bundle to the model space, the second projection is `C^n`.
-/
lemma contMDiff_snd_tangentBundle_modelSpace :
    ContMDiff I.tangent 𝓘(𝕜, E) n (fun (p : TangentBundle I H) ↦ p.2) := by
  change CMDiff n ((id Prod.snd : ModelProd H E → E) ∘ (tangentBundleModelSpaceHomeomorph I))
  apply ContMDiff.comp (I' := I.prod 𝓘(𝕜, E))
  · convert! contMDiff_snd
    rw [chartedSpaceSelf_prod]
    rfl
  · exact contMDiff_tangentBundleModelSpaceHomeomorph

/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
/-
**contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt {V : Π (x : E), Tangent
Space 𝓘(𝕜, E) x} {s : Set E} {x : E} : CMDiffAt[s] n (T% V) x ↔ ContDiffWithinAt
 𝕜 n V s x
参数：x : E；𝕜, E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `ContMDiffWithinAt.contDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…
· 使用定理 `ContMDiffAt.comp_contMDiffWithinAt`：ContMDiffAt.comp_contMDiffWithinAt {
g : M' -> M''} (x : M) (hg : ContMDiffAt I' I'' n g (f x)) (hf : ContMDiffWithin
At I I' n f s x) : ContM…
· 使用定理 `ContMDiff.contMDiffAt`：ContMDiff.contMDiffAt (h : ContMDiff I I' n f) : 
ContMDiffAt I I' n f x
· 使用引理 `contMDiff_snd_tangentBundle_modelSpace`：contMDiff_snd_tangentBundle_mode
lSpace : ContMDiff I.tangent 𝓘(𝕜, E) n (fun (p : TangentBundle I H) => p.2)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bundle.contMDiffWithinAt_totalSpace`：contMDiffWithinAt_totalSpace {f : M
 -> TotalSpace F E} {s : Set M} {x₀ : M} : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)
) n f s x₀ ↔ ContMDiffWit…
· 使用定理 `contMDiffWithinAt_id`：contMDiffWithinAt_id : ContMDiffWithinAt I I n (id
 : M -> M) s x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `trivializationAt_model_space_apply`：trivializationAt_model_space_apply (
p : TangentBundle I H) (x : H) : trivializationAt E (TangentSpace I) x p = (p.1,
 p.2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContDiffWithinAt.contMDiffWithinAt`：∀ {𝕜 : Type u_1} [inst : Nontriviall
yNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Norme
dSpace 𝕜 E] {E' : Type u…

--- 原说明 ---
A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` 
in the vector
space sense.
-/
lemma contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} {x : E} :
    CMDiffAt[s] n (T% V) x ↔ ContDiffWithinAt 𝕜 n V s x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ContMDiffWithinAt.contDiffWithinAt <|
      (contMDiff_snd_tangentBundle_modelSpace E 𝓘(𝕜, E)).contMDiffAt.comp_contMDiffWithinAt _ h
  · apply Bundle.contMDiffWithinAt_totalSpace.2
    refine ⟨contMDiffWithinAt_id, ?_⟩
    convert! h.contMDiffWithinAt with y
    simp

set_option backward.isDefEq.respectTransparency false in
/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
/-
**contMDiffAt_vectorSpace_iff_contDiffAt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffAt_vectorSpace_iff_contDiffAt {V : Π (x : E), TangentSpace 𝓘(𝕜, E
) x} {x : E} : CMDiffAt n (T% V) x ↔ ContDiffAt 𝕜 n V x
参数：x : E；𝕜, E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` 
in the vector
space sense.
-/
lemma contMDiffAt_vectorSpace_iff_contDiffAt
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {x : E} :
    CMDiffAt n (T% V) x ↔ ContDiffAt 𝕜 n V x := by
  simp only [← contMDiffWithinAt_univ, ← contDiffWithinAt_univ,
    contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
/-
**contMDiffOn_vectorSpace_iff_contDiffOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiffOn_vectorSpace_iff_contDiffOn {V : Π (x : E), TangentSpace 𝓘(𝕜, E
) x} {s : Set E} : CMDiff[s] n (T% V) ↔ ContDiffOn 𝕜 n V s
参数：x : E；𝕜, E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` 
in the vector
space sense.
-/
lemma contMDiffOn_vectorSpace_iff_contDiffOn
    {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} {s : Set E} :
    CMDiff[s] n (T% V) ↔ ContDiffOn 𝕜 n V s := by
  simp only [ContMDiffOn, ContDiffOn, contMDiffWithinAt_vectorSpace_iff_contDiffWithinAt]

set_option backward.isDefEq.respectTransparency false in
/-- A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` in the vector
space sense. -/
/-
**contMDiff_vectorSpace_iff_contDiff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：contMDiff_vectorSpace_iff_contDiff {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x}
 : CMDiff n (T% V) ↔ ContDiff 𝕜 n V
参数：x : E；𝕜, E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A vector field on a vector space is `C^n` in the manifold sense iff it is `C^n` 
in the vector
space sense.
-/
lemma contMDiff_vectorSpace_iff_contDiff {V : Π (x : E), TangentSpace 𝓘(𝕜, E) x} :
    CMDiff n (T% V) ↔ ContDiff 𝕜 n V := by
  simp only [← contMDiffOn_univ, ← contDiffOn_univ, contMDiffOn_vectorSpace_iff_contDiffOn]

section inTangentCoordinates

variable {N : Type*}

/-- The map `inCoordinates` for the tangent bundle is trivial on the model spaces -/
/-
**inCoordinates_tangent_bundle_core_model_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inCoordinates_tangent_bundle_core_model_space (x₀ x : H) (y₀ y : H') (ϕ : 
E ->L[𝕜] E') : inCoordinates E (TangentSpace I) E' (TangentSpace I') x₀ x y₀ y ϕ
 = ϕ
参数：x₀ x : H；y₀ y : H'；ϕ : E ->L[𝕜] E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `VectorBundleCore.vectorBundle`：∀ {R : Type u_1} {B : Type u_2} {F : Type
 u_3} [inst : NontriviallyNormedField R] [inst_1 : NormedAddCommGroup F]   [inst
_2 : NormedSpace R …
· 使用定理 `VectorBundleCore.inCoordinates_eq`：∀ {B : Type u_2} {F : Type u_3} [inst
 : NormedAddCommGroup F] [inst_1 : TopologicalSpace B] {𝕜₁ : Type u_5}   {𝕜₂ : T
ype u_6} [inst_2 : Nont…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ContinuousLinearMap.comp.congr_simp`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {
R₃ : Type u_3} [inst : Semiring R₁] [inst_1 : Semiring R₂] [inst_2 : Semiring R₃
]   {σ₁₂ : R₁ →+* R₂} {σ₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `tangentBundleCore_indexAt`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `tangentBundleCore_coordChange_model_space`：tangentBundleCore_coordChange
_model_space (x x' z : H) : (tangentBundleCore I H).coordChange (achart H x) (ac
hart H x') z = ContinuousLinear…
· 使用定理 `ContinuousLinearMap.id_comp`：id_comp (f : M₁ ->SL[σ₁₂] M₂) : .id R₂ M₂ ∘
SL f = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ContinuousLinearMap.comp_id`：comp_id (f : M₁ ->SL[σ₁₂] M₂) : f ∘SL .id R
₁ M₁ = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The map `inCoordinates` for the tangent bundle is trivial on the model spaces
-/
theorem inCoordinates_tangent_bundle_core_model_space (x₀ x : H) (y₀ y : H') (ϕ : E →L[𝕜] E') :
    inCoordinates E (TangentSpace I) E' (TangentSpace I') x₀ x y₀ y ϕ = ϕ := by
  erw [VectorBundleCore.inCoordinates_eq] <;> try trivial
  simp_rw [tangentBundleCore_indexAt, tangentBundleCore_coordChange_model_space,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]

variable (I I') in
/-- When `ϕ x` is a continuous linear map that changes vectors in charts around `f x` to vectors
in charts around `g x`, `inTangentCoordinates I I' f g ϕ x₀ x` is a coordinate change of
this continuous linear map that makes sense from charts around `f x₀` to charts around `g x₀`
by composing it with appropriate coordinate changes.
Note that the type of `ϕ` is more accurately
`Π x : N, TangentSpace I (f x) →L[𝕜] TangentSpace I' (g x)`.
We are unfolding `TangentSpace` in this type so that Lean recognizes that the type of `ϕ` doesn't
actually depend on `f` or `g`.

This is the underlying function of the trivializations of the hom of (pullbacks of) tangent spaces.
-/
/-
**inTangentCoordinates** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：inTangentCoordinates (f : N -> M) (g : N -> M') (ϕ : N -> E ->L[𝕜] E') : N
 -> N -> E ->L[𝕜] E'
参数：f : N -> M；g : N -> M'；ϕ : N -> E ->L[𝕜] E'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `ϕ x` is a continuous linear map that changes vectors in charts around `f x
` to vectors
in charts around `g x`, `inTangentCoordinates I I' f g ϕ x₀ x` is a coordinate c
hange of
this continuous linear map that makes sense from charts around `f x₀` to charts 
around `g x₀`
by composing it with appropriate coordinate changes.
Note that the type of `ϕ` is more accurately
`Π x : N, TangentSpace I (f x) →L[𝕜] TangentSpace I' (g x)`.
We are unfolding `TangentSpace` in this type so that Lean recognizes that the ty
pe of `ϕ` doesn't
actually depend on `f` or `g`.

This is the underlying function of the trivializations of the hom of (pullbacks 
of) tangent spaces.
-/
def inTangentCoordinates (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') : N → N → E →L[𝕜] E' :=
  fun x₀ x => inCoordinates E (TangentSpace I) E' (TangentSpace I') (f x₀) (f x) (g x₀) (g x) (ϕ x)
/-
**inTangentCoordinates_model_space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inTangentCoordinates_model_space (f : N -> H) (g : N -> H') (ϕ : N -> E ->
L[𝕜] E') (x₀ : N) : inTangentCoordinates I I' f g ϕ x₀ = ϕ
参数：f : N -> H；g : N -> H'；ϕ : N -> E ->L[𝕜] E'；x₀ : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `inCoordinates_tangent_bundle_core_model_space`：inCoordinates_tangent_bun
dle_core_model_space (x₀ x : H) (y₀ y : H') (ϕ : E ->L[𝕜] E') : inCoordinates E 
(TangentSpace I) E' (TangentSpace I…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inTangentCoordinates_model_space (f : N → H) (g : N → H') (ϕ : N → E →L[𝕜] E') (x₀ : N) :
    inTangentCoordinates I I' f g ϕ x₀ = ϕ := by
  simp +unfoldPartialApp only [inTangentCoordinates,
    inCoordinates_tangent_bundle_core_model_space]

/-- To write a linear map between tangent spaces in coordinates amounts to precomposing and
postcomposing it with suitable coordinate changes. For a concrete version expressing the
change of coordinates as derivatives of extended charts,
see `inTangentCoordinates_eq_mfderiv_comp`. -/
/-
**inTangentCoordinates_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：inTangentCoordinates_eq (f : N -> M) (g : N -> M') (ϕ : N -> E ->L[𝕜] E') 
{x₀ x : N} (hx : f x in (chartAt H (f x₀)).source) (hy : g x in (chartAt H' (g x
₀)).source) : inTangentCoordinates I I' f g ϕ x₀ x = (tangentBundleCore I' M').c
oordChange (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L ϕ x ∘L (tangentBundleCo
re I M).coordChange (achart H (f x₀)) (achart H (f x)) (f x)
参数：f : N -> M；g : N -> M'；ϕ : N -> E ->L[𝕜] E'；hx : f x in (chartAt H (f x₀)).so
urce；hy : g x in (chartAt H' (g x₀)).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundleCore.inCoordinates_eq`：∀ {B : Type u_2} {F : Type u_3} [inst
 : NormedAddCommGroup F] [inst_1 : TopologicalSpace B] {𝕜₁ : Type u_5}   {𝕜₂ : T
ype u_6} [inst_2 : Nont…

--- 原说明 ---
To write a linear map between tangent spaces in coordinates amounts to precompos
ing and
postcomposing it with suitable coordinate changes. For a concrete version expres
sing the
change of coordinates as derivatives of extended charts,
see `inTangentCoordinates_eq_mfderiv_comp`.
-/
theorem inTangentCoordinates_eq (f : N → M) (g : N → M') (ϕ : N → E →L[𝕜] E') {x₀ x : N}
    (hx : f x ∈ (chartAt H (f x₀)).source) (hy : g x ∈ (chartAt H' (g x₀)).source) :
    inTangentCoordinates I I' f g ϕ x₀ x =
      (tangentBundleCore I' M').coordChange (achart H' (g x)) (achart H' (g x₀)) (g x) ∘L
        ϕ x ∘L (tangentBundleCore I M).coordChange (achart H (f x₀)) (achart H (f x)) (f x) :=
  (tangentBundleCore I M).inCoordinates_eq (tangentBundleCore I' M') (ϕ x) hx hy

end inTangentCoordinates

end General

