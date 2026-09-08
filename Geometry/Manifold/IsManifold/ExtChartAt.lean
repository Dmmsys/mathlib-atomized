/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Extended charts in smooth manifolds

In a `C^n` manifold with corners with the model `I` on `(E, H)`, the charts take values in the
model space `H`. However, we also need to use extended charts taking values in the model vector
space `E`. These extended charts are not `OpenPartialHomeomorph` as the target is not open in `E`
in general, but we can still register them as `PartialEquiv`s.

## Main definitions

* `OpenPartialHomeomorph.extend`: compose an open partial homeomorphism into `H` with the model `I`,
  to obtain a `PartialEquiv` into `E`. Extended charts are an example of this.
* `extChartAt I x`: the extended chart at `x`, obtained by composing the `chartAt H x` with `I`.
  Since the target is in general not open, this is not an open partial homeomorphism in general, but
  we register them as `PartialEquiv`s.
* `I.extendCoordChange e e'`: the change of extended charts `(e.extend I).symm ≫ e'.extend I`.

## Main results

* `ModelWithCorners.contDiffOn_extendCoordChange`: if `f` and `f'` lie in the maximal atlas on `M`,
  `I.extendCoordChange f f'` is Cⁿ on its source

* `contDiffOn_ext_coord_change`: for `x x' : M`, the coordinate change
  `(extChartAt I x').symm ≫ extChartAt I x` is continuous on its source

* `Manifold.locallyCompact_of_finiteDimensional`: a finite-dimensional manifold
  modelled on a locally compact field (such as ℝ, ℂ or the `p`-adic numbers) is locally compact
* `LocallyCompactSpace.of_locallyCompact_manifold`: a locally compact manifold must be modelled
  on a locally compact space.
* `FiniteDimensional.of_locallyCompact_manifold`: a locally compact manifold must be modelled
  on a finite-dimensional space

## Implementation notes

This file uses the name `writtenInExtend` (in analogy to `writtenInExtChart`) to refer to a
composition `ψ.extend J ∘ f ∘ φ.extend I` of `f : M → N` with charts `ψ` and `φ` extended by the
appropriate models with corners. This is not a definition, so technically deviating from the naming
convention.

TODO: this file uses more made-up names; document these as well

-/

@[expose] public section

noncomputable section

open Set Filter Function
open scoped Manifold Topology

variable {𝕜 E M H E' M' H' : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] [TopologicalSpace M] {n : WithTop ℕ∞}
  (f f' : OpenPartialHomeomorph M H)
  {I : ModelWithCorners 𝕜 E H} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  [TopologicalSpace M'] {I' : ModelWithCorners 𝕜 E' H'} {s t : Set M}

section ExtendedCharts

namespace OpenPartialHomeomorph

variable (I) in
/-- Given a chart `f` on a manifold with corners, `f.extend I` is the extended chart to the model
vector space. -/
@[simp, mfld_simps]
/-
**OpenPartialHomeomorph.extend** 是 Mathlib 中的一个定义，位于命名空间 `OpenPartialHomeomorph`
。
形式化陈述：extend : PartialEquiv M E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a chart `f` on a manifold with corners, `f.extend I` is the extended chart
 to the model
vector space.
-/
def extend : PartialEquiv M E :=
  f.toPartialEquiv ≫ I.toPartialEquiv
/-
**OpenPartialHomeomorph.extend_coe** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeomo
rph`。
形式化陈述：extend_coe : ⇑(f.extend I) = I ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extend_coe : ⇑(f.extend I) = I ∘ f :=
  rfl
/-
**OpenPartialHomeomorph.extend_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：extend_coe_symm : ⇑(f.extend I).symm = f.symm ∘ I.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extend_coe_symm : ⇑(f.extend I).symm = f.symm ∘ I.symm :=
  rfl
/-
**OpenPartialHomeomorph.extend_source** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：extend_source : (f.extend I).source = f.source
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : 
Type u_3} {H : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAd
dCommGroup E] [inst_2 :…
· 使用定理 `PartialEquiv.trans_source`：trans_source : (e.trans e').source = e.source
 inter e ⁻¹' e'.source
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem extend_source : (f.extend I).source = f.source := by
  rw [extend, PartialEquiv.trans_source, I.source_eq, preimage_univ, inter_univ]
/-
**OpenPartialHomeomorph.isOpen_extend_source** 是 Mathlib 中的一个定理，位于命名空间 `OpenPart
ialHomeomorph`。
形式化陈述：isOpen_extend_source : IsOpen (f.extend I).source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem isOpen_extend_source : IsOpen (f.extend I).source := by
  rw [extend_source]
  exact f.open_source
/-
**OpenPartialHomeomorph.extend_target** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：extend_target : (f.extend I).target = I.symm ⁻¹' f.target inter range I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_target : (f.extend I).target = I.symm ⁻¹' f.target ∩ range I := by
  simp_rw [extend, PartialEquiv.trans_target, I.target_eq, I.toPartialEquiv_coe_symm, inter_comm]
/-
**OpenPartialHomeomorph.extend_target'** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHom
eomorph`。
形式化陈述：extend_target' : (f.extend I).target = I '' f.target
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : 
Type u_3} {H : Type u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAd
dCommGroup E] [inst_2 :…
· 使用定理 `PartialEquiv.trans_target''`：trans_target'' : (e.trans e').target = e' '
' (e'.source inter e.target)
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `ModelWithCorners.toPartialEquiv_coe`：toPartialEquiv_coe : (I.toPartialEq
uiv : H -> E) = I
-/
theorem extend_target' : (f.extend I).target = I '' f.target := by
  rw [extend, PartialEquiv.trans_target'', I.source_eq, univ_inter, I.toPartialEquiv_coe]
/-
**OpenPartialHomeomorph.extend_target_eq_image_source** 是 Mathlib 中的一个定理，位于命名空间 
`OpenPartialHomeomorph`。
形式化陈述：extend_target_eq_image_source : (f.extend I).target = (f.extend I) '' f.so
urce
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_target'`：extend_target' : (f.extend I).targ
et = I '' f.target
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.image_source_eq_target`：image_source_eq_target : e
 '' e.source = e.target
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `OpenPartialHomeomorph.extend_coe`：extend_coe : ⇑(f.extend I) = I ∘ f
-/
theorem extend_target_eq_image_source : (f.extend I).target = (f.extend I) '' f.source := by
  rw [f.extend_target', ← f.image_source_eq_target, ← image_comp, f.extend_coe]
/-
**OpenPartialHomeomorph.isOpen_extend_target** 是 Mathlib 中的一个引理，位于命名空间 `OpenPart
ialHomeomorph`。
形式化陈述：isOpen_extend_target [I.Boundaryless] : IsOpen (f.extend I).target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_target`：extend_target : (f.extend I).target
 = I.symm ⁻¹' f.target inter range I
· 使用定理 `ModelWithCorners.range_eq_univ`：ModelWithCorners.range_eq_univ {𝕜 : Type
*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜
 E] {H : Type*} [Top…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
lemma isOpen_extend_target [I.Boundaryless] : IsOpen (f.extend I).target := by
  rw [extend_target, I.range_eq_univ, inter_univ]
  exact I.continuous_symm.isOpen_preimage _ f.open_target
/-
**OpenPartialHomeomorph.mapsTo_extend** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHome
omorph`。
形式化陈述：mapsTo_extend (hs : s subseteq f.source) : MapsTo (f.extend I) s ((f.exten
d I).symm ⁻¹' s inter range I)
参数：hs : s subseteq f.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mapsTo_iff_image_subset`：mapsTo_iff_image_subset : MapsTo f s t ↔ f 
'' s subseteq t
· 使用定理 `OpenPartialHomeomorph.extend_coe`：extend_coe : ⇑(f.extend I) = I ∘ f
· 使用定理 `OpenPartialHomeomorph.extend_coe_symm`：extend_coe_symm : ⇑(f.extend I).s
ymm = f.symm ∘ I.symm
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `OpenPartialHomeomorph.image_eq_target_inter_inv_preimage`：image_eq_targe
t_inter_inv_preimage {s : Set X} (h : s subseteq e.source) : e '' s = e.target i
nter e.symm ⁻¹' s
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem mapsTo_extend (hs : s ⊆ f.source) :
    MapsTo (f.extend I) s ((f.extend I).symm ⁻¹' s ∩ range I) := by
  rw [mapsTo_iff_image_subset, extend_coe, extend_coe_symm, preimage_comp, ← I.image_eq, image_comp,
    f.image_eq_target_inter_inv_preimage hs]
  exact image_mono inter_subset_right
/-
**OpenPartialHomeomorph.extend_left_inv** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：extend_left_inv {x : M} (hxf : x in f.source) : (f.extend I).symm (f.exten
d I x) = x
参数：hxf : x in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
-/
theorem extend_left_inv {x : M} (hxf : x ∈ f.source) : (f.extend I).symm (f.extend I x) = x :=
  (f.extend I).left_inv <| by rwa [f.extend_source]

/-- Variant of `f.extend_left_inv I`, stated in terms of images. -/
/-
**OpenPartialHomeomorph.extend_left_inv'** 是 Mathlib 中的一个引理，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：extend_left_inv' (ht : t subseteq f.source) : ((f.extend I).symm ∘ (f.exte
nd I)) '' t = t
参数：ht : t subseteq f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.image_eq_self`：∀ {α : Type u_1} {s : Set α} {f : α → α}, Set.Eq
On f id s → f '' s = s
· 使用定理 `OpenPartialHomeomorph.extend_left_inv`：extend_left_inv {x : M} (hxf : x 
in f.source) : (f.extend I).symm (f.extend I x) = x

--- 原说明 ---
Variant of `f.extend_left_inv I`, stated in terms of images.
-/
lemma extend_left_inv' (ht : t ⊆ f.source) : ((f.extend I).symm ∘ (f.extend I)) '' t = t :=
  EqOn.image_eq_self (fun _ hx ↦ f.extend_left_inv (ht hx))
/-
**OpenPartialHomeomorph.extend_source_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `OpenPa
rtialHomeomorph`。
形式化陈述：extend_source_mem_nhds {x : M} (h : x in f.source) : (f.extend I).source i
n 𝓝 x
参数：h : x in f.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.isOpen_extend_source`：isOpen_extend_source : IsOpe
n (f.extend I).source
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
-/
theorem extend_source_mem_nhds {x : M} (h : x ∈ f.source) : (f.extend I).source ∈ 𝓝 x :=
  (isOpen_extend_source f).mem_nhds <| by rwa [f.extend_source]
/-
**OpenPartialHomeomorph.extend_source_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `
OpenPartialHomeomorph`。
形式化陈述：extend_source_mem_nhdsWithin {x : M} (h : x in f.source) : (f.extend I).so
urce in 𝓝[s] x
参数：h : x in f.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `OpenPartialHomeomorph.extend_source_mem_nhds`：extend_source_mem_nhds {x 
: M} (h : x in f.source) : (f.extend I).source in 𝓝 x
-/
theorem extend_source_mem_nhdsWithin {x : M} (h : x ∈ f.source) : (f.extend I).source ∈ 𝓝[s] x :=
  mem_nhdsWithin_of_mem_nhds <| extend_source_mem_nhds f h
/-
**OpenPartialHomeomorph.continuousOn_extend** 是 Mathlib 中的一个定理，位于命名空间 `OpenParti
alHomeomorph`。
形式化陈述：continuousOn_extend : ContinuousOn (f.extend I) (f.extend I).source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_continuousOn`：Continuous.comp_continuousOn {g : β -> γ} 
{f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continuou
sOn (g ∘ f) s
· 使用定理 `ModelWithCorners.continuous`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 
𝕜 E] {H : Type u_…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
· 使用定理 `OpenPartialHomeomorph.continuousOn`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y), ContinuousOn (↑…
-/
theorem continuousOn_extend : ContinuousOn (f.extend I) (f.extend I).source := by
  refine I.continuous.comp_continuousOn ?_
  rw [extend_source]
  exact f.continuousOn
/-
**OpenPartialHomeomorph.continuousAt_extend** 是 Mathlib 中的一个定理，位于命名空间 `OpenParti
alHomeomorph`。
形式化陈述：continuousAt_extend {x : M} (h : x in f.source) : ContinuousAt (f.extend I
) x
参数：h : x in f.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `OpenPartialHomeomorph.continuousOn_extend`：continuousOn_extend : Continu
ousOn (f.extend I) (f.extend I).source
· 使用定理 `OpenPartialHomeomorph.extend_source_mem_nhds`：extend_source_mem_nhds {x 
: M} (h : x in f.source) : (f.extend I).source in 𝓝 x
-/
theorem continuousAt_extend {x : M} (h : x ∈ f.source) : ContinuousAt (f.extend I) x :=
  (continuousOn_extend f).continuousAt <| extend_source_mem_nhds f h
/-
**OpenPartialHomeomorph.map_extend_nhds** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：map_extend_nhds {x : M} (hy : x in f.source) : map (f.extend I) (𝓝 x) = 𝓝[
range I] f.extend I x
参数：hy : x in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_coe`：extend_coe : ⇑(f.extend I) = I ∘ f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.map_nhds_eq`：map_nhds_eq (x : H) : map I (𝓝 x) = 𝓝[rang
e I] I x
· 使用定理 `OpenPartialHomeomorph.map_nhds_eq`：map_nhds_eq {x} (hx : x in e.source) 
: map e (𝓝 x) = 𝓝 (e x)
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
-/
theorem map_extend_nhds {x : M} (hy : x ∈ f.source) :
    map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x := by
  rwa [extend_coe, comp_apply, ← I.map_nhds_eq, ← f.map_nhds_eq, map_map]
/-
**OpenPartialHomeomorph.map_extend_nhds_of_mem_interior_range** 是 Mathlib 中的一个定理
，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：map_extend_nhds_of_mem_interior_range {x : M} (hx : x in f.source) (h'x : 
f.extend I x in interior (range I)) : map (f.extend I) (𝓝 x) = 𝓝 (f.extend I x)
参数：hx : x in f.source；h'x : f.extend I x in interior (range I)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.map_extend_nhds`：map_extend_nhds {x : M} (hy : x i
n f.source) : map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x
· 使用定理 `nhdsWithin_eq_nhds`：∀ {α : Type u_1} [inst : TopologicalSpace α] {a : α}
 {s : Set α}, nhdsWithin a s = nhds a ↔ s ∈ nhds a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
-/
theorem map_extend_nhds_of_mem_interior_range {x : M} (hx : x ∈ f.source)
    (h'x : f.extend I x ∈ interior (range I)) :
    map (f.extend I) (𝓝 x) = 𝓝 (f.extend I x) := by
  rw [f.map_extend_nhds hx, nhdsWithin_eq_nhds]
  exact mem_of_superset (isOpen_interior.mem_nhds h'x) interior_subset
/-
**OpenPartialHomeomorph.map_extend_nhds_of_boundaryless** 是 Mathlib 中的一个定理，位于命名空
间 `OpenPartialHomeomorph`。
形式化陈述：map_extend_nhds_of_boundaryless [I.Boundaryless] {x : M} (hx : x in f.sour
ce) : map (f.extend I) (𝓝 x) = 𝓝 (f.extend I x)
参数：hx : x in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.map_extend_nhds`：map_extend_nhds {x : M} (hy : x i
n f.source) : map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x
· 使用定理 `ModelWithCorners.range_eq_univ`：ModelWithCorners.range_eq_univ {𝕜 : Type
*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜
 E] {H : Type*} [Top…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
-/
theorem map_extend_nhds_of_boundaryless [I.Boundaryless] {x : M} (hx : x ∈ f.source) :
    map (f.extend I) (𝓝 x) = 𝓝 (f.extend I x) := by
  rw [f.map_extend_nhds hx, I.range_eq_univ, nhdsWithin_univ]
/-
**OpenPartialHomeomorph.extend_target_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `
OpenPartialHomeomorph`。
形式化陈述：extend_target_mem_nhdsWithin {y : M} (hy : y in f.source) : (f.extend I).t
arget in 𝓝[range I] f.extend I y
参数：hy : y in f.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
· 使用定理 `OpenPartialHomeomorph.map_extend_nhds`：map_extend_nhds {x : M} (hy : x i
n f.source) : map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x
· 使用定理 `Filter.image_mem_map`：image_mem_map (hs : s in f) : m '' s in map m f
· 使用定理 `OpenPartialHomeomorph.extend_source_mem_nhds`：extend_source_mem_nhds {x 
: M} (h : x in f.source) : (f.extend I).source in 𝓝 x
-/
theorem extend_target_mem_nhdsWithin {y : M} (hy : y ∈ f.source) :
    (f.extend I).target ∈ 𝓝[range I] f.extend I y := by
  rw [← PartialEquiv.image_source_eq_target, ← map_extend_nhds f hy]
  exact image_mem_map (extend_source_mem_nhds _ hy)
/-
**OpenPartialHomeomorph.extend_image_target_mem_nhds** 是 Mathlib 中的一个引理，位于命名空间 `
OpenPartialHomeomorph`。
形式化陈述：extend_image_target_mem_nhds {x : M} (hx : x in f.source) : I '' f.target 
in 𝓝[range I] (f.extend I) x
参数：hx : x in f.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.map_extend_nhds`：map_extend_nhds {x : M} (hy : x i
n f.source) : map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `OpenPartialHomeomorph.extend_coe`：extend_coe : ⇑(f.extend I) = I ∘ f
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `ModelWithCorners.preimage_image`：preimage_image (s : Set H) : I ⁻¹' I ''
 s = s
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
-/
lemma extend_image_target_mem_nhds {x : M} (hx : x ∈ f.source) :
    I '' f.target ∈ 𝓝[range I] (f.extend I) x := by
  rw [← f.map_extend_nhds hx, Filter.mem_map,
    f.extend_coe, Set.preimage_comp, I.preimage_image f.target]
  exact (f.continuousAt hx).preimage_mem_nhds (f.open_target.mem_nhds (f.map_source hx))
/-
**OpenPartialHomeomorph.extend_image_nhds_mem_nhds_of_boundaryless** 是 Mathlib 中
的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：extend_image_nhds_mem_nhds_of_boundaryless [I.Boundaryless] {x} (hx : x in
 f.source) {s : Set M} (h : s in 𝓝 x) : (f.extend I) '' s in 𝓝 ((f.extend I) x)
参数：hx : x in f.source；h : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.map_extend_nhds_of_boundaryless`：map_extend_nhds_o
f_boundaryless [I.Boundaryless] {x : M} (hx : x in f.source) : map (f.extend I) 
(𝓝 x) = 𝓝 (f.extend I x)
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem extend_image_nhds_mem_nhds_of_boundaryless [I.Boundaryless] {x} (hx : x ∈ f.source)
    {s : Set M} (h : s ∈ 𝓝 x) : (f.extend I) '' s ∈ 𝓝 ((f.extend I) x) := by
  rw [← f.map_extend_nhds_of_boundaryless hx, Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s
/-
**OpenPartialHomeomorph.extend_image_nhds_mem_nhds_of_mem_interior_range** 是 Mat
hlib 中的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：extend_image_nhds_mem_nhds_of_mem_interior_range {x} (hx : x in f.source) 
(h'x : f.extend I x in interior (range I)) {s : Set M} (h : s in 𝓝 x) : (f.exten
d I) '' s in 𝓝 ((f.extend I) x)
参数：hx : x in f.source；h'x : f.extend I x in interior (range I)；h : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.map_extend_nhds_of_mem_interior_range`：map_extend_
nhds_of_mem_interior_range {x : M} (hx : x in f.source) (h'x : f.extend I x in i
nterior (range I)) : map (f.extend I) (𝓝 x) = 𝓝 (…
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem extend_image_nhds_mem_nhds_of_mem_interior_range {x} (hx : x ∈ f.source)
    (h'x : f.extend I x ∈ interior (range I)) {s : Set M} (h : s ∈ 𝓝 x) :
    (f.extend I) '' s ∈ 𝓝 ((f.extend I) x) := by
  rw [← f.map_extend_nhds_of_mem_interior_range hx h'x, Filter.mem_map]
  filter_upwards [h] using subset_preimage_image (f.extend I) s
/-
**OpenPartialHomeomorph.extend_target_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：extend_target_subset_range : (f.extend I).target subseteq range I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
-/
theorem extend_target_subset_range : (f.extend I).target ⊆ range I := by simp only [mfld_simps]
/-
**OpenPartialHomeomorph.interior_extend_target_subset_interior_range** 是 Mathlib
 中的一个引理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：interior_extend_target_subset_interior_range : interior (f.extend I).targe
t subseteq interior (range I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_target`：extend_target : (f.extend I).target
 = I.symm ⁻¹' f.target inter range I
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
lemma interior_extend_target_subset_interior_range :
    interior (f.extend I).target ⊆ interior (range I) := by
  rw [f.extend_target, interior_inter, (f.open_target.preimage I.continuous_symm).interior_eq]
  exact inter_subset_right

/-- If `y ∈ f.target` and `I y ∈ interior (range I)`,
then `I y` is an interior point of `(I ∘ f).target`. -/
/-
**OpenPartialHomeomorph.mem_interior_extend_target** 是 Mathlib 中的一个引理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：mem_interior_extend_target {y : H} (hy : y in f.target) (hy' : I y in inte
rior (range I)) : I y in interior (f.extend I).target
参数：hy : y in f.target；hy' : I y in interior (range I)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_target`：extend_target : (f.extend I).target
 = I.symm ⁻¹' f.target inter range I
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `IsOpen.interior_eq`：IsOpen.interior_eq (h : IsOpen s) : interior s = s
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Set.mem_inter_iff`：mem_inter_iff (x : α) (a b : Set α) : x in a inter b 
↔ x in a ∧ x in b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_of_eq_of_mem`：mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y
) (h : y in s) : x in s
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…

--- 原说明 ---
If `y ∈ f.target` and `I y ∈ interior (range I)`,
then `I y` is an interior point of `(I ∘ f).target`.
-/
lemma mem_interior_extend_target {y : H} (hy : y ∈ f.target)
    (hy' : I y ∈ interior (range I)) : I y ∈ interior (f.extend I).target := by
  rw [f.extend_target, interior_inter, (f.open_target.preimage I.continuous_symm).interior_eq,
    mem_inter_iff, mem_preimage]
  exact ⟨mem_of_eq_of_mem (I.left_inv (y)) hy, hy'⟩
/-
**OpenPartialHomeomorph.nhdsWithin_extend_target_eq** 是 Mathlib 中的一个定理，位于命名空间 `O
penPartialHomeomorph`。
形式化陈述：nhdsWithin_extend_target_eq {y : M} (hy : y in f.source) : 𝓝[(f.extend I).
target] f.extend I y = 𝓝[range I] f.extend I y
参数：hy : y in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `OpenPartialHomeomorph.extend_target_subset_range`：extend_target_subset_r
ange : (f.extend I).target subseteq range I
· 使用定理 `nhdsWithin_le_of_mem`：nhdsWithin_le_of_mem {a : α} {s t : Set α} (h : s 
in 𝓝[t] a) : 𝓝[t] a <= 𝓝[s] a
· 使用定理 `OpenPartialHomeomorph.extend_target_mem_nhdsWithin`：extend_target_mem_nh
dsWithin {y : M} (hy : y in f.source) : (f.extend I).target in 𝓝[range I] f.exte
nd I y
-/
theorem nhdsWithin_extend_target_eq {y : M} (hy : y ∈ f.source) :
    𝓝[(f.extend I).target] f.extend I y = 𝓝[range I] f.extend I y :=
  (nhdsWithin_mono _ (extend_target_subset_range _)).antisymm <|
    nhdsWithin_le_of_mem (extend_target_mem_nhdsWithin _ hy)
/-
**OpenPartialHomeomorph.extend_target_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：extend_target_eventuallyEq {y : M} (hy : y in f.source) : (f.extend I).tar
get =ᶠ[𝓝 (f.extend I y)] range I
参数：hy : y in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用定理 `OpenPartialHomeomorph.nhdsWithin_extend_target_eq`：nhdsWithin_extend_tar
get_eq {y : M} (hy : y in f.source) : 𝓝[(f.extend I).target] f.extend I y = 𝓝[ra
nge I] f.extend I y
-/
theorem extend_target_eventuallyEq {y : M} (hy : y ∈ f.source) :
    (f.extend I).target =ᶠ[𝓝 (f.extend I y)] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extend_target_eq _ hy)
/-
**OpenPartialHomeomorph.continuousAt_extend_symm'** 是 Mathlib 中的一个定理，位于命名空间 `Ope
nPartialHomeomorph`。
形式化陈述：continuousAt_extend_symm' {x : E} (h : x in (f.extend I).target) : Continu
ousAt (f.extend I).symm x
参数：h : x in (f.extend I).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `OpenPartialHomeomorph.continuousAt_symm`：continuousAt_symm {x : Y} (h : 
x in e.target) : ContinuousAt e.symm x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
-/
theorem continuousAt_extend_symm' {x : E} (h : x ∈ (f.extend I).target) :
    ContinuousAt (f.extend I).symm x :=
  (f.continuousAt_symm h.2).comp I.continuous_symm.continuousAt
/-
**OpenPartialHomeomorph.continuousAt_extend_symm** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：continuousAt_extend_symm {x : M} (h : x in f.source) : ContinuousAt (f.ext
end I).symm (f.extend I x)
参数：h : x in f.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.continuousAt_extend_symm'`：continuousAt_extend_sym
m' {x : E} (h : x in (f.extend I).target) : ContinuousAt (f.extend I).symm x
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
-/
theorem continuousAt_extend_symm {x : M} (h : x ∈ f.source) :
    ContinuousAt (f.extend I).symm (f.extend I x) :=
  continuousAt_extend_symm' f <| (f.extend I).map_source <| by rwa [f.extend_source]
/-
**OpenPartialHomeomorph.continuousOn_extend_symm** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：continuousOn_extend_symm : ContinuousOn (f.extend I).symm (f.extend I).tar
get
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `OpenPartialHomeomorph.continuousAt_extend_symm'`：continuousAt_extend_sym
m' {x : E} (h : x in (f.extend I).target) : ContinuousAt (f.extend I).symm x
-/
theorem continuousOn_extend_symm : ContinuousOn (f.extend I).symm (f.extend I).target := fun _ h =>
  (continuousAt_extend_symm' _ h).continuousWithinAt
/-
**OpenPartialHomeomorph.extend_symm_continuousWithinAt_comp_right_iff** 是 Mathli
b 中的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：extend_symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {g 
: M -> X} {s : Set M} {x : M} : ContinuousWithinAt (g ∘ (f.extend I).symm) ((f.e
xtend I).symm ⁻¹' s inter range I) (f.extend I x) ↔ ContinuousWithinAt (g ∘ f.sy
mm) (f.symm ⁻¹' s) (f x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModelWithCorners.symm_continuousWithinAt_comp_right_iff`：symm_continuous
WithinAt_comp_right_iff {X} [TopologicalSpace X] {f : H -> X} {s : Set H} {x : H
} : ContinuousWithinAt (f ∘ I.symm) (I.symm ⁻…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem extend_symm_continuousWithinAt_comp_right_iff {X} [TopologicalSpace X] {g : M → X}
    {s : Set M} {x : M} :
    ContinuousWithinAt (g ∘ (f.extend I).symm) ((f.extend I).symm ⁻¹' s ∩ range I) (f.extend I x) ↔
      ContinuousWithinAt (g ∘ f.symm) (f.symm ⁻¹' s) (f x) := by
  rw [← I.symm_continuousWithinAt_comp_right_iff]; rfl
/-
**OpenPartialHomeomorph.isOpen_extend_preimage'** 是 Mathlib 中的一个定理，位于命名空间 `OpenP
artialHomeomorph`。
形式化陈述：isOpen_extend_preimage' {s : Set E} (hs : IsOpen s) : IsOpen ((f.extend I)
.source inter f.extend I ⁻¹' s)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.isOpen_inter_preimage`：ContinuousOn.isOpen_inter_preimage {
t : Set β} (hf : ContinuousOn f s) (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s i
nter f ⁻¹' t)
· 使用定理 `OpenPartialHomeomorph.continuousOn_extend`：continuousOn_extend : Continu
ousOn (f.extend I) (f.extend I).source
· 使用定理 `OpenPartialHomeomorph.isOpen_extend_source`：isOpen_extend_source : IsOpe
n (f.extend I).source
-/
theorem isOpen_extend_preimage' {s : Set E} (hs : IsOpen s) :
    IsOpen ((f.extend I).source ∩ f.extend I ⁻¹' s) :=
  (continuousOn_extend f).isOpen_inter_preimage (isOpen_extend_source _) hs
/-
**OpenPartialHomeomorph.isOpen_extend_preimage** 是 Mathlib 中的一个定理，位于命名空间 `OpenPa
rtialHomeomorph`。
形式化陈述：isOpen_extend_preimage {s : Set E} (hs : IsOpen s) : IsOpen (f.source inte
r f.extend I ⁻¹' s)
参数：hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
· 使用定理 `OpenPartialHomeomorph.isOpen_extend_preimage'`：isOpen_extend_preimage' {
s : Set E} (hs : IsOpen s) : IsOpen ((f.extend I).source inter f.extend I ⁻¹' s)
-/
theorem isOpen_extend_preimage {s : Set E} (hs : IsOpen s) :
    IsOpen (f.source ∩ f.extend I ⁻¹' s) := by
  rw [← extend_source f (I := I)]; exact isOpen_extend_preimage' f hs
/-
**OpenPartialHomeomorph.map_extend_nhdsWithin_eq_image** 是 Mathlib 中的一个定理，位于命名空间
 `OpenPartialHomeomorph`。
形式化陈述：map_extend_nhdsWithin_eq_image {y : M} (hy : y in f.source) : map (f.exten
d I) (𝓝[s] y) = 𝓝[f.extend I '' ((f.extend I).source inter s)] f.extend I y
参数：hy : y in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_inter_of_mem`：nhdsWithin_inter_of_mem {a : α} {s t : Set α} (
h : s in 𝓝[t] a) : 𝓝[s inter t] a = 𝓝[t] a
· 使用定理 `OpenPartialHomeomorph.extend_source_mem_nhdsWithin`：extend_source_mem_nh
dsWithin {x : M} (h : x in f.source) : (f.extend I).source in 𝓝[s] x
· 使用定理 `Set.LeftInvOn.map_nhdsWithin_eq`：Set.LeftInvOn.map_nhdsWithin_eq {f : α 
-> β} {g : β -> α} {x : β} {s : Set β} (h : LeftInvOn f g s) (hx : f (g x) = x) 
(hf : ContinuousWithi…
· 使用定理 `Set.LeftInvOn.mono`：mono (hf : LeftInvOn f' f s) (ht : s₁ subseteq s) : 
LeftInvOn f' f s₁
· 使用定理 `PartialEquiv.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqui
v α β), Set.LeftInvOn (↑e.symm) (↑e) e.source
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `OpenPartialHomeomorph.continuousAt_extend_symm`：continuousAt_extend_symm
 {x : M} (h : x in f.source) : ContinuousAt (f.extend I).symm (f.extend I x)
· 使用定理 `OpenPartialHomeomorph.continuousAt_extend`：continuousAt_extend {x : M} (
h : x in f.source) : ContinuousAt (f.extend I) x
-/
theorem map_extend_nhdsWithin_eq_image {y : M} (hy : y ∈ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I '' ((f.extend I).source ∩ s)] f.extend I y := by
  set e := f.extend I
  calc
    map e (𝓝[s] y) = map e (𝓝[e.source ∩ s] y) :=
      congr_arg (map e) (nhdsWithin_inter_of_mem (extend_source_mem_nhdsWithin f hy)).symm
    _ = 𝓝[e '' (e.source ∩ s)] e y :=
      ((f.extend I).leftInvOn.mono inter_subset_left).map_nhdsWithin_eq
        ((f.extend I).left_inv <| by rwa [f.extend_source])
        (continuousAt_extend_symm f hy).continuousWithinAt
        (continuousAt_extend f hy).continuousWithinAt
/-
**OpenPartialHomeomorph.map_extend_nhdsWithin_eq_image_of_subset** 是 Mathlib 中的一
个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：map_extend_nhdsWithin_eq_image_of_subset {y : M} (hy : y in f.source) (hs 
: s subseteq f.source) : map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I '' s] f.extend
 I y
参数：hy : y in f.source；hs : s subseteq f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin_eq_image`：map_extend_nhdsWit
hin_eq_image {y : M} (hy : y in f.source) : map (f.extend I) (𝓝[s] y) = 𝓝[f.exte
nd I '' ((f.extend I).source inter s)] f.e…
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
-/
theorem map_extend_nhdsWithin_eq_image_of_subset {y : M} (hy : y ∈ f.source) (hs : s ⊆ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I '' s] f.extend I y := by
  rw [map_extend_nhdsWithin_eq_image _ hy, inter_eq_self_of_subset_right]
  rwa [extend_source]
/-
**OpenPartialHomeomorph.map_extend_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `OpenPar
tialHomeomorph`。
形式化陈述：map_extend_nhdsWithin {y : M} (hy : y in f.source) : map (f.extend I) (𝓝[s
] y) = 𝓝[(f.extend I).symm ⁻¹' s inter range I] f.extend I y
参数：hy : y in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin_eq_image`：map_extend_nhdsWit
hin_eq_image {y : M} (hy : y in f.source) : map (f.extend I) (𝓝[s] y) = 𝓝[f.exte
nd I '' ((f.extend I).source inter s)] f.e…
· 使用定理 `nhdsWithin_inter`：nhdsWithin_inter (a : α) (s t : Set α) : 𝓝[s inter t] 
a = 𝓝[s] a ⊓ 𝓝[t] a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.nhdsWithin_extend_target_eq`：nhdsWithin_extend_tar
get_eq {y : M} (hy : y in f.source) : 𝓝[(f.extend I).target] f.extend I y = 𝓝[ra
nge I] f.extend I y
· 使用定理 `PartialEquiv.image_source_inter_eq'`：image_source_inter_eq' (s : Set α) 
: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
-/
theorem map_extend_nhdsWithin {y : M} (hy : y ∈ f.source) :
    map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I y := by
  rw [map_extend_nhdsWithin_eq_image f hy, nhdsWithin_inter, ←
    nhdsWithin_extend_target_eq _ hy, ← nhdsWithin_inter, (f.extend I).image_source_inter_eq',
    inter_comm]
/-
**OpenPartialHomeomorph.map_extend_symm_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 `Op
enPartialHomeomorph`。
形式化陈述：map_extend_symm_nhdsWithin {y : M} (hy : y in f.source) : map (f.extend I)
.symm (𝓝[(f.extend I).symm ⁻¹' s inter range I] f.extend I y) = 𝓝[s] y
参数：hy : y in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin`：map_extend_nhdsWithin {y : 
M} (hy : y in f.source) : map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s 
inter range I] f.extend I y
· 使用定理 `Filter.map_map`：map_map : Filter.map m' (Filter.map m f) = Filter.map (m
' ∘ m) f
· 使用定理 `Filter.map_congr`：map_congr {m₁ m₂ : α -> β} {f : Filter α} (h : m₁ =ᶠ[f
] m₂) : map m₁ f = map m₂ f
· 使用定理 `Set.EqOn.eventuallyEq_of_mem`：Set.EqOn.eventuallyEq_of_mem {α β} {s : Se
t α} {l : Filter α} {f g : α -> β} (h : EqOn f g s) (hl : s in l) : f =ᶠ[l] g
· 使用定理 `Set.LeftInvOn.eqOn`：eqOn (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s
· 使用定理 `PartialEquiv.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqui
v α β), Set.LeftInvOn (↑e.symm) (↑e) e.source
· 使用定理 `OpenPartialHomeomorph.extend_source_mem_nhdsWithin`：extend_source_mem_nh
dsWithin {x : M} (h : x in f.source) : (f.extend I).source in 𝓝[s] x
· 使用定理 `Filter.map_id`：map_id : Filter.map id f = f
-/
theorem map_extend_symm_nhdsWithin {y : M} (hy : y ∈ f.source) :
    map (f.extend I).symm (𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I y) = 𝓝[s] y := by
  rw [← map_extend_nhdsWithin f hy, map_map, Filter.map_congr, map_id]
  exact (f.extend I).leftInvOn.eqOn.eventuallyEq_of_mem (extend_source_mem_nhdsWithin _ hy)
/-
**OpenPartialHomeomorph.map_extend_symm_nhdsWithin_range** 是 Mathlib 中的一个定理，位于命名
空间 `OpenPartialHomeomorph`。
形式化陈述：map_extend_symm_nhdsWithin_range {y : M} (hy : y in f.source) : map (f.ext
end I).symm (𝓝[range I] f.extend I y) = 𝓝 y
参数：hy : y in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `OpenPartialHomeomorph.map_extend_symm_nhdsWithin`：map_extend_symm_nhdsWi
thin {y : M} (hy : y in f.source) : map (f.extend I).symm (𝓝[(f.extend I).symm ⁻
¹' s inter range I] f.extend I y) = 𝓝[…
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
-/
theorem map_extend_symm_nhdsWithin_range {y : M} (hy : y ∈ f.source) :
    map (f.extend I).symm (𝓝[range I] f.extend I y) = 𝓝 y := by
  rw [← nhdsWithin_univ, ← map_extend_symm_nhdsWithin f (I := I) hy, preimage_univ, univ_inter]
/-
**OpenPartialHomeomorph.tendsto_extend_comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `OpenP
artialHomeomorph`。
形式化陈述：tendsto_extend_comp_iff {α : Type*} {l : Filter α} {g : α -> M} (hg : fora
llᶠ z in l, g z in f.source) {y : M} (hy : y in f.source) : Tendsto (f.extend I 
∘ g) l (𝓝 (f.extend I y)) ↔ Tendsto g l (𝓝 y)
参数：hg : forallᶠ z in l, g z in f.source；hy : y in f.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `OpenPartialHomeomorph.continuousAt_extend_symm`：continuousAt_extend_symm
 {x : M} (h : x in f.source) : ContinuousAt (f.extend I).symm (f.extend I x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_left_inv`：extend_left_inv {x : M} (hxf : x 
in f.source) : (f.extend I).symm (f.extend I x) = x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OpenPartialHomeomorph.continuousAt_extend`：continuousAt_extend {x : M} (
h : x in f.source) : ContinuousAt (f.extend I) x
-/
theorem tendsto_extend_comp_iff {α : Type*} {l : Filter α} {g : α → M}
    (hg : ∀ᶠ z in l, g z ∈ f.source) {y : M} (hy : y ∈ f.source) :
    Tendsto (f.extend I ∘ g) l (𝓝 (f.extend I y)) ↔ Tendsto g l (𝓝 y) := by
  refine ⟨fun h u hu ↦ mem_map.2 ?_, (continuousAt_extend _ hy).tendsto.comp⟩
  have := (f.continuousAt_extend_symm hy).tendsto.comp h
  rw [extend_left_inv _ hy] at this
  filter_upwards [hg, mem_map.1 (this hu)] with z hz hzu
  simpa only [(· ∘ ·), extend_left_inv _ hz, mem_preimage] using hzu
/-
**OpenPartialHomeomorph.continuousWithinAt_writtenInExtend_iff** 是 Mathlib 中的一个定
理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：continuousWithinAt_writtenInExtend_iff {f' : OpenPartialHomeomorph M' H'} 
{g : M -> M'} {y : M} (hy : y in f.source) (hgy : g y in f'.source) (hmaps : Map
sTo g s f'.source) : ContinuousWithinAt (f'.extend I' ∘ g ∘ (f.extend I).symm) (
(f.extend I).symm ⁻¹' s inter range I) (f.extend I y) ↔ ContinuousWithinAt g s y
参数：hy : y in f.source；hgy : g y in f'.source；hmaps : MapsTo g s f'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.extend_left_inv`：extend_left_inv {x : M} (hxf : x 
in f.source) : (f.extend I).symm (f.extend I x) = x
· 使用定理 `OpenPartialHomeomorph.tendsto_extend_comp_iff`：tendsto_extend_comp_iff {
α : Type*} {l : Filter α} {g : α -> M} (hg : forallᶠ z in l, g z in f.source) {y
 : M} (hy : y in f.source) : Tendst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin`：map_extend_nhdsWithin {y : 
M} (hy : y in f.source) : map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s 
inter range I] f.extend I y
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `inter_mem_nhdsWithin`：inter_mem_nhdsWithin (s : Set α) {t : Set α} {a : 
α} (h : t in 𝓝 a) : s inter t in 𝓝[s] a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `OpenPartialHomeomorph.map_extend_symm_nhdsWithin`：map_extend_symm_nhdsWi
thin {y : M} (hy : y in f.source) : map (f.extend I).symm (𝓝[(f.extend I).symm ⁻
¹' s inter range I] f.extend I y) = 𝓝[…
· 使用定理 `Filter.tendsto_map'_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{f : β → γ} {g : α → β} {x : Filter α} {y : Filter γ},   Filter.Tendsto f (Filte
r.map g x) y …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem continuousWithinAt_writtenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M → M'}
    {y : M} (hy : y ∈ f.source) (hgy : g y ∈ f'.source) (hmaps : MapsTo g s f'.source) :
    ContinuousWithinAt (f'.extend I' ∘ g ∘ (f.extend I).symm)
      ((f.extend I).symm ⁻¹' s ∩ range I) (f.extend I y) ↔ ContinuousWithinAt g s y := by
  unfold ContinuousWithinAt
  simp only [comp_apply]
  rw [extend_left_inv _ hy, f'.tendsto_extend_comp_iff _ hgy,
    ← f.map_extend_symm_nhdsWithin (I := I) hy, tendsto_map'_iff]
  rw [← f.map_extend_nhdsWithin (I := I) hy, eventually_map]
  filter_upwards [inter_mem_nhdsWithin _ (f.open_source.mem_nhds hy)] with z hz
  rw [comp_apply, extend_left_inv _ hz.2]
  exact hmaps hz.1

/-- If `s ⊆ f.source` and `g x ∈ f'.source` whenever `x ∈ s`, then `g` is continuous on `s` if and
only if `g` written in charts `f.extend I` and `f'.extend I'` is continuous on `f.extend I '' s`. -/
/-
**OpenPartialHomeomorph.continuousOn_writtenInExtend_iff** 是 Mathlib 中的一个定理，位于命名
空间 `OpenPartialHomeomorph`。
形式化陈述：continuousOn_writtenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M
 -> M'} (hs : s subseteq f.source) (hmaps : MapsTo g s f'.source) : ContinuousOn
 (f'.extend I' ∘ g ∘ (f.extend I).symm) (f.extend I '' s) ↔ ContinuousOn g s
参数：hs : s subseteq f.source；hmaps : MapsTo g s f'.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `continuousWithinAt_congr_set`：continuousWithinAt_congr_set (h : s =ᶠ[𝓝 x
] t) : ContinuousWithinAt f s x ↔ ContinuousWithinAt f t x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin_eq_image_of_subset`：map_exte
nd_nhdsWithin_eq_image_of_subset {y : M} (hy : y in f.source) (hs : s subseteq f
.source) : map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I …
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin`：map_extend_nhdsWithin {y : 
M} (hy : y in f.source) : map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s 
inter range I] f.extend I y
· 使用定理 `OpenPartialHomeomorph.continuousWithinAt_writtenInExtend_iff`：continuous
WithinAt_writtenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M -> M'} {y
 : M} (hy : y in f.source) (hgy : g y in f'.source…

--- 原说明 ---
If `s ⊆ f.source` and `g x ∈ f'.source` whenever `x ∈ s`, then `g` is continuous
 on `s` if and
only if `g` written in charts `f.extend I` and `f'.extend I'` is continuous on `
f.extend I '' s`.
-/
theorem continuousOn_writtenInExtend_iff {f' : OpenPartialHomeomorph M' H'} {g : M → M'}
    (hs : s ⊆ f.source) (hmaps : MapsTo g s f'.source) :
    ContinuousOn (f'.extend I' ∘ g ∘ (f.extend I).symm) (f.extend I '' s) ↔ ContinuousOn g s := by
  refine forall_mem_image.trans <| forall₂_congr fun x hx ↦ ?_
  refine (continuousWithinAt_congr_set ?_).trans
    (continuousWithinAt_writtenInExtend_iff _ (hs hx) (hmaps hx) hmaps)
  rw [← nhdsWithin_eq_iff_eventuallyEq, ← map_extend_nhdsWithin_eq_image_of_subset,
    ← map_extend_nhdsWithin]
  exacts [hs hx, hs hx, hs]
/-
**OpenPartialHomeomorph.extend_preimage_mem_nhds_of_mem_nhdsWithin** 是 Mathlib 中
的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：extend_preimage_mem_nhds_of_mem_nhdsWithin {s : Set E} {x : M} (hx : x in 
f.source) (hs : s in 𝓝[range I] (f.extend I x)) : (f.extend I) ⁻¹' s in 𝓝 x
参数：hx : x in f.source；hs : s in 𝓝[range I] (f.extend I x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.map_extend_nhds`：map_extend_nhds {x : M} (hy : x i
n f.source) : map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x
-/
theorem extend_preimage_mem_nhds_of_mem_nhdsWithin {s : Set E} {x : M} (hx : x ∈ f.source)
    (hs : s ∈ 𝓝[range I] (f.extend I x)) :
    (f.extend I) ⁻¹' s ∈ 𝓝 x := by
  rwa [← map_extend_nhds (I := I) f hx] at hs

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
/-
**OpenPartialHomeomorph.extend_preimage_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间
 `OpenPartialHomeomorph`。
形式化陈述：extend_preimage_mem_nhdsWithin {x : M} (h : x in f.source) (ht : t in 𝓝[s]
 x) : (f.extend I).symm ⁻¹' t in 𝓝[(f.extend I).symm ⁻¹' s inter range I] f.exte
nd I x
参数：h : x in f.source；ht : t in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.map_extend_symm_nhdsWithin`：map_extend_symm_nhdsWi
thin {y : M} (hy : y in f.source) : map (f.extend I).symm (𝓝[(f.extend I).symm ⁻
¹' s inter range I] f.extend I y) = 𝓝[…

--- 原说明 ---
Technical lemma ensuring that the preimage under an extended chart of a neighbor
hood of a point
in the source is a neighborhood of the preimage, within a set.
-/
theorem extend_preimage_mem_nhdsWithin {x : M} (h : x ∈ f.source) (ht : t ∈ 𝓝[s] x) :
    (f.extend I).symm ⁻¹' t ∈ 𝓝[(f.extend I).symm ⁻¹' s ∩ range I] f.extend I x := by
  rwa [← map_extend_symm_nhdsWithin f (I := I) h, mem_map] at ht
/-
**OpenPartialHomeomorph.extend_preimage_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：extend_preimage_mem_nhds {x : M} (h : x in f.source) (ht : t in 𝓝 x) : (f.
extend I).symm ⁻¹' t in 𝓝 (f.extend I x)
参数：h : x in f.source；ht : t in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `OpenPartialHomeomorph.continuousAt_extend_symm`：continuousAt_extend_symm
 {x : M} (h : x in f.source) : ContinuousAt (f.extend I).symm (f.extend I x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
-/
theorem extend_preimage_mem_nhds {x : M} (h : x ∈ f.source) (ht : t ∈ 𝓝 x) :
    (f.extend I).symm ⁻¹' t ∈ 𝓝 (f.extend I x) := by
  apply (continuousAt_extend_symm f h).preimage_mem_nhds
  rwa [(f.extend I).left_inv]
  rwa [f.extend_source]

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
/-
**OpenPartialHomeomorph.extend_preimage_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `Open
PartialHomeomorph`。
形式化陈述：extend_preimage_inter_eq : (f.extend I).symm ⁻¹' (s inter t) inter range I
 = (f.extend I).symm ⁻¹' s inter range I inter (f.extend I).symm ⁻¹' t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Technical lemma to rewrite suitably the preimage of an intersection under an ext
ended chart, to
bring it into a convenient form to apply derivative lemmas.
-/
theorem extend_preimage_inter_eq :
    (f.extend I).symm ⁻¹' (s ∩ t) ∩ range I =
      (f.extend I).symm ⁻¹' s ∩ range I ∩ (f.extend I).symm ⁻¹' t := by
  mfld_set_tac
/-
**OpenPartialHomeomorph.extend_symm_preimage_inter_range_eventuallyEq** 是 Mathli
b 中的一个定理，位于命名空间 `OpenPartialHomeomorph`。
形式化陈述：extend_symm_preimage_inter_range_eventuallyEq {s : Set M} {x : M} (hs : s 
subseteq f.source) (hx : x in f.source) : ((f.extend I).symm ⁻¹' s inter range I
 : Set _) =ᶠ[𝓝 (f.extend I x)] f.extend I '' s
参数：hs : s subseteq f.source；hx : x in f.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin`：map_extend_nhdsWithin {y : 
M} (hy : y in f.source) : map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s 
inter range I] f.extend I y
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin_eq_image_of_subset`：map_exte
nd_nhdsWithin_eq_image_of_subset {y : M} (hy : y in f.source) (hs : s subseteq f
.source) : map (f.extend I) (𝓝[s] y) = 𝓝[f.extend I …
-/
theorem extend_symm_preimage_inter_range_eventuallyEq {s : Set M} {x : M} (hs : s ⊆ f.source)
    (hx : x ∈ f.source) :
    ((f.extend I).symm ⁻¹' s ∩ range I : Set _) =ᶠ[𝓝 (f.extend I x)] f.extend I '' s := by
  rw [← nhdsWithin_eq_iff_eventuallyEq, ← map_extend_nhdsWithin _ hx,
    map_extend_nhdsWithin_eq_image_of_subset _ hx hs]
/-
**OpenPartialHomeomorph.extend_prod** 是 Mathlib 中的一个引理，位于命名空间 `OpenPartialHomeom
orph`。
形式化陈述：extend_prod (f' : OpenPartialHomeomorph M' H') : (f.prod f').extend (I.pro
d I') = (f.extend I).prod (f'.extend I')
参数：f' : OpenPartialHomeomorph M' H'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `PartialEquiv.prod_trans`：prod_trans {η : Type*} {ε : Type*} (e : Partial
Equiv α β) (f : PartialEquiv β γ) (e' : PartialEquiv δ η) (f' : PartialEquiv η ε
) : (e.prod e…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extend_prod (f' : OpenPartialHomeomorph M' H') :
    (f.prod f').extend (I.prod I') = (f.extend I).prod (f'.extend I') := by simp

end OpenPartialHomeomorph

namespace ModelWithCorners

/-- The change of charts from `e` to `e'` in the model vector space `E`. -/
/-
**ModelWithCorners.extendCoordChange** 是 Mathlib 中的一个缩写定义，位于命名空间 `ModelWithCorne
rs`。
形式化陈述：extendCoordChange (e e' : OpenPartialHomeomorph M H) : PartialEquiv E E
参数：e e' : OpenPartialHomeomorph M H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The change of charts from `e` to `e'` in the model vector space `E`.
-/
abbrev extendCoordChange (e e' : OpenPartialHomeomorph M H) : PartialEquiv E E :=
  (e.extend I).symm ≫ e'.extend I

variable {e e' : OpenPartialHomeomorph M H}
/-
**ModelWithCorners.extendCoordChange_symm** 是 Mathlib 中的一个引理，位于命名空间 `ModelWithCo
rners`。
形式化陈述：extendCoordChange_symm : (I.extendCoordChange e e').symm = I.extendCoordCh
ange e' e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extendCoordChange_symm : (I.extendCoordChange e e').symm = I.extendCoordChange e' e := by
  rfl
/-
**ModelWithCorners.extendCoordChange_source** 是 Mathlib 中的一个引理，位于命名空间 `ModelWith
Corners`。
形式化陈述：extendCoordChange_source : (I.extendCoordChange e e').source = I '' (e.sym
m ≫ₕ e').source
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
· 使用定理 `OpenPartialHomeomorph.extend_target`：extend_target : (f.extend I).target
 = I.symm ⁻¹' f.target inter range I
· 使用定理 `Set.inter_right_comm`：inter_right_comm (s₁ s₂ s₃ : Set α) : s₁ inter s₂ 
inter s₃ = s₁ inter s₃ inter s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extendCoordChange_source :
    (I.extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source := by
  simp_rw [extendCoordChange, PartialEquiv.trans_source, I.image_eq, e'.extend_source,
    PartialEquiv.symm_source, e.extend_target, inter_right_comm _ (range I)]
  simp [Set.preimage_comp]
/-
**ModelWithCorners.extendCoordChange_target** 是 Mathlib 中的一个引理，位于命名空间 `ModelWith
Corners`。
形式化陈述：extendCoordChange_target : (I.extendCoordChange e e').target = I '' (e.sym
m ≫ₕ e').target
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.symm_source`：symm_source : e.symm.source = e.target
· 使用定理 `OpenPartialHomeomorph.symm_source`：symm_source : e.symm.source = e.targe
t
· 使用引理 `ModelWithCorners.extendCoordChange_source`：extendCoordChange_source : (I
.extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source
-/
lemma extendCoordChange_target :
    (I.extendCoordChange e e').target = I '' (e.symm ≫ₕ e').target := by
  rw [← PartialEquiv.symm_source, ← OpenPartialHomeomorph.symm_source]
  exact I.extendCoordChange_source
/-
**ModelWithCorners._root_.OpenPartialHomeomorph.extend_image_source_inter** 是 Ma
thlib 中的一个引理，位于命名空间 `ModelWithCorners`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.OpenPartialHomeomorph.extend_image_source_inter :
    f.extend I '' (f.source ∩ f'.source) = (I.extendCoordChange f f').source := by
  simp_rw [I.extendCoordChange_source, f.extend_coe, image_comp I f,
    OpenPartialHomeomorph.trans_source'', OpenPartialHomeomorph.symm_symm,
    OpenPartialHomeomorph.symm_target]
/-
**ModelWithCorners.extendCoordChange_source_mem_nhdsWithin** 是 Mathlib 中的一个引理，位于
命名空间 `ModelWithCorners`。
形式化陈述：extendCoordChange_source_mem_nhdsWithin {x : E} (hx : x in (I.extendCoordC
hange e e').source) : (I.extendCoordChange e e').source in 𝓝[range I] x
参数：hx : x in (I.extendCoordChange e e').source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.extendCoordChange_source`：extendCoordChange_source : (I
.extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source
· 使用定理 `ModelWithCorners.image_mem_nhdsWithin`：image_mem_nhdsWithin {x : H} {s :
 Set H} (hs : s in 𝓝 x) : I '' s in 𝓝[range I] I x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
lemma extendCoordChange_source_mem_nhdsWithin {x : E}
    (hx : x ∈ (I.extendCoordChange e e').source) :
    (I.extendCoordChange e e').source ∈ 𝓝[range I] x := by
  rw [I.extendCoordChange_source] at hx ⊢
  obtain ⟨x, hx, rfl⟩ := hx
  refine I.image_mem_nhdsWithin ?_
  exact (OpenPartialHomeomorph.open_source _).mem_nhds hx
/-
**ModelWithCorners.extendCoordChange_source_mem_nhdsWithin'** 是 Mathlib 中的一个引理，位
于命名空间 `ModelWithCorners`。
形式化陈述：extendCoordChange_source_mem_nhdsWithin' {x : M} (hxe : x in e.source) (hx
e' : x in e'.source) : (I.extendCoordChange e e').source in 𝓝[range I] e.extend 
I x
参数：hxe : x in e.source；hxe' : x in e'.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModelWithCorners.extendCoordChange_source_mem_nhdsWithin`：extendCoordCha
nge_source_mem_nhdsWithin {x : E} (hx : x in (I.extendCoordChange e e').source) 
: (I.extendCoordChange e e').source in 𝓝[range…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.extend_image_source_inter`：∀ {𝕜 : Type u_1} {E : T
ype u_2} {M : Type u_3} {H : Type u_4} [inst : NontriviallyNormedField 𝕜]   [ins
t_1 : NormedAddCommGroup E] [inst_2 :…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma extendCoordChange_source_mem_nhdsWithin' {x : M} (hxe : x ∈ e.source)
    (hxe' : x ∈ e'.source) :
    (I.extendCoordChange e e').source ∈ 𝓝[range I] e.extend I x := by
  apply extendCoordChange_source_mem_nhdsWithin
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxe, hxe'⟩
/-
**ModelWithCorners.uniqueDiffOn_extendCoordChange_source** 是 Mathlib 中的一个引理，位于命名
空间 `ModelWithCorners`。
形式化陈述：uniqueDiffOn_extendCoordChange_source : UniqueDiffOn 𝕜 (I.extendCoordChang
e e e').source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.extendCoordChange_source`：extendCoordChange_source : (I
.extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `ModelWithCorners.uniqueDiffOn_preimage`：uniqueDiffOn_preimage {s : Set H
} (hs : IsOpen s) : UniqueDiffOn 𝕜 (I.symm ⁻¹' s inter range I)
· 使用定理 `OpenPartialHomeomorph.isOpen_inter_preimage_symm`：isOpen_inter_preimage_
symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target inter e.symm ⁻¹' s)
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
lemma uniqueDiffOn_extendCoordChange_source : UniqueDiffOn 𝕜 (I.extendCoordChange e e').source := by
  rw [extendCoordChange_source, I.image_eq]
  exact I.uniqueDiffOn_preimage <| e.isOpen_inter_preimage_symm e'.open_source
/-
**ModelWithCorners.uniqueDiffOn_extendCoordChange_target** 是 Mathlib 中的一个引理，位于命名
空间 `ModelWithCorners`。
形式化陈述：uniqueDiffOn_extendCoordChange_target : UniqueDiffOn 𝕜 (I.extendCoordChang
e e e').target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ModelWithCorners.extendCoordChange_symm`：extendCoordChange_symm : (I.ext
endCoordChange e e').symm = I.extendCoordChange e' e
· 使用定理 `PartialEquiv.symm_target`：symm_target : e.symm.target = e.source
· 使用引理 `ModelWithCorners.uniqueDiffOn_extendCoordChange_source`：uniqueDiffOn_ext
endCoordChange_source : UniqueDiffOn 𝕜 (I.extendCoordChange e e').source
-/
lemma uniqueDiffOn_extendCoordChange_target : UniqueDiffOn 𝕜 (I.extendCoordChange e e').target := by
  rw [← extendCoordChange_symm, PartialEquiv.symm_target]
  exact uniqueDiffOn_extendCoordChange_source

open IsManifold

variable [ChartedSpace H M]
/-
**ModelWithCorners.contDiffOn_extendCoordChange** 是 Mathlib 中的一个引理，位于命名空间 `Model
WithCorners`。
形式化陈述：contDiffOn_extendCoordChange (he : e in maximalAtlas I n M) (he' : e' in m
aximalAtlas I n M) : ContDiffOn 𝕜 n (I.extendCoordChange e e') (I.extendCoordCha
nge e e').source
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I n M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.extendCoordChange_source`：extendCoordChange_source : (I
.extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source
· 使用定理 `ModelWithCorners.image_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `StructureGroupoid.compatible_of_mem_maximalAtlas`：StructureGroupoid.comp
atible_of_mem_maximalAtlas {e e' : OpenPartialHomeomorph M H} (he : e in G.maxim
alAtlas M) (he' : e' in G.maximalAtlas…
-/
lemma contDiffOn_extendCoordChange (he : e ∈ maximalAtlas I n M) (he' : e' ∈ maximalAtlas I n M) :
    ContDiffOn 𝕜 n (I.extendCoordChange e e') (I.extendCoordChange e e').source := by
  rw [I.extendCoordChange_source, I.image_eq]
  exact (StructureGroupoid.compatible_of_mem_maximalAtlas he he').1
/-
**ModelWithCorners.contDiffWithinAt_extendCoordChange** 是 Mathlib 中的一个引理，位于命名空间 
`ModelWithCorners`。
形式化陈述：contDiffWithinAt_extendCoordChange (he : e in maximalAtlas I n M) (he' : e
' in maximalAtlas I n M) {x : E} (hx : x in (I.extendCoordChange e e').source) :
 ContDiffWithinAt 𝕜 n (I.extendCoordChange e e') (range I) x
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I n M；hx : x in (I.exte
ndCoordChange e e').source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffWithinAt.mono_of_mem_nhdsWithin`：ContDiffWithinAt.mono_of_mem_nh
dsWithin (h : ContDiffWithinAt 𝕜 n f s x) {t : Set E} (hst : s in 𝓝[t] x) : Cont
DiffWithinAt 𝕜 n f t x
· 使用引理 `ModelWithCorners.contDiffOn_extendCoordChange`：contDiffOn_extendCoordCha
nge (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) : ContDiffOn
 𝕜 n (I.extendCoordChange e e') (I.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.extendCoordChange_source`：extendCoordChange_source : (I
.extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source
· 使用定理 `ModelWithCorners.image_mem_nhdsWithin`：image_mem_nhdsWithin {x : H} {s :
 Set H} (hs : s in 𝓝 x) : I '' s in 𝓝[range I] I x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `OpenPartialHomeomorph.open_source`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
lemma contDiffWithinAt_extendCoordChange (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I n M) {x : E} (hx : x ∈ (I.extendCoordChange e e').source) :
    ContDiffWithinAt 𝕜 n (I.extendCoordChange e e') (range I) x := by
  apply (I.contDiffOn_extendCoordChange he he' x hx).mono_of_mem_nhdsWithin
  rw [I.extendCoordChange_source] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := hx
  exact I.image_mem_nhdsWithin ((OpenPartialHomeomorph.open_source _).mem_nhds hz)
/-
**ModelWithCorners.contDiffWithinAt_extendCoordChange'** 是 Mathlib 中的一个引理，位于命名空间
 `ModelWithCorners`。
形式化陈述：contDiffWithinAt_extendCoordChange' (he : e in maximalAtlas I n M) (he' : 
e' in maximalAtlas I n M) {x : M} (hxe : x in e.source) (hxe' : x in e'.source) 
: ContDiffWithinAt 𝕜 n (I.extendCoordChange e e') (range I) (e.extend I x)
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I n M；hxe : x in e.sour
ce；hxe' : x in e'.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModelWithCorners.contDiffWithinAt_extendCoordChange`：contDiffWithinAt_ex
tendCoordChange (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) 
{x : E} (hx : x in (I.extendCoordChange e…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.extend_image_source_inter`：∀ {𝕜 : Type u_1} {E : T
ype u_2} {M : Type u_3} {H : Type u_4} [inst : NontriviallyNormedField 𝕜]   [ins
t_1 : NormedAddCommGroup E] [inst_2 :…
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma contDiffWithinAt_extendCoordChange' (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I n M) {x : M} (hxe : x ∈ e.source) (hxe' : x ∈ e'.source) :
    ContDiffWithinAt 𝕜 n (I.extendCoordChange e e') (range I) (e.extend I x) := by
  refine I.contDiffWithinAt_extendCoordChange he he' ?_
  rw [← OpenPartialHomeomorph.extend_image_source_inter]
  exact mem_image_of_mem _ ⟨hxe, hxe'⟩
/-
**ModelWithCorners.contDiffOn_extendCoordChange_symm** 是 Mathlib 中的一个引理，位于命名空间 `
ModelWithCorners`。
形式化陈述：contDiffOn_extendCoordChange_symm (he : e in maximalAtlas I n M) (he' : e'
 in maximalAtlas I n M) : ContDiffOn 𝕜 n (I.extendCoordChange e e').symm (I.exte
ndCoordChange e e').target
参数：he : e in maximalAtlas I n M；he' : e' in maximalAtlas I n M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModelWithCorners.contDiffOn_extendCoordChange`：contDiffOn_extendCoordCha
nge (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) : ContDiffOn
 𝕜 n (I.extendCoordChange e e') (I.…
-/
lemma contDiffOn_extendCoordChange_symm (he : e ∈ maximalAtlas I n M)
    (he' : e' ∈ maximalAtlas I n M) :
    ContDiffOn 𝕜 n (I.extendCoordChange e e').symm (I.extendCoordChange e e').target :=
  I.contDiffOn_extendCoordChange he' he
/-
**ModelWithCorners.isInvertible_fderivWithin_extendCoordChange** 是 Mathlib 中的一个引
理，位于命名空间 `ModelWithCorners`。
形式化陈述：isInvertible_fderivWithin_extendCoordChange (hn : n != 0) (he : e in maxim
alAtlas I n M) (he' : e' in maximalAtlas I n M) {x : E} (hx : x in (I.extendCoor
dChange e e').source) : ContinuousLinearMap.IsInvertible fderivWithin 𝕜 (I.exten
dCoordChange e e') (I.extendCoordChange e e').source x
参数：hn : n != 0；he : e in maximalAtlas I n M；he' : e' in maximalAtlas I n M；hx : 
x in (I.extendCoordChange e e').source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ModelWithCorners.contDiffOn_extendCoordChange`：contDiffOn_extendCoordCha
nge (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) : ContDiffOn
 𝕜 n (I.extendCoordChange e e') (I.…
· 使用引理 `ModelWithCorners.contDiffOn_extendCoordChange_symm`：contDiffOn_extendCoo
rdChange_symm (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) : 
ContDiffOn 𝕜 n (I.extendCoordChange e e'…
· 使用定理 `ContinuousLinearMap.IsInvertible.of_inverse`：∀ {R : Type u_1} {M : Type 
u_2} {M₂ : Type u_3} [inst : TopologicalSpace M] [inst_1 : TopologicalSpace M₂] 
  [inst_2 : Semiring R] [inst_3 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `fderivWithin_comp`：fderivWithin_comp {g : F -> G} {t : Set F} (hg : Diff
erentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsT
o f s t…
· 使用定理 `ContDiffWithinAt.differentiableWithinAt`：ContDiffWithinAt.differentiable
WithinAt (h : ContDiffWithinAt 𝕜 n f s x) (hn : n != 0) : DifferentiableWithinAt
 𝕜 f s x
· 使用定理 `PartialEquiv.mapsTo_symm`：mapsTo_symm : MapsTo e.symm e.target e.source
· 使用引理 `ModelWithCorners.uniqueDiffOn_extendCoordChange_source`：uniqueDiffOn_ext
endCoordChange_source : UniqueDiffOn 𝕜 (I.extendCoordChange e e').source
· 使用定理 `fderivWithin_congr'`：fderivWithin_congr' (hs : EqOn f₁ f s) (hx : x in s
) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x
· 使用定理 `Set.RightInvOn.eqOn`：eqOn (h : RightInvOn f' f t) : EqOn (f ∘ f') id t
· 使用定理 `PartialEquiv.rightInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqu
iv α β), Set.RightInvOn (↑e.symm) (↑e) e.target
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
· 使用定理 `PartialEquiv.mapsTo`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.MapsTo (↑e) e.source e.target
· 使用定理 `Set.LeftInvOn.eqOn`：eqOn (h : LeftInvOn f' f s) : EqOn (f' ∘ f) id s
· 使用定理 `PartialEquiv.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqui
v α β), Set.LeftInvOn (↑e.symm) (↑e) e.source
-/
lemma isInvertible_fderivWithin_extendCoordChange (hn : n ≠ 0)
    (he : e ∈ maximalAtlas I n M) (he' : e' ∈ maximalAtlas I n M)
    {x : E} (hx : x ∈ (I.extendCoordChange e e').source) :
    ContinuousLinearMap.IsInvertible <|
      fderivWithin 𝕜 (I.extendCoordChange e e') (I.extendCoordChange e e').source x := by
  set φ := I.extendCoordChange e e'
  have hφ : ContDiffOn 𝕜 n φ φ.source := I.contDiffOn_extendCoordChange he he'
  have hφ' : ContDiffOn 𝕜 n φ.symm φ.target := I.contDiffOn_extendCoordChange_symm he he'
  refine .of_inverse (g := (fderivWithin 𝕜 φ.symm φ.target (φ x))) ?_ ?_
  · rw [← φ.left_inv hx, φ.right_inv (φ.map_source hx), ← fderivWithin_comp,
      fderivWithin_congr' φ.rightInvOn.eqOn (φ.map_source hx), fderivWithin_id]
    · exact I.uniqueDiffOn_extendCoordChange_source _ (φ.map_source hx)
    · exact (φ.left_inv hx ▸ ((hφ _ hx).differentiableWithinAt hn) :)
    · exact (hφ' _ (φ.map_source hx)).differentiableWithinAt hn
    · exact φ.mapsTo_symm
    · exact I.uniqueDiffOn_extendCoordChange_source _ (φ.map_source hx)
  · rw [← fderivWithin_comp, fderivWithin_congr' φ.leftInvOn.eqOn hx, fderivWithin_id]
    · exact I.uniqueDiffOn_extendCoordChange_source _ hx
    · exact (hφ' _ (φ.map_source hx)).differentiableWithinAt hn
    · exact (hφ _ hx).differentiableWithinAt hn
    · exact φ.mapsTo
    · exact I.uniqueDiffOn_extendCoordChange_source _ hx

end ModelWithCorners

namespace OpenPartialHomeomorph

@[deprecated (since := "2026-02-16")]
alias extend_coord_change_source := ModelWithCorners.extendCoordChange_source

@[deprecated (since := "2026-02-16")]
alias extend_coord_change_source_mem_nhdsWithin :=
  ModelWithCorners.extendCoordChange_source_mem_nhdsWithin

@[deprecated (since := "2026-02-16")]
alias extend_coord_change_source_mem_nhdsWithin' :=
  ModelWithCorners.extendCoordChange_source_mem_nhdsWithin'

@[deprecated (since := "2026-02-16")]
alias contDiffOn_extend_coord_change := ModelWithCorners.contDiffOn_extendCoordChange

@[deprecated (since := "2026-02-16")]
alias contDiffWithinAt_extend_coord_change := ModelWithCorners.contDiffWithinAt_extendCoordChange

@[deprecated (since := "2026-02-16")]
alias contDiffWithinAt_extend_coord_change' := ModelWithCorners.contDiffWithinAt_extendCoordChange'

end OpenPartialHomeomorph

open OpenPartialHomeomorph

variable [ChartedSpace H M] [ChartedSpace H' M']

variable (I) in
/-- The preferred extended chart on a manifold with corners around a point `x`, from a neighborhood
of `x` to the model vector space. -/
@[simp, mfld_simps]
/-
**extChartAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：extChartAt (x : M) : PartialEquiv M E
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preferred extended chart on a manifold with corners around a point `x`, from
 a neighborhood
of `x` to the model vector space.
-/
def extChartAt (x : M) : PartialEquiv M E :=
  (chartAt H x).extend I
/-
**extChartAt_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_coe (x : M) : ⇑(extChartAt I x) = I ∘ chartAt H x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extChartAt_coe (x : M) : ⇑(extChartAt I x) = I ∘ chartAt H x :=
  rfl
/-
**extChartAt_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_coe_symm (x : M) : ⇑(extChartAt I x).symm = (chartAt H x).symm 
∘ I.symm
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extChartAt_coe_symm (x : M) : ⇑(extChartAt I x).symm = (chartAt H x).symm ∘ I.symm :=
  rfl

variable (I) in
/-
**extChartAt_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_source (x : M) : (extChartAt I x).source = (chartAt H x).source
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.extend_source`：extend_source : (f.extend I).source
 = f.source
-/
theorem extChartAt_source (x : M) : (extChartAt I x).source = (chartAt H x).source :=
  extend_source _
/-
**isOpen_extChartAt_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_extChartAt_source (x : M) : IsOpen (extChartAt I x).source
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.isOpen_extend_source`：isOpen_extend_source : IsOpe
n (f.extend I).source
-/
theorem isOpen_extChartAt_source (x : M) : IsOpen (extChartAt I x).source :=
  isOpen_extend_source _
/-
**mem_extChartAt_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_extChartAt_source (x : M) : x in (extChartAt I x).source
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
theorem mem_extChartAt_source (x : M) : x ∈ (extChartAt I x).source := by
  simp only [extChartAt_source, mem_chart_source]
/-
**mem_extChartAt_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_extChartAt_target (x : M) : extChartAt I x x in (extChartAt I x).targe
t
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem mem_extChartAt_target (x : M) : extChartAt I x x ∈ (extChartAt I x).target :=
  (extChartAt I x).map_source <| mem_extChartAt_source _

variable (I) in
/-
**extChartAt_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_target (x : M) : (extChartAt I x).target = I.symm ⁻¹' (chartAt 
H x).target inter range I
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.extend_target`：extend_target : (f.extend I).target
 = I.symm ⁻¹' f.target inter range I
-/
theorem extChartAt_target (x : M) :
    (extChartAt I x).target = I.symm ⁻¹' (chartAt H x).target ∩ range I :=
  extend_target _
/-
**uniqueDiffOn_extChartAt_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffOn_extChartAt_target (x : M) : UniqueDiffOn 𝕜 (extChartAt I x).t
arget
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_target`：extChartAt_target (x : M) : (extChartAt I x).target =
 I.symm ⁻¹' (chartAt H x).target inter range I
· 使用定理 `ModelWithCorners.uniqueDiffOn_preimage`：uniqueDiffOn_preimage {s : Set H
} (hs : IsOpen s) : UniqueDiffOn 𝕜 (I.symm ⁻¹' s inter range I)
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem uniqueDiffOn_extChartAt_target (x : M) : UniqueDiffOn 𝕜 (extChartAt I x).target := by
  rw [extChartAt_target]
  exact I.uniqueDiffOn_preimage (chartAt H x).open_target
/-
**uniqueDiffWithinAt_extChartAt_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：uniqueDiffWithinAt_extChartAt_target (x : M) : UniqueDiffWithinAt 𝕜 (extCh
artAt I x).target (extChartAt I x x)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `uniqueDiffOn_extChartAt_target`：uniqueDiffOn_extChartAt_target (x : M) :
 UniqueDiffOn 𝕜 (extChartAt I x).target
· 使用定理 `mem_extChartAt_target`：mem_extChartAt_target (x : M) : extChartAt I x x 
in (extChartAt I x).target
-/
theorem uniqueDiffWithinAt_extChartAt_target (x : M) :
    UniqueDiffWithinAt 𝕜 (extChartAt I x).target (extChartAt I x x) :=
  uniqueDiffOn_extChartAt_target x _ <| mem_extChartAt_target x
/-
**extChartAt_to_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_to_inv (x : M) : (extChartAt I x).symm ((extChartAt I x) x) = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem extChartAt_to_inv (x : M) : (extChartAt I x).symm ((extChartAt I x) x) = x :=
  (extChartAt I x).left_inv (mem_extChartAt_source x)
/-
**mapsTo_extChartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mapsTo_extChartAt {x : M} (hs : s subseteq (chartAt H x).source) : MapsTo 
(extChartAt I x) s ((extChartAt I x).symm ⁻¹' s inter range I)
参数：hs : s subseteq (chartAt H x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.mapsTo_extend`：mapsTo_extend (hs : s subseteq f.so
urce) : MapsTo (f.extend I) s ((f.extend I).symm ⁻¹' s inter range I)
-/
theorem mapsTo_extChartAt {x : M} (hs : s ⊆ (chartAt H x).source) :
    MapsTo (extChartAt I x) s ((extChartAt I x).symm ⁻¹' s ∩ range I) :=
  mapsTo_extend _ hs
/-
**extChartAt_source_mem_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_source_mem_nhds' {x x' : M} (h : x' in (extChartAt I x).source)
 : (extChartAt I x).source in 𝓝 x'
参数：h : x' in (extChartAt I x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.extend_source_mem_nhds`：extend_source_mem_nhds {x 
: M} (h : x in f.source) : (f.extend I).source in 𝓝 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
theorem extChartAt_source_mem_nhds' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    (extChartAt I x).source ∈ 𝓝 x' :=
  extend_source_mem_nhds _ <| by rwa [← extChartAt_source I]
/-
**extChartAt_source_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_source_mem_nhds (x : M) : (extChartAt I x).source in 𝓝 x
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extChartAt_source_mem_nhds'`：extChartAt_source_mem_nhds' {x x' : M} (h :
 x' in (extChartAt I x).source) : (extChartAt I x).source in 𝓝 x'
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem extChartAt_source_mem_nhds (x : M) : (extChartAt I x).source ∈ 𝓝 x :=
  extChartAt_source_mem_nhds' (mem_extChartAt_source x)
/-
**extChartAt_source_mem_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_source_mem_nhdsWithin' {x x' : M} (h : x' in (extChartAt I x).s
ource) : (extChartAt I x).source in 𝓝[s] x'
参数：h : x' in (extChartAt I x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `extChartAt_source_mem_nhds'`：extChartAt_source_mem_nhds' {x x' : M} (h :
 x' in (extChartAt I x).source) : (extChartAt I x).source in 𝓝 x'
-/
theorem extChartAt_source_mem_nhdsWithin' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    (extChartAt I x).source ∈ 𝓝[s] x' :=
  mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds' h)
/-
**extChartAt_source_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_source_mem_nhdsWithin (x : M) : (extChartAt I x).source in 𝓝[s]
 x
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_nhdsWithin_of_mem_nhds`：mem_nhdsWithin_of_mem_nhds {s t : Set α} {a 
: α} (h : s in 𝓝 a) : s in 𝓝[t] a
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
-/
theorem extChartAt_source_mem_nhdsWithin (x : M) : (extChartAt I x).source ∈ 𝓝[s] x :=
  mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds x)
/-
**continuousOn_extChartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_extChartAt (x : M) : ContinuousOn (extChartAt I x) (extChartA
t I x).source
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.continuousOn_extend`：continuousOn_extend : Continu
ousOn (f.extend I) (f.extend I).source
-/
theorem continuousOn_extChartAt (x : M) : ContinuousOn (extChartAt I x) (extChartAt I x).source :=
  continuousOn_extend _
/-
**continuousAt_extChartAt'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_extChartAt' {x x' : M} (h : x' in (extChartAt I x).source) : 
ContinuousAt (extChartAt I x) x'
参数：h : x' in (extChartAt I x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.continuousAt_extend`：continuousAt_extend {x : M} (
h : x in f.source) : ContinuousAt (f.extend I) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
theorem continuousAt_extChartAt' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    ContinuousAt (extChartAt I x) x' :=
  continuousAt_extend _ <| by rwa [← extChartAt_source I]
/-
**continuousAt_extChartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_extChartAt (x : M) : ContinuousAt (extChartAt I x) x
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_extChartAt'`：continuousAt_extChartAt' {x x' : M} (h : x' in
 (extChartAt I x).source) : ContinuousAt (extChartAt I x) x'
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem continuousAt_extChartAt (x : M) : ContinuousAt (extChartAt I x) x :=
  continuousAt_extChartAt' (mem_extChartAt_source x)
/-
**map_extChartAt_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_nhds' {x y : M} (hy : y in (extChartAt I x).source) : map (
extChartAt I x) (𝓝 y) = 𝓝[range I] extChartAt I x y
参数：hy : y in (extChartAt I x).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_extend_nhds`：map_extend_nhds {x : M} (hy : x i
n f.source) : map (f.extend I) (𝓝 x) = 𝓝[range I] f.extend I x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
theorem map_extChartAt_nhds' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝 y) = 𝓝[range I] extChartAt I x y :=
  map_extend_nhds _ <| by rwa [← extChartAt_source I]
/-
**map_extChartAt_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_nhds (x : M) : map (extChartAt I x) (𝓝 x) = 𝓝[range I] extC
hartAt I x x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_extChartAt_nhds'`：map_extChartAt_nhds' {x y : M} (hy : y in (extChar
tAt I x).source) : map (extChartAt I x) (𝓝 y) = 𝓝[range I] extChartAt I x y
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem map_extChartAt_nhds (x : M) : map (extChartAt I x) (𝓝 x) = 𝓝[range I] extChartAt I x x :=
  map_extChartAt_nhds' <| mem_extChartAt_source x
/-
**map_extChartAt_nhds_of_boundaryless** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_nhds_of_boundaryless [I.Boundaryless] (x : M) : map (extCha
rtAt I x) (𝓝 x) = 𝓝 (extChartAt I x x)
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `OpenPartialHomeomorph.map_extend_nhds_of_boundaryless`：map_extend_nhds_o
f_boundaryless [I.Boundaryless] {x : M} (hx : x in f.source) : map (f.extend I) 
(𝓝 x) = 𝓝 (f.extend I x)
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
-/
theorem map_extChartAt_nhds_of_boundaryless [I.Boundaryless] (x : M) :
    map (extChartAt I x) (𝓝 x) = 𝓝 (extChartAt I x x) := by
  rw [extChartAt]
  exact map_extend_nhds_of_boundaryless (chartAt H x) (mem_chart_source H x)
/-
**extChartAt_image_nhds_mem_nhds_of_mem_interior_range** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：extChartAt_image_nhds_mem_nhds_of_mem_interior_range {x y} (hx : y in (ext
ChartAt I x).source) (h'x : extChartAt I x y in interior (range I)) {s : Set M} 
(h : s in 𝓝 y) : (extChartAt I x) '' s in 𝓝 (extChartAt I x y)
参数：hx : y in (extChartAt I x).source；h'x : extChartAt I x y in interior (range I
)；h : s in 𝓝 y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `OpenPartialHomeomorph.extend_image_nhds_mem_nhds_of_mem_interior_range`：
extend_image_nhds_mem_nhds_of_mem_interior_range {x} (hx : x in f.source) (h'x :
 f.extend I x in interior (range I)) {s : Set M} (h : s in 𝓝…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem extChartAt_image_nhds_mem_nhds_of_mem_interior_range {x y}
    (hx : y ∈ (extChartAt I x).source)
    (h'x : extChartAt I x y ∈ interior (range I)) {s : Set M} (h : s ∈ 𝓝 y) :
    (extChartAt I x) '' s ∈ 𝓝 (extChartAt I x y) := by
  rw [extChartAt]
  exact extend_image_nhds_mem_nhds_of_mem_interior_range _ (by simpa using hx) h'x h

variable {x} in
/-
**extChartAt_image_nhds_mem_nhds_of_boundaryless** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_image_nhds_mem_nhds_of_boundaryless [I.Boundaryless] {x : M} (h
x : s in 𝓝 x) : extChartAt I x '' s in 𝓝 (extChartAt I x x)
参数：hx : s in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt.eq_1`：∀ {𝕜 : Type u_1} {E : Type u_2} {M : Type u_3} {H : Typ
e u_4} [inst : NontriviallyNormedField 𝕜]   [inst_1 : NormedAddCommGroup E] [ins
t_2 :…
· 使用定理 `OpenPartialHomeomorph.extend_image_nhds_mem_nhds_of_boundaryless`：extend
_image_nhds_mem_nhds_of_boundaryless [I.Boundaryless] {x} (hx : x in f.source) {
s : Set M} (h : s in 𝓝 x) : (f.extend I) '' s in 𝓝 ((f…
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
-/
theorem extChartAt_image_nhds_mem_nhds_of_boundaryless [I.Boundaryless]
    {x : M} (hx : s ∈ 𝓝 x) : extChartAt I x '' s ∈ 𝓝 (extChartAt I x x) := by
  rw [extChartAt]
  exact extend_image_nhds_mem_nhds_of_boundaryless _ (mem_chart_source H x) hx
/-
**extChartAt_target_mem_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_target_mem_nhdsWithin' {x y : M} (hy : y in (extChartAt I x).so
urce) : (extChartAt I x).target in 𝓝[range I] extChartAt I x y
参数：hy : y in (extChartAt I x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.extend_target_mem_nhdsWithin`：extend_target_mem_nh
dsWithin {y : M} (hy : y in f.source) : (f.extend I).target in 𝓝[range I] f.exte
nd I y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
theorem extChartAt_target_mem_nhdsWithin' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    (extChartAt I x).target ∈ 𝓝[range I] extChartAt I x y :=
  extend_target_mem_nhdsWithin _ <| by rwa [← extChartAt_source I]
/-
**extChartAt_target_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_target_mem_nhdsWithin (x : M) : (extChartAt I x).target in 𝓝[ra
nge I] extChartAt I x x
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extChartAt_target_mem_nhdsWithin'`：extChartAt_target_mem_nhdsWithin' {x 
y : M} (hy : y in (extChartAt I x).source) : (extChartAt I x).target in 𝓝[range 
I] extChartAt I x y
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem extChartAt_target_mem_nhdsWithin (x : M) :
    (extChartAt I x).target ∈ 𝓝[range I] extChartAt I x x :=
  extChartAt_target_mem_nhdsWithin' (mem_extChartAt_source x)
/-
**extChartAt_target_mem_nhdsWithin_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_target_mem_nhdsWithin_of_mem {x : M} {y : E} (hy : y in (extCha
rtAt I x).target) : (extChartAt I x).target in 𝓝[range I] y
参数：hy : y in (extChartAt I x).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `extChartAt_target_mem_nhdsWithin'`：extChartAt_target_mem_nhdsWithin' {x 
y : M} (hy : y in (extChartAt I x).source) : (extChartAt I x).target in 𝓝[range 
I] extChartAt I x y
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source
-/
theorem extChartAt_target_mem_nhdsWithin_of_mem {x : M} {y : E} (hy : y ∈ (extChartAt I x).target) :
    (extChartAt I x).target ∈ 𝓝[range I] y := by
  rw [← (extChartAt I x).right_inv hy]
  apply extChartAt_target_mem_nhdsWithin'
  exact (extChartAt I x).map_target hy
/-
**extChartAt_target_union_compl_range_mem_nhds_of_mem** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：extChartAt_target_union_compl_range_mem_nhds_of_mem {y : E} {x : M} (hy : 
y in (extChartAt I x).target) : (extChartAt I x).target union (range I)ᶜ in 𝓝 y
参数：hy : y in (extChartAt I x).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `extChartAt_target_mem_nhdsWithin_of_mem`：extChartAt_target_mem_nhdsWithi
n_of_mem {x : M} {y : E} (hy : y in (extChartAt I x).target) : (extChartAt I x).
target in 𝓝[range I] y
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
-/
theorem extChartAt_target_union_compl_range_mem_nhds_of_mem {y : E} {x : M}
    (hy : y ∈ (extChartAt I x).target) : (extChartAt I x).target ∪ (range I)ᶜ ∈ 𝓝 y := by
  rw [← nhdsWithin_univ, ← union_compl_self (range I), nhdsWithin_union]
  exact Filter.union_mem_sup (extChartAt_target_mem_nhdsWithin_of_mem hy) self_mem_nhdsWithin

/-- If we're boundaryless, `extChartAt` has open target -/
/-
**isOpen_extChartAt_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_extChartAt_target [I.Boundaryless] (x : M) : IsOpen (extChartAt I x
).target
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `extChartAt_target`：extChartAt_target (x : M) : (extChartAt I x).target =
 I.symm ⁻¹' (chartAt H x).target inter range I
· 使用定理 `ModelWithCorners.range_eq_univ`：ModelWithCorners.range_eq_univ {𝕜 : Type
*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜
 E] {H : Type*} [Top…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `ModelWithCorners.continuous_symm`：continuous_symm : Continuous I.symm
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…

--- 原说明 ---
If we're boundaryless, `extChartAt` has open target
-/
theorem isOpen_extChartAt_target [I.Boundaryless] (x : M) : IsOpen (extChartAt I x).target := by
  simp_rw [extChartAt_target, I.range_eq_univ, inter_univ]
  exact (OpenPartialHomeomorph.open_target _).preimage I.continuous_symm

/-- If we're boundaryless, `(extChartAt I x).target` is a neighborhood of the key point -/
/-
**extChartAt_target_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_target_mem_nhds [I.Boundaryless] (x : M) : (extChartAt I x).tar
get in 𝓝 (extChartAt I x x)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.range_eq_univ`：ModelWithCorners.range_eq_univ {𝕜 : Type
*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜
 E] {H : Type*} [Top…
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `extChartAt_target_mem_nhdsWithin`：extChartAt_target_mem_nhdsWithin (x : 
M) : (extChartAt I x).target in 𝓝[range I] extChartAt I x x

--- 原说明 ---
If we're boundaryless, `(extChartAt I x).target` is a neighborhood of the key po
int
-/
theorem extChartAt_target_mem_nhds [I.Boundaryless] (x : M) :
    (extChartAt I x).target ∈ 𝓝 (extChartAt I x x) := by
  convert! extChartAt_target_mem_nhdsWithin x
  simp only [I.range_eq_univ, nhdsWithin_univ]

/-- If we're boundaryless, `(extChartAt I x).target` is a neighborhood of any of its points -/
/-
**extChartAt_target_mem_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_target_mem_nhds' [I.Boundaryless] {x : M} {y : E} (m : y in (ex
tChartAt I x).target) : (extChartAt I x).target in 𝓝 y
参数：m : y in (extChartAt I x).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_extChartAt_target`：isOpen_extChartAt_target [I.Boundaryless] (x :
 M) : IsOpen (extChartAt I x).target

--- 原说明 ---
If we're boundaryless, `(extChartAt I x).target` is a neighborhood of any of its
 points
-/
theorem extChartAt_target_mem_nhds' [I.Boundaryless] {x : M} {y : E}
    (m : y ∈ (extChartAt I x).target) : (extChartAt I x).target ∈ 𝓝 y :=
  (isOpen_extChartAt_target x).mem_nhds m
/-
**extChartAt_target_subset_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_target_subset_range (x : M) : (extChartAt I x).target subseteq 
range I
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
-/
theorem extChartAt_target_subset_range (x : M) : (extChartAt I x).target ⊆ range I := by
  simp only [mfld_simps]

/-- Around the image of a point in the source, the neighborhoods are the same
within `(extChartAt I x).target` and within `range I`. -/
/-
**nhdsWithin_extChartAt_target_eq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_extChartAt_target_eq' {x y : M} (hy : y in (extChartAt I x).sou
rce) : 𝓝[(extChartAt I x).target] extChartAt I x y = 𝓝[range I] extChartAt I x y
参数：hy : y in (extChartAt I x).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.nhdsWithin_extend_target_eq`：nhdsWithin_extend_tar
get_eq {y : M} (hy : y in f.source) : 𝓝[(f.extend I).target] f.extend I y = 𝓝[ra
nge I] f.extend I y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source

--- 原说明 ---
Around the image of a point in the source, the neighborhoods are the same
within `(extChartAt I x).target` and within `range I`.
-/
theorem nhdsWithin_extChartAt_target_eq' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    𝓝[(extChartAt I x).target] extChartAt I x y = 𝓝[range I] extChartAt I x y :=
  nhdsWithin_extend_target_eq _ <| by rwa [← extChartAt_source I]

/-- Around a point in the target, the neighborhoods are the same within `(extChartAt I x).target`
and within `range I`. -/
/-
**nhdsWithin_extChartAt_target_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_extChartAt_target_eq_of_mem {x : M} {z : E} (hz : z in (extChar
tAt I x).target) : 𝓝[(extChartAt I x).target] z = 𝓝[range I] z
参数：hz : z in (extChartAt I x).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `nhdsWithin_extChartAt_target_eq'`：nhdsWithin_extChartAt_target_eq' {x y 
: M} (hy : y in (extChartAt I x).source) : 𝓝[(extChartAt I x).target] extChartAt
 I x y = 𝓝[range I] ex…
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source

--- 原说明 ---
Around a point in the target, the neighborhoods are the same within `(extChartAt
 I x).target`
and within `range I`.
-/
theorem nhdsWithin_extChartAt_target_eq_of_mem {x : M} {z : E} (hz : z ∈ (extChartAt I x).target) :
    𝓝[(extChartAt I x).target] z = 𝓝[range I] z := by
  rw [← PartialEquiv.right_inv (extChartAt I x) hz]
  exact nhdsWithin_extChartAt_target_eq' ((extChartAt I x).map_target hz)

/-- Around the image of the base point, the neighborhoods are the same
within `(extChartAt I x).target` and within `range I`. -/
/-
**nhdsWithin_extChartAt_target_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nhdsWithin_extChartAt_target_eq (x : M) : 𝓝[(extChartAt I x).target] (extC
hartAt I x) x = 𝓝[range I] (extChartAt I x) x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nhdsWithin_extChartAt_target_eq'`：nhdsWithin_extChartAt_target_eq' {x y 
: M} (hy : y in (extChartAt I x).source) : 𝓝[(extChartAt I x).target] extChartAt
 I x y = 𝓝[range I] ex…
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source

--- 原说明 ---
Around the image of the base point, the neighborhoods are the same
within `(extChartAt I x).target` and within `range I`.
-/
theorem nhdsWithin_extChartAt_target_eq (x : M) :
    𝓝[(extChartAt I x).target] (extChartAt I x) x = 𝓝[range I] (extChartAt I x) x :=
  nhdsWithin_extChartAt_target_eq' (mem_extChartAt_source x)

/-- Around the image of a point in the source, `(extChartAt I x).target` and `range I`
coincide locally. -/
/-
**extChartAt_target_eventuallyEq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_target_eventuallyEq' {x y : M} (hy : y in (extChartAt I x).sour
ce) : (extChartAt I x).target =ᶠ[𝓝 (extChartAt I x y)] range I
参数：hy : y in (extChartAt I x).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用定理 `nhdsWithin_extChartAt_target_eq'`：nhdsWithin_extChartAt_target_eq' {x y 
: M} (hy : y in (extChartAt I x).source) : 𝓝[(extChartAt I x).target] extChartAt
 I x y = 𝓝[range I] ex…

--- 原说明 ---
Around the image of a point in the source, `(extChartAt I x).target` and `range 
I`
coincide locally.
-/
theorem extChartAt_target_eventuallyEq' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    (extChartAt I x).target =ᶠ[𝓝 (extChartAt I x y)] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq' hy)

/-- Around a point in the target, `(extChartAt I x).target` and `range I` coincide locally. -/
/-
**extChartAt_target_eventuallyEq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_target_eventuallyEq_of_mem {x : M} {z : E} (hz : z in (extChart
At I x).target) : (extChartAt I x).target =ᶠ[𝓝 z] range I
参数：hz : z in (extChartAt I x).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用定理 `nhdsWithin_extChartAt_target_eq_of_mem`：nhdsWithin_extChartAt_target_eq_
of_mem {x : M} {z : E} (hz : z in (extChartAt I x).target) : 𝓝[(extChartAt I x).
target] z = 𝓝[range I] z

--- 原说明 ---
Around a point in the target, `(extChartAt I x).target` and `range I` coincide l
ocally.
-/
theorem extChartAt_target_eventuallyEq_of_mem {x : M} {z : E} (hz : z ∈ (extChartAt I x).target) :
    (extChartAt I x).target =ᶠ[𝓝 z] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq_of_mem hz)

/-- Around the image of the base point, `(extChartAt I x).target` and `range I` coincide locally. -/
/-
**extChartAt_target_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_target_eventuallyEq {x : M} : (extChartAt I x).target =ᶠ[𝓝 (ext
ChartAt I x x)] range I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用定理 `nhdsWithin_extChartAt_target_eq`：nhdsWithin_extChartAt_target_eq (x : M)
 : 𝓝[(extChartAt I x).target] (extChartAt I x) x = 𝓝[range I] (extChartAt I x) x

--- 原说明 ---
Around the image of the base point, `(extChartAt I x).target` and `range I` coin
cide locally.
-/
theorem extChartAt_target_eventuallyEq {x : M} :
    (extChartAt I x).target =ᶠ[𝓝 (extChartAt I x x)] range I :=
  nhdsWithin_eq_iff_eventuallyEq.1 (nhdsWithin_extChartAt_target_eq x)
/-
**continuousAt_extChartAt_symm''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_extChartAt_symm'' {x : M} {y : E} (h : y in (extChartAt I x).
target) : ContinuousAt (extChartAt I x).symm y
参数：h : y in (extChartAt I x).target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.continuousAt_extend_symm'`：continuousAt_extend_sym
m' {x : E} (h : x in (f.extend I).target) : ContinuousAt (f.extend I).symm x
-/
theorem continuousAt_extChartAt_symm'' {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    ContinuousAt (extChartAt I x).symm y :=
  continuousAt_extend_symm' _ h
/-
**continuousAt_extChartAt_symm'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_extChartAt_symm' {x x' : M} (h : x' in (extChartAt I x).sourc
e) : ContinuousAt (extChartAt I x).symm (extChartAt I x x')
参数：h : x' in (extChartAt I x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_extChartAt_symm''`：continuousAt_extChartAt_symm'' {x : M} {
y : E} (h : y in (extChartAt I x).target) : ContinuousAt (extChartAt I x).symm y
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
-/
theorem continuousAt_extChartAt_symm' {x x' : M} (h : x' ∈ (extChartAt I x).source) :
    ContinuousAt (extChartAt I x).symm (extChartAt I x x') :=
  continuousAt_extChartAt_symm'' <| (extChartAt I x).map_source h
/-
**continuousAt_extChartAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_extChartAt_symm (x : M) : ContinuousAt (extChartAt I x).symm 
((extChartAt I x) x)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousAt_extChartAt_symm'`：continuousAt_extChartAt_symm' {x x' : M} 
(h : x' in (extChartAt I x).source) : ContinuousAt (extChartAt I x).symm (extCha
rtAt I x x')
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem continuousAt_extChartAt_symm (x : M) :
    ContinuousAt (extChartAt I x).symm ((extChartAt I x) x) :=
  continuousAt_extChartAt_symm' (mem_extChartAt_source x)
/-
**continuousOn_extChartAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_extChartAt_symm (x : M) : ContinuousOn (extChartAt I x).symm 
(extChartAt I x).target
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.continuousWithinAt`：ContinuousAt.continuousWithinAt (h : Co
ntinuousAt f x) : ContinuousWithinAt f s x
· 使用定理 `continuousAt_extChartAt_symm''`：continuousAt_extChartAt_symm'' {x : M} {
y : E} (h : y in (extChartAt I x).target) : ContinuousAt (extChartAt I x).symm y
-/
theorem continuousOn_extChartAt_symm (x : M) :
    ContinuousOn (extChartAt I x).symm (extChartAt I x).target :=
  fun _y hy => (continuousAt_extChartAt_symm'' hy).continuousWithinAt
/-
**extChartAt_target_subset_closure_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：extChartAt_target_subset_closure_interior {x : M} : (extChartAt I x).targe
t subseteq closure (interior (extChartAt I x).target)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `extChartAt_target_union_compl_range_mem_nhds_of_mem`：extChartAt_target_u
nion_compl_range_mem_nhds_of_mem {y : E} {x : M} (hy : y in (extChartAt I x).tar
get) : (extChartAt I x).target union (ran…
· 使用定理 `ModelWithCorners.range_subset_closure_interior`：range_subset_closure_int
erior : range I subseteq closure (interior (range I))
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `Filter.EventuallyEq.mem_interior`：Filter.EventuallyEq.mem_interior {x : 
α} {s t : Set α} (hst : s =ᶠ[𝓝 x] t) (h : x in interior s) : x in interior t
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `extChartAt_target_eventuallyEq_of_mem`：extChartAt_target_eventuallyEq_of
_mem {x : M} {z : E} (hz : z in (extChartAt I x).target) : (extChartAt I x).targ
et =ᶠ[𝓝 z] range I
-/
lemma extChartAt_target_subset_closure_interior {x : M} :
    (extChartAt I x).target ⊆ closure (interior (extChartAt I x).target) := by
  intro y hy
  rw [mem_closure_iff_nhds]
  intro t ht
  have A : t ∩ ((extChartAt I x).target ∪ (range I)ᶜ) ∈ 𝓝 y :=
    inter_mem ht (extChartAt_target_union_compl_range_mem_nhds_of_mem hy)
  have B : y ∈ closure (interior (range I)) := by
    apply I.range_subset_closure_interior (extChartAt_target_subset_range x hy)
  obtain ⟨z, ⟨tz, h'z⟩, hz⟩ :
      (t ∩ ((extChartAt I x).target ∪ (range ↑I)ᶜ) ∩ interior (range I)).Nonempty :=
    mem_closure_iff_nhds.1 B _ A
  refine ⟨z, ⟨tz, ?_⟩⟩
  have h''z : z ∈ (extChartAt I x).target := by simpa [interior_subset hz] using h'z
  exact (extChartAt_target_eventuallyEq_of_mem h''z).symm.mem_interior hz

variable (I) in
/-
**interior_extChartAt_target_nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：interior_extChartAt_target_nonempty (x : M) : (interior (extChartAt I x).t
arget).Nonempty
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `extChartAt_target_subset_closure_interior`：extChartAt_target_subset_clos
ure_interior {x : M} : (extChartAt I x).target subseteq closure (interior (extCh
artAt I x).target)
· 使用定理 `mem_extChartAt_target`：mem_extChartAt_target (x : M) : extChartAt I x x 
in (extChartAt I x).target
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_empty`：closure_empty : closure (∅ : Set X) = ∅
-/
theorem interior_extChartAt_target_nonempty (x : M) :
    (interior (extChartAt I x).target).Nonempty := by
  by_contra! H
  have := extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := I) x)
  simp only [H, closure_empty, mem_empty_iff_false] at this
/-
**extChartAt_mem_closure_interior** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：extChartAt_mem_closure_interior {x₀ x : M} (hx : x in closure (interior s)
) (h'x : x in (extChartAt I x₀).source) : extChartAt I x₀ x in closure (interior
 ((extChartAt I x₀).symm ⁻¹' s inter (extChartAt I x₀).target))
参数：hx : x in closure (interior s)；h'x : x in (extChartAt I x₀).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_inter`：interior_inter : interior (s inter t) = interior s inter
 interior t
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `continuousAt_extChartAt'`：continuousAt_extChartAt' {x x' : M} (h : x' in
 (extChartAt I x).source) : ContinuousAt (extChartAt I x) x'
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_iff_nhds`：mem_closure_iff_nhds : x in closure s ↔ forall t i
n 𝓝 x, (t inter s).Nonempty
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `isOpen_extChartAt_source`：isOpen_extChartAt_source (x : M) : IsOpen (ext
ChartAt I x).source
· 使用定理 `continuousAt_extChartAt_symm'`：continuousAt_extChartAt_symm' {x x' : M} 
(h : x' in (extChartAt I x).source) : ContinuousAt (extChartAt I x).symm (extCha
rtAt I x x')
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `mem_interior_iff_mem_nhds`：mem_interior_iff_mem_nhds : x in interior s ↔
 s in 𝓝 x
· 使用引理 `extChartAt_target_subset_closure_interior`：extChartAt_target_subset_clos
ure_interior {x : M} : (extChartAt I x).target subseteq closure (interior (extCh
artAt I x).target)
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
-/
lemma extChartAt_mem_closure_interior {x₀ x : M}
    (hx : x ∈ closure (interior s)) (h'x : x ∈ (extChartAt I x₀).source) :
    extChartAt I x₀ x ∈
      closure (interior ((extChartAt I x₀).symm ⁻¹' s ∩ (extChartAt I x₀).target)) := by
  simp_rw [mem_closure_iff, interior_inter, ← inter_assoc]
  intro o o_open ho
  obtain ⟨y, ⟨yo, hy⟩, ys⟩ :
      ((extChartAt I x₀) ⁻¹' o ∩ (extChartAt I x₀).source ∩ interior s).Nonempty := by
    have : (extChartAt I x₀) ⁻¹' o ∈ 𝓝 x := by
      apply (continuousAt_extChartAt' h'x).preimage_mem_nhds (o_open.mem_nhds ho)
    refine (mem_closure_iff_nhds.1 hx) _ (inter_mem this ?_)
    apply (isOpen_extChartAt_source x₀).mem_nhds h'x
  have A : interior (↑(extChartAt I x₀).symm ⁻¹' s) ∈ 𝓝 (extChartAt I x₀ y) := by
    simp only [interior_mem_nhds]
    apply (continuousAt_extChartAt_symm' hy).preimage_mem_nhds
    simp only [hy, PartialEquiv.left_inv]
    exact mem_interior_iff_mem_nhds.mp ys
  have B : (extChartAt I x₀) y ∈ closure (interior (extChartAt I x₀).target) := by
    apply extChartAt_target_subset_closure_interior (x := x₀)
    exact (extChartAt I x₀).map_source hy
  exact mem_closure_iff_nhds.1 B _ (inter_mem (o_open.mem_nhds yo) A)
/-
**isOpen_extChartAt_preimage'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_extChartAt_preimage' (x : M) {s : Set E} (hs : IsOpen s) : IsOpen (
(extChartAt I x).source inter extChartAt I x ⁻¹' s)
参数：x : M；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.isOpen_extend_preimage'`：isOpen_extend_preimage' {
s : Set E} (hs : IsOpen s) : IsOpen ((f.extend I).source inter f.extend I ⁻¹' s)
-/
theorem isOpen_extChartAt_preimage' (x : M) {s : Set E} (hs : IsOpen s) :
    IsOpen ((extChartAt I x).source ∩ extChartAt I x ⁻¹' s) :=
  isOpen_extend_preimage' _ hs
/-
**isOpen_extChartAt_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpen_extChartAt_preimage (x : M) {s : Set E} (hs : IsOpen s) : IsOpen ((
chartAt H x).source inter extChartAt I x ⁻¹' s)
参数：x : M；hs : IsOpen s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
· 使用定理 `isOpen_extChartAt_preimage'`：isOpen_extChartAt_preimage' (x : M) {s : Se
t E} (hs : IsOpen s) : IsOpen ((extChartAt I x).source inter extChartAt I x ⁻¹' 
s)
-/
theorem isOpen_extChartAt_preimage (x : M) {s : Set E} (hs : IsOpen s) :
    IsOpen ((chartAt H x).source ∩ extChartAt I x ⁻¹' s) := by
  rw [← extChartAt_source I]
  exact isOpen_extChartAt_preimage' x hs
/-
**map_extChartAt_nhdsWithin_eq_image'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_nhdsWithin_eq_image' {x y : M} (hy : y in (extChartAt I x).
source) : map (extChartAt I x) (𝓝[s] y) = 𝓝[extChartAt I x '' ((extChartAt I x).
source inter s)] extChartAt I x y
参数：hy : y in (extChartAt I x).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin_eq_image`：map_extend_nhdsWit
hin_eq_image {y : M} (hy : y in f.source) : map (f.extend I) (𝓝[s] y) = 𝓝[f.exte
nd I '' ((f.extend I).source inter s)] f.e…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
theorem map_extChartAt_nhdsWithin_eq_image' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝[s] y) =
      𝓝[extChartAt I x '' ((extChartAt I x).source ∩ s)] extChartAt I x y :=
  map_extend_nhdsWithin_eq_image _ <| by rwa [← extChartAt_source I]
/-
**map_extChartAt_nhdsWithin_eq_image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_nhdsWithin_eq_image (x : M) : map (extChartAt I x) (𝓝[s] x)
 = 𝓝[extChartAt I x '' ((extChartAt I x).source inter s)] extChartAt I x x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_extChartAt_nhdsWithin_eq_image'`：map_extChartAt_nhdsWithin_eq_image'
 {x y : M} (hy : y in (extChartAt I x).source) : map (extChartAt I x) (𝓝[s] y) =
 𝓝[extChartAt I x '' ((ex…
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem map_extChartAt_nhdsWithin_eq_image (x : M) :
    map (extChartAt I x) (𝓝[s] x) =
      𝓝[extChartAt I x '' ((extChartAt I x).source ∩ s)] extChartAt I x x :=
  map_extChartAt_nhdsWithin_eq_image' (mem_extChartAt_source x)
/-
**map_extChartAt_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_nhdsWithin' {x y : M} (hy : y in (extChartAt I x).source) :
 map (extChartAt I x) (𝓝[s] y) = 𝓝[(extChartAt I x).symm ⁻¹' s inter range I] ex
tChartAt I x y
参数：hy : y in (extChartAt I x).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_extend_nhdsWithin`：map_extend_nhdsWithin {y : 
M} (hy : y in f.source) : map (f.extend I) (𝓝[s] y) = 𝓝[(f.extend I).symm ⁻¹' s 
inter range I] f.extend I y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
theorem map_extChartAt_nhdsWithin' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x) (𝓝[s] y) = 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x y :=
  map_extend_nhdsWithin _ <| by rwa [← extChartAt_source I]
/-
**map_extChartAt_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_nhdsWithin (x : M) : map (extChartAt I x) (𝓝[s] x) = 𝓝[(ext
ChartAt I x).symm ⁻¹' s inter range I] extChartAt I x x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_extChartAt_nhdsWithin'`：map_extChartAt_nhdsWithin' {x y : M} (hy : y
 in (extChartAt I x).source) : map (extChartAt I x) (𝓝[s] y) = 𝓝[(extChartAt I x
).symm ⁻¹' s int…
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem map_extChartAt_nhdsWithin (x : M) :
    map (extChartAt I x) (𝓝[s] x) = 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x x :=
  map_extChartAt_nhdsWithin' (mem_extChartAt_source x)
/-
**map_extChartAt_symm_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_symm_nhdsWithin' {x y : M} (hy : y in (extChartAt I x).sour
ce) : map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s inter range I] ex
tChartAt I x y) = 𝓝[s] y
参数：hy : y in (extChartAt I x).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_extend_symm_nhdsWithin`：map_extend_symm_nhdsWi
thin {y : M} (hy : y in f.source) : map (f.extend I).symm (𝓝[(f.extend I).symm ⁻
¹' s inter range I] f.extend I y) = 𝓝[…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
theorem map_extChartAt_symm_nhdsWithin' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x y) =
      𝓝[s] y :=
  map_extend_symm_nhdsWithin _ <| by rwa [← extChartAt_source I]
/-
**map_extChartAt_symm_nhdsWithin_range'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_symm_nhdsWithin_range' {x y : M} (hy : y in (extChartAt I x
).source) : map (extChartAt I x).symm (𝓝[range I] extChartAt I x y) = 𝓝 y
参数：hy : y in (extChartAt I x).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_extend_symm_nhdsWithin_range`：map_extend_symm_
nhdsWithin_range {y : M} (hy : y in f.source) : map (f.extend I).symm (𝓝[range I
] f.extend I y) = 𝓝 y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
theorem map_extChartAt_symm_nhdsWithin_range' {x y : M} (hy : y ∈ (extChartAt I x).source) :
    map (extChartAt I x).symm (𝓝[range I] extChartAt I x y) = 𝓝 y :=
  map_extend_symm_nhdsWithin_range _ <| by rwa [← extChartAt_source I]
/-
**map_extChartAt_symm_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_symm_nhdsWithin (x : M) : map (extChartAt I x).symm (𝓝[(ext
ChartAt I x).symm ⁻¹' s inter range I] extChartAt I x x) = 𝓝[s] x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_extChartAt_symm_nhdsWithin'`：map_extChartAt_symm_nhdsWithin' {x y : 
M} (hy : y in (extChartAt I x).source) : map (extChartAt I x).symm (𝓝[(extChartA
t I x).symm ⁻¹' s int…
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem map_extChartAt_symm_nhdsWithin (x : M) :
    map (extChartAt I x).symm (𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] extChartAt I x x) =
      𝓝[s] x :=
  map_extChartAt_symm_nhdsWithin' (mem_extChartAt_source x)
/-
**map_extChartAt_symm_nhdsWithin_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_extChartAt_symm_nhdsWithin_range (x : M) : map (extChartAt I x).symm (
𝓝[range I] extChartAt I x x) = 𝓝 x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_extChartAt_symm_nhdsWithin_range'`：map_extChartAt_symm_nhdsWithin_ra
nge' {x y : M} (hy : y in (extChartAt I x).source) : map (extChartAt I x).symm (
𝓝[range I] extChartAt I x y…
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source
-/
theorem map_extChartAt_symm_nhdsWithin_range (x : M) :
    map (extChartAt I x).symm (𝓝[range I] extChartAt I x x) = 𝓝 x :=
  map_extChartAt_symm_nhdsWithin_range' (mem_extChartAt_source x)
/-
**extChartAt_preimage_mem_nhds_of_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_preimage_mem_nhds_of_mem_nhdsWithin {s : Set E} {x x' : M} (hx 
: x' in (extChartAt I x).source) (hs : s in 𝓝[range I] (extChartAt I x x')) : (e
xtChartAt I x) ⁻¹' s in 𝓝 x'
参数：hx : x' in (extChartAt I x).source；hs : s in 𝓝[range I] (extChartAt I x x')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.extend_preimage_mem_nhds_of_mem_nhdsWithin`：extend
_preimage_mem_nhds_of_mem_nhdsWithin {s : Set E} {x : M} (hx : x in f.source) (h
s : s in 𝓝[range I] (f.extend I x)) : (f.extend I) ⁻¹'…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
-/
theorem extChartAt_preimage_mem_nhds_of_mem_nhdsWithin {s : Set E} {x x' : M}
    (hx : x' ∈ (extChartAt I x).source)
    (hs : s ∈ 𝓝[range I] (extChartAt I x x')) :
    (extChartAt I x) ⁻¹' s ∈ 𝓝 x' :=
  extend_preimage_mem_nhds_of_mem_nhdsWithin _ (by simpa using hx) hs

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
in the source is a neighborhood of the preimage, within a set. -/
/-
**extChartAt_preimage_mem_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_preimage_mem_nhdsWithin' {x x' : M} (h : x' in (extChartAt I x)
.source) (ht : t in 𝓝[s] x') : (extChartAt I x).symm ⁻¹' t in 𝓝[(extChartAt I x)
.symm ⁻¹' s inter range I] (extChartAt I x) x'
参数：h : x' in (extChartAt I x).source；ht : t in 𝓝[s] x'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_extChartAt_symm_nhdsWithin'`：map_extChartAt_symm_nhdsWithin' {x y : 
M} (hy : y in (extChartAt I x).source) : map (extChartAt I x).symm (𝓝[(extChartA
t I x).symm ⁻¹' s int…

--- 原说明 ---
Technical lemma ensuring that the preimage under an extended chart of a neighbor
hood of a point
in the source is a neighborhood of the preimage, within a set.
-/
theorem extChartAt_preimage_mem_nhdsWithin' {x x' : M} (h : x' ∈ (extChartAt I x).source)
    (ht : t ∈ 𝓝[s] x') :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x' := by
  rwa [← map_extChartAt_symm_nhdsWithin' h, mem_map] at ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of the
base point is a neighborhood of the preimage, within a set. -/
/-
**extChartAt_preimage_mem_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_preimage_mem_nhdsWithin {x : M} (ht : t in 𝓝[s] x) : (extChartA
t I x).symm ⁻¹' t in 𝓝[(extChartAt I x).symm ⁻¹' s inter range I] (extChartAt I 
x) x
参数：ht : t in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `extChartAt_preimage_mem_nhdsWithin'`：extChartAt_preimage_mem_nhdsWithin'
 {x x' : M} (h : x' in (extChartAt I x).source) (ht : t in 𝓝[s] x') : (extChartA
t I x).symm ⁻¹' t in 𝓝[(e…
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source

--- 原说明 ---
Technical lemma ensuring that the preimage under an extended chart of a neighbor
hood of the
base point is a neighborhood of the preimage, within a set.
-/
theorem extChartAt_preimage_mem_nhdsWithin {x : M} (ht : t ∈ 𝓝[s] x) :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x) x :=
  extChartAt_preimage_mem_nhdsWithin' (mem_extChartAt_source x) ht
/-
**extChartAt_preimage_mem_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_preimage_mem_nhds' {x x' : M} (h : x' in (extChartAt I x).sourc
e) (ht : t in 𝓝 x') : (extChartAt I x).symm ⁻¹' t in 𝓝 (extChartAt I x x')
参数：h : x' in (extChartAt I x).source；ht : t in 𝓝 x'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.extend_preimage_mem_nhds`：extend_preimage_mem_nhds
 {x : M} (h : x in f.source) (ht : t in 𝓝 x) : (f.extend I).symm ⁻¹' t in 𝓝 (f.e
xtend I x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `extChartAt_source`：extChartAt_source (x : M) : (extChartAt I x).source =
 (chartAt H x).source
-/
theorem extChartAt_preimage_mem_nhds' {x x' : M} (h : x' ∈ (extChartAt I x).source)
    (ht : t ∈ 𝓝 x') : (extChartAt I x).symm ⁻¹' t ∈ 𝓝 (extChartAt I x x') :=
  extend_preimage_mem_nhds _ (by rwa [← extChartAt_source I]) ht

/-- Technical lemma ensuring that the preimage under an extended chart of a neighborhood of a point
is a neighborhood of the preimage. -/
/-
**extChartAt_preimage_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_preimage_mem_nhds {x : M} (ht : t in 𝓝 x) : (extChartAt I x).sy
mm ⁻¹' t in 𝓝 ((extChartAt I x) x)
参数：ht : t in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `continuousAt_extChartAt_symm`：continuousAt_extChartAt_symm (x : M) : Con
tinuousAt (extChartAt I x).symm ((extChartAt I x) x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `mem_extChartAt_source`：mem_extChartAt_source (x : M) : x in (extChartAt 
I x).source

--- 原说明 ---
Technical lemma ensuring that the preimage under an extended chart of a neighbor
hood of a point
is a neighborhood of the preimage.
-/
theorem extChartAt_preimage_mem_nhds {x : M} (ht : t ∈ 𝓝 x) :
    (extChartAt I x).symm ⁻¹' t ∈ 𝓝 ((extChartAt I x) x) := by
  apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
  rwa [(extChartAt I x).left_inv (mem_extChartAt_source _)]

/-- Technical lemma to rewrite suitably the preimage of an intersection under an extended chart, to
bring it into a convenient form to apply derivative lemmas. -/
/-
**extChartAt_preimage_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_preimage_inter_eq (x : M) : (extChartAt I x).symm ⁻¹' (s inter 
t) inter range I = (extChartAt I x).symm ⁻¹' s inter range I inter (extChartAt I
 x).symm ⁻¹' t
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Technical lemma to rewrite suitably the preimage of an intersection under an ext
ended chart, to
bring it into a convenient form to apply derivative lemmas.
-/
theorem extChartAt_preimage_inter_eq (x : M) :
    (extChartAt I x).symm ⁻¹' (s ∩ t) ∩ range I =
      (extChartAt I x).symm ⁻¹' s ∩ range I ∩ (extChartAt I x).symm ⁻¹' t := by
  mfld_set_tac
/-
**ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range** 是 Mathlib
 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range {f : M 
-> M'} {x : M} (hc : ContinuousWithinAt f s x) : 𝓝[(extChartAt I x).symm ⁻¹' s i
nter range I] (extChartAt I x x) = 𝓝[(extChartAt I x).target inter (extChartAt I
 x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' (f x)).source)] (extChartAt I x x)
参数：hc : ContinuousWithinAt f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.image_source_inter_eq'`：image_source_inter_eq' (s : Set α) 
: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `map_extChartAt_nhdsWithin_eq_image`：map_extChartAt_nhdsWithin_eq_image (
x : M) : map (extChartAt I x) (𝓝[s] x) = 𝓝[extChartAt I x '' ((extChartAt I x).s
ource inter s)] extChart…
· 使用定理 `map_extChartAt_nhdsWithin`：map_extChartAt_nhdsWithin (x : M) : map (extC
hartAt I x) (𝓝[s] x) = 𝓝[(extChartAt I x).symm ⁻¹' s inter range I] extChartAt I
 x x
· 使用定理 `nhdsWithin_inter_of_mem'`：nhdsWithin_inter_of_mem' {a : α} {s t : Set α}
 (h : t in 𝓝[s] a) : 𝓝[s inter t] a = 𝓝[s] a
· 使用定理 `extChartAt_source_mem_nhds`：extChartAt_source_mem_nhds (x : M) : (extCha
rtAt I x).source in 𝓝 x
-/
theorem ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range
    {f : M → M'} {x : M} (hc : ContinuousWithinAt f s x) :
    𝓝[(extChartAt I x).symm ⁻¹' s ∩ range I] (extChartAt I x x) =
      𝓝[(extChartAt I x).target ∩
        (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source)] (extChartAt I x x) := by
  rw [← (extChartAt I x).image_source_inter_eq', ← map_extChartAt_nhdsWithin_eq_image,
    ← map_extChartAt_nhdsWithin, nhdsWithin_inter_of_mem']
  exact hc (extChartAt_source_mem_nhds _)
/-
**ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq** 是 Mathl
ib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq {f : 
M -> M'} {x : M} (hc : ContinuousWithinAt f s x) : ((extChartAt I x).symm ⁻¹' s 
inter range I : Set E) =ᶠ[𝓝 (extChartAt I x x)] ((extChartAt I x).target inter (
extChartAt I x).symm ⁻¹' (s inter f ⁻¹' (extChartAt I' (f x)).source) : Set E)
参数：hc : ContinuousWithinAt f s x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_eq_iff_eventuallyEq`：nhdsWithin_eq_iff_eventuallyEq {s t : Se
t α} {x : α} : 𝓝[s] x = 𝓝[t] x ↔ s =ᶠ[𝓝 x] t
· 使用定理 `ContinuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range`：Cont
inuousWithinAt.nhdsWithin_extChartAt_symm_preimage_inter_range {f : M -> M'} {x 
: M} (hc : ContinuousWithinAt f s x) : 𝓝[(extChartAt I x…
-/
theorem ContinuousWithinAt.extChartAt_symm_preimage_inter_range_eventuallyEq
    {f : M → M'} {x : M} (hc : ContinuousWithinAt f s x) :
    ((extChartAt I x).symm ⁻¹' s ∩ range I : Set E) =ᶠ[𝓝 (extChartAt I x x)]
      ((extChartAt I x).target ∩
        (extChartAt I x).symm ⁻¹' (s ∩ f ⁻¹' (extChartAt I' (f x)).source) : Set E) := by
  rw [← nhdsWithin_eq_iff_eventuallyEq]
  exact hc.nhdsWithin_extChartAt_symm_preimage_inter_range

/-! We use the name `ext_coord_change` for `(extChartAt I x').symm ≫ extChartAt I x`. -/

/-
**ext_coord_change_source** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ext_coord_change_source (x x' : M) : ((extChartAt I x').symm ≫ extChartAt 
I x).source = I '' ((chartAt H x').symm ≫ₕ chartAt H x).source
参数：x x' : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModelWithCorners.extendCoordChange_source`：extendCoordChange_source : (I
.extendCoordChange e e').source = I '' (e.symm ≫ₕ e').source

--- 原说明 ---
We use the name `ext_coord_change` for `(extChartAt I x').symm ≫ extChartAt I x`
.
-/
theorem ext_coord_change_source (x x' : M) :
    ((extChartAt I x').symm ≫ extChartAt I x).source =
      I '' ((chartAt H x').symm ≫ₕ chartAt H x).source :=
  I.extendCoordChange_source

open IsManifold
/-
**contDiffOn_ext_coord_change** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffOn_ext_coord_change [IsManifold I n M] (x x' : M) : ContDiffOn 𝕜 n
 (extChartAt I x ∘ (extChartAt I x').symm) ((extChartAt I x').symm ≫ extChartAt 
I x).source
参数：x x' : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModelWithCorners.contDiffOn_extendCoordChange`：contDiffOn_extendCoordCha
nge (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) : ContDiffOn
 𝕜 n (I.extendCoordChange e e') (I.…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
-/
theorem contDiffOn_ext_coord_change [IsManifold I n M] (x x' : M) :
    ContDiffOn 𝕜 n (extChartAt I x ∘ (extChartAt I x').symm)
      ((extChartAt I x').symm ≫ extChartAt I x).source :=
  I.contDiffOn_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x)
/-
**contDiffWithinAt_ext_coord_change** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：contDiffWithinAt_ext_coord_change [IsManifold I n M] (x x' : M) {y : E} (h
y : y in ((extChartAt I x').symm ≫ extChartAt I x).source) : ContDiffWithinAt 𝕜 
n (extChartAt I x ∘ (extChartAt I x').symm) (range I) y
参数：x x' : M；hy : y in ((extChartAt I x').symm ≫ extChartAt I x).source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModelWithCorners.contDiffWithinAt_extendCoordChange`：contDiffWithinAt_ex
tendCoordChange (he : e in maximalAtlas I n M) (he' : e' in maximalAtlas I n M) 
{x : E} (hx : x in (I.extendCoordChange e…
· 使用定理 `IsManifold.chart_mem_maximalAtlas`：chart_mem_maximalAtlas [IsManifold I 
n M] (x : M) : chartAt H x in maximalAtlas I n M
-/
theorem contDiffWithinAt_ext_coord_change [IsManifold I n M] (x x' : M) {y : E}
    (hy : y ∈ ((extChartAt I x').symm ≫ extChartAt I x).source) :
    ContDiffWithinAt 𝕜 n (extChartAt I x ∘ (extChartAt I x').symm) (range I) y :=
  I.contDiffWithinAt_extendCoordChange (chart_mem_maximalAtlas x') (chart_mem_maximalAtlas x) hy

variable (I I') in
/-- Conjugating a function to write it in the preferred charts around `x`.
The manifold derivative of `f` will just be the derivative of this conjugated function. -/
@[simp, mfld_simps]
/-
**writtenInExtChartAt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：writtenInExtChartAt (x : M) (f : M -> M') : E -> E'
参数：x : M；f : M -> M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugating a function to write it in the preferred charts around `x`.
The manifold derivative of `f` will just be the derivative of this conjugated fu
nction.
-/
def writtenInExtChartAt (x : M) (f : M → M') : E → E' :=
  extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm

set_option backward.isDefEq.respectTransparency false in
/-
**writtenInExtChartAt_chartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_chartAt {x : M} {y : E} (h : y in (extChartAt I x).tar
get) : writtenInExtChartAt I I x (chartAt H x) y = y
参数：h : y in (extChartAt I x).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem writtenInExtChartAt_chartAt {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt I I x (chartAt H x) y = y := by simp_all only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
/-
**writtenInExtChartAt_chartAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_chartAt_symm {x : M} {y : E} (h : y in (extChartAt I x
).target) : writtenInExtChartAt I I (chartAt H x x) (chartAt H x).symm y = y
参数：h : y in (extChartAt I x).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem writtenInExtChartAt_chartAt_symm {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt I I (chartAt H x x) (chartAt H x).symm y = y := by
  simp_all only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
/-
**writtenInExtChartAt_extChartAt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_extChartAt {x : M} {y : E} (h : y in (extChartAt I x).
target) : writtenInExtChartAt I 𝓘(𝕜, E) x (extChartAt I x) y = y
参数：h : y in (extChartAt I x).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem writtenInExtChartAt_extChartAt {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt I 𝓘(𝕜, E) x (extChartAt I x) y = y := by
  simp_all only [mfld_simps]

set_option backward.isDefEq.respectTransparency false in
/-
**writtenInExtChartAt_extChartAt_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_extChartAt_symm {x : M} {y : E} (h : y in (extChartAt 
I x).target) : writtenInExtChartAt 𝓘(𝕜, E) I (extChartAt I x x) (extChartAt I x)
.symm y = y
参数：h : y in (extChartAt I x).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem writtenInExtChartAt_extChartAt_symm {x : M} {y : E} (h : y ∈ (extChartAt I x).target) :
    writtenInExtChartAt 𝓘(𝕜, E) I (extChartAt I x x) (extChartAt I x).symm y = y := by
  simp_all only [mfld_simps]
/-
**writtenInExtChartAt_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_mapsTo {x : M} {f : M -> M'} : MapsTo (writtenInExtCha
rtAt I I' x f) ((extChartAt I x).target inter f ∘ (extChartAt I x).symm ⁻¹' (ext
ChartAt I' (f x)).source) (extChartAt I' (f x)).target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `OpenPartialHomeomorph.mapsTo`：∀ {X : Type u_1} {Y : Type u_3} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y
), Set.MapsTo (↑e)…
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem writtenInExtChartAt_mapsTo {x : M} {f : M → M'} :
    MapsTo (writtenInExtChartAt I I' x f)
      ((extChartAt I x).target ∩ f ∘ (extChartAt I x).symm ⁻¹' (extChartAt I' (f x)).source)
      (extChartAt I' (f x)).target := by
  intro x' hx'
  simpa using (chartAt H' (f x)).mapsTo (by simpa using hx'.2)

section

variable {G G' F F' N N' : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  [TopologicalSpace G] [TopologicalSpace N] [TopologicalSpace G'] [TopologicalSpace N']
  {J : ModelWithCorners 𝕜 F G} {J' : ModelWithCorners 𝕜 F' G'}
  [ChartedSpace G N] [ChartedSpace G' N']

/-
**writtenInExtChartAt_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_prod {f : M -> N} {g : M' -> N'} {x : M} {x' : M'} : (
writtenInExtChartAt (I.prod I') (J.prod J') (x, x') (Prod.map f g)) = Prod.map (
writtenInExtChartAt I J x f) (writtenInExtChartAt I' J' x' g)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `PartialEquiv.prod_symm`：prod_symm (e : PartialEquiv α β) (e' : PartialEq
uiv γ δ) : (e.prod e').symm = e.symm.prod e'.symm
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma writtenInExtChartAt_prod {f : M → N} {g : M' → N'} {x : M} {x' : M'} :
    (writtenInExtChartAt (I.prod I') (J.prod J') (x, x') (Prod.map f g)) =
      Prod.map (writtenInExtChartAt I J x f) (writtenInExtChartAt I' J' x' g) := by
  ext p <;>
  simp [writtenInExtChartAt, I.toPartialEquiv.prod_symm, (chartAt H x).toPartialEquiv.prod_symm]

@[deprecated (since := "2026-02-18")] alias writtenInExtChart_prod := writtenInExtChartAt_prod

end

variable (𝕜)

/-
**extChartAt_self_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_self_eq {x : H} : ⇑(extChartAt I x) = I
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extChartAt_self_eq {x : H} : ⇑(extChartAt I x) = I :=
  rfl
/-
**extChartAt_self_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_self_apply {x y : H} : extChartAt I x y = I y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem extChartAt_self_apply {x y : H} : extChartAt I x y = I y :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In the case of the manifold structure on a vector space, the extended charts are just the
identity. -/
/-
**extChartAt_model_space_eq_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_model_space_eq_id (x : E) : extChartAt 𝓘(𝕜, E) x = PartialEquiv
.refl E
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In the case of the manifold structure on a vector space, the extended charts are
 just the
identity.
-/
theorem extChartAt_model_space_eq_id (x : E) : extChartAt 𝓘(𝕜, E) x = PartialEquiv.refl E := by
  simp only [mfld_simps]
/-
**ext_chart_model_space_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ext_chart_model_space_apply {x y : E} : extChartAt 𝓘(𝕜, E) x y = y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ext_chart_model_space_apply {x y : E} : extChartAt 𝓘(𝕜, E) x y = y :=
  rfl

variable {𝕜}
/-
**extChartAt_prod** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_prod (x : M × M') : extChartAt (I.prod I') x = (extChartAt I x.
1).prod (extChartAt I' x.2)
参数：x : M × M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.prod_toPartialHomeomorph`：∀ {X : Type u_1} {X' : T
ype u_2} {Y : Type u_3} {Y' : Type u_4} [inst : TopologicalSpace X]   [inst_1 : 
TopologicalSpace X'] [inst_2 : Topol…
· 使用定理 `PartialEquiv.prod_trans`：prod_trans {η : Type*} {ε : Type*} (e : Partial
Equiv α β) (f : PartialEquiv β γ) (e' : PartialEquiv δ η) (f' : PartialEquiv η ε
) : (e.prod e…
-/
theorem extChartAt_prod (x : M × M') :
    extChartAt (I.prod I') x = (extChartAt I x.1).prod (extChartAt I' x.2) := by
  simp only [mfld_simps]
  rw [PartialEquiv.prod_trans]
/-
**extChartAt_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：extChartAt_comp [ChartedSpace H H'] (x : M') : (letI
参数：x : M'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.trans_assoc`：trans_assoc (e'' : PartialEquiv γ δ) : (e.tran
s e').trans e'' = e.trans (e'.trans e'')
-/
theorem extChartAt_comp [ChartedSpace H H'] (x : M') :
    (letI := ChartedSpace.comp H H' M'; extChartAt I x) =
      (chartAt H' x).toPartialEquiv ≫ extChartAt I (chartAt H' x x) :=
  PartialEquiv.trans_assoc ..
/-
**writtenInExtChartAt_chartAt_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_chartAt_comp [ChartedSpace H H'] (x : M') {y} (hy : y 
in letI
参数：x : M'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem writtenInExtChartAt_chartAt_comp [ChartedSpace H H'] (x : M') {y}
    (hy : y ∈ letI := ChartedSpace.comp H H' M'; (extChartAt I x).target) :
    (letI := ChartedSpace.comp H H' M'; writtenInExtChartAt I I x (chartAt H' x) y) = y := by
  let := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]
/-
**writtenInExtChartAt_chartAt_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：writtenInExtChartAt_chartAt_symm_comp [ChartedSpace H H'] (x : M') {y} (hy
 : y in letI
参数：x : M'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x
· 使用定理 `ModelWithCorners.target_eq`：target_eq : I.target = range (I : H -> E)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.right_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem writtenInExtChartAt_chartAt_symm_comp [ChartedSpace H H'] (x : M') {y}
    (hy : y ∈ letI := ChartedSpace.comp H H' M'; (extChartAt I x).target) :
    (letI := ChartedSpace.comp H H' M'
     writtenInExtChartAt I I (chartAt H' x x) (chartAt H' x).symm y) = y := by
  let := ChartedSpace.comp H H' M'
  simp_all only [mfld_simps, chartAt_comp]

end ExtendedCharts

section Topology

-- Let `M` be a topological manifold over the field 𝕜.
variable
  {E : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- A finite-dimensional manifold modelled on a locally compact field
(such as ℝ, ℂ or the `p`-adic numbers) is locally compact. -/
/-
**Manifold.locallyCompact_of_finiteDimensional** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Manifold.locallyCompact_of_finiteDimensional (I : ModelWithCorners 𝕜 E H) 
[LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E] : LocallyCompactSpace M
参数：I : ModelWithCorners 𝕜 E H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteDimensional.proper`：FiniteDimensional.proper [FiniteDimensional 𝕜 
E] : ProperSpace E
· 使用定理 `ModelWithCorners.locallyCompactSpace`：∀ {𝕜 : Type u_1} [inst : Nontrivia
llyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : Nor
medSpace 𝕜 E] {H : Type u_…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `ChartedSpace.locallyCompactSpace`：ChartedSpace.locallyCompactSpace [Loca
llyCompactSpace H] : LocallyCompactSpace M

--- 原说明 ---
A finite-dimensional manifold modelled on a locally compact field
(such as ℝ, ℂ or the `p`-adic numbers) is locally compact.
-/
lemma Manifold.locallyCompact_of_finiteDimensional
    (I : ModelWithCorners 𝕜 E H) [LocallyCompactSpace 𝕜] [FiniteDimensional 𝕜 E] :
    LocallyCompactSpace M := by
  have : ProperSpace E := FiniteDimensional.proper 𝕜 E
  have : LocallyCompactSpace H := I.locallyCompactSpace
  exact ChartedSpace.locallyCompactSpace H M

variable (M)

/-- A locally compact manifold must be modelled on a locally compact space. -/
/-
**LocallyCompactSpace.of_locallyCompact_manifold** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LocallyCompactSpace.of_locallyCompact_manifold (I : ModelWithCorners 𝕜 E H
) [h : Nonempty M] [LocallyCompactSpace M] : LocallyCompactSpace E
参数：I : ModelWithCorners 𝕜 E H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `interior_extChartAt_target_nonempty`：interior_extChartAt_target_nonempty
 (x : M) : (interior (extChartAt I x).target).Nonempty
· 使用定理 `interior_subset`：interior_subset : interior s subseteq s
· 使用定理 `LocallyCompactSpace.local_compact_nhds`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : LocallyCompactSpace X] (x : X),   ∀ n ∈ nhds x, ∃ s ∈ nhds 
x, s ⊆ n ∧ IsCompact s
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_extChartAt_source`：isOpen_extChartAt_source (x : M) : IsOpen (ext
ChartAt I x).source
· 使用定理 `PartialEquiv.map_target`：map_target {x : β} (h : x in e.target) : e.symm
 x in e.source
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `continuousOn_extChartAt`：continuousOn_extChartAt (x : M) : ContinuousOn 
(extChartAt I x) (extChartAt I x).source
· 使用定理 `IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup`：∀ {G : Type w} [i
nst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {K : S
et G},   IsCompact K → ∀ {x : G}, K ∈ nhds …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `extChartAt_image_nhds_mem_nhds_of_mem_interior_range`：extChartAt_image_n
hds_mem_nhds_of_mem_interior_range {x y} (hx : y in (extChartAt I x).source) (h'
x : extChartAt I x y in interior (range I)…
· 使用定理 `interior_mono`：interior_mono (h : s subseteq t) : interior s subseteq in
terior t
· 使用定理 `extChartAt_target_subset_range`：extChartAt_target_subset_range (x : M) :
 (extChartAt I x).target subseteq range I

--- 原说明 ---
A locally compact manifold must be modelled on a locally compact space.
-/
lemma LocallyCompactSpace.of_locallyCompact_manifold (I : ModelWithCorners 𝕜 E H)
    [h : Nonempty M] [LocallyCompactSpace M] :
    LocallyCompactSpace E := by
  rcases h with ⟨x⟩
  obtain ⟨y, hy⟩ := interior_extChartAt_target_nonempty I x
  have h'y : y ∈ (extChartAt I x).target := interior_subset hy
  obtain ⟨s, hmem, hss, hcom⟩ :=
    LocallyCompactSpace.local_compact_nhds ((extChartAt I x).symm y) (extChartAt I x).source
      ((isOpen_extChartAt_source x).mem_nhds ((extChartAt I x).map_target h'y))
  have : IsCompact <| (extChartAt I x) '' s :=
    hcom.image_of_continuousOn <| (continuousOn_extChartAt x).mono hss
  apply this.locallyCompactSpace_of_mem_nhds_of_addGroup (x := y)
  rw [← (extChartAt I x).right_inv h'y]
  apply extChartAt_image_nhds_mem_nhds_of_mem_interior_range
    (PartialEquiv.map_target (extChartAt I x) h'y) _ hmem
  simp only [(extChartAt I x).right_inv h'y]
  exact interior_mono (extChartAt_target_subset_range x) hy

/-- Riesz's theorem applied to manifolds: a locally compact manifold must be modelled on a
finite-dimensional space. This is the converse to `Manifold.locallyCompact_of_finiteDimensional`. -/
/-
**FiniteDimensional.of_locallyCompact_manifold** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FiniteDimensional.of_locallyCompact_manifold [CompleteSpace 𝕜] (I : ModelW
ithCorners 𝕜 E H) [Nonempty M] [LocallyCompactSpace M] : FiniteDimensional 𝕜 E
参数：I : ModelWithCorners 𝕜 E H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LocallyCompactSpace.of_locallyCompact_manifold`：LocallyCompactSpace.of_l
ocallyCompact_manifold (I : ModelWithCorners 𝕜 E H) [h : Nonempty M] [LocallyCom
pactSpace M] : LocallyCompactSpace E
· 使用定理 `FiniteDimensional.of_locallyCompactSpace`：FiniteDimensional.of_locallyCo
mpactSpace [WeaklyLocallyCompactSpace E] : FiniteDimensional 𝕜 E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X

--- 原说明 ---
Riesz's theorem applied to manifolds: a locally compact manifold must be modelle
d on a
finite-dimensional space. This is the converse to `Manifold.locallyCompact_of_fi
niteDimensional`.
-/
theorem FiniteDimensional.of_locallyCompact_manifold
    [CompleteSpace 𝕜] (I : ModelWithCorners 𝕜 E H) [Nonempty M] [LocallyCompactSpace M] :
    FiniteDimensional 𝕜 E := by
  have := LocallyCompactSpace.of_locallyCompact_manifold M I
  exact FiniteDimensional.of_locallyCompactSpace 𝕜

end Topology

