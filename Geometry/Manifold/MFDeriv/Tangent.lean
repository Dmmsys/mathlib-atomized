/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.UniqueDifferential
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Derivatives of maps in the tangent bundle

This file contains properties of derivatives which need the manifold structure of the tangent
bundle. Notably, it includes formulas for the tangent maps to charts, and unique differentiability
statements for subsets of the tangent bundle.
-/

@[expose] public section

open Bundle Set
open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' 1 M']


/-- The derivative of the chart at a base point is the chart of the tangent bundle, composed with
the identification between the tangent bundle of the model space and the product space. -/
/-
**tangentMap_chart** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMap_chart {p q : TangentBundle I M} (h : q.1 in (chartAt H p.1).sou
rce) : tangentMap% (chartAt H p.1) q = (TotalSpace.toProd _ _).symm ((chartAt (M
odelProd H E) p : TangentBundle I M -> ModelProd H E) q)
参数：h : q.1 in (chartAt H p.1).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiableAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `mdifferentiableAt_atlas`：mdifferentiableAt_atlas (h : e in atlas H M) {x
 : M} (hx : x in e.source) : MDiffAt e x
· 使用引理 `chart_mem_atlas`：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpa
ce H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M

--- 原说明 ---
The derivative of the chart at a base point is the chart of the tangent bundle, 
composed with
the identification between the tangent bundle of the model space and the product
 space.
-/
theorem tangentMap_chart {p q : TangentBundle I M} (h : q.1 ∈ (chartAt H p.1).source) :
    tangentMap% (chartAt H p.1) q =
      (TotalSpace.toProd _ _).symm
        ((chartAt (ModelProd H E) p : TangentBundle I M → ModelProd H E) q) := by
  dsimp [tangentMap]
  rw [MDifferentiableAt.mfderiv]
  · rfl
  · exact mdifferentiableAt_atlas (chart_mem_atlas _ _) h

/-- The derivative of the inverse of the chart at a base point is the inverse of the chart of the
tangent bundle, composed with the identification between the tangent bundle of the model space and
the product space. -/
/-
**tangentMap_chart_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tangentMap_chart_symm {p : TangentBundle I M} {q : TangentBundle I H} (h :
 q.1 in (chartAt H p.1).target) : tangentMap% (chartAt H p.1).symm q = (chartAt 
(ModelProd H E) p).symm (TotalSpace.toProd H E q)
参数：h : q.1 in (chartAt H p.1).target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MDifferentiableAt.mfderiv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `mdifferentiableAt_atlas_symm`：mdifferentiableAt_atlas_symm (h : e in atl
as H M) {x : H} (hx : x in e.target) : MDiffAt e.symm x
· 使用引理 `chart_mem_atlas`：chart_mem_atlas (H : Type*) {M : Type*} [TopologicalSpa
ce H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : chartAt H x in atlas H M
· 使用引理 `mem_chart_source`：mem_chart_source (H : Type*) {M : Type*} [TopologicalS
pace H] [TopologicalSpace M] [ChartedSpace H M] (x : M) : x in (chartAt H x).sou
rce
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OpenPartialHomeomorph.right_inv`：right_inv {x : Y} (h : x in e.target) :
 e (e.symm x) = x

--- 原说明 ---
The derivative of the inverse of the chart at a base point is the inverse of the
 chart of the
tangent bundle, composed with the identification between the tangent bundle of t
he model space and
the product space.
-/
theorem tangentMap_chart_symm {p : TangentBundle I M} {q : TangentBundle I H}
    (h : q.1 ∈ (chartAt H p.1).target) :
    tangentMap% (chartAt H p.1).symm q =
      (chartAt (ModelProd H E) p).symm (TotalSpace.toProd H E q) := by
  dsimp only [tangentMap]
  rw [MDifferentiableAt.mfderiv (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) h)]
  simp only [TangentBundle.chartAt, tangentBundleCore,
    mfld_simps]
  -- `simp` fails to apply `PartialEquiv.prod_symm` with `ModelProd`
  congr
  exact ((chartAt H (TotalSpace.proj p)).right_inv h).symm

set_option backward.isDefEq.respectTransparency false in
/-
**mfderiv_chartAt_eq_tangentCoordChange** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mfderiv_chartAt_eq_tangentCoordChange {x y : M} (hsrc : x in (chartAt H y)
.source) : mfderiv% (chartAt H y) x = tangentCoordChange I x y x
参数：hsrc : x in (chartAt H y).source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mdifferentiableAt_atlas`：mdifferentiableAt_atlas (h : e in atlas H M) {x
 : M} (hx : x in e.source) : MDiffAt e x
· 使用定理 `ChartedSpace.chart_mem_atlas`：∀ {H : Type u_5} {inst : TopologicalSpace 
H} {M : Type u_6} {inst_1 : TopologicalSpace M} [self : ChartedSpace H M]   (x :
 M), ChartedSpace.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.refl_trans`：refl_trans : (PartialEquiv.refl α).trans e = e
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `tangentBundleCore_coordChange`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mfderiv_chartAt_eq_tangentCoordChange {x y : M} (hsrc : x ∈ (chartAt H y).source) :
    mfderiv% (chartAt H y) x = tangentCoordChange I x y x := by
  have := mdifferentiableAt_atlas (I := I) (ChartedSpace.chart_mem_atlas _) hsrc
  simp [mfderiv, if_pos this, Function.comp_assoc]

/-- The preimage under the projection from the tangent bundle of a set with unique differential in
the basis also has unique differential. -/
/-
**UniqueMDiffOn.tangentBundle_proj_preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：UniqueMDiffOn.tangentBundle_proj_preimage {s : Set M} (hs : UniqueMDiffOn 
I s) : UniqueMDiffOn I.tangent (π E (TangentSpace I) ⁻¹' s)
参数：hs : UniqueMDiffOn I s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueMDiffOn.bundle_preimage`：UniqueMDiffOn.bundle_preimage (hs : Uniqu
eMDiff[s]) : UniqueMDiff[π F Z ⁻¹' s]

--- 原说明 ---
The preimage under the projection from the tangent bundle of a set with unique d
ifferential in
the basis also has unique differential.
-/
theorem UniqueMDiffOn.tangentBundle_proj_preimage {s : Set M} (hs : UniqueMDiffOn I s) :
    UniqueMDiffOn I.tangent (π E (TangentSpace I) ⁻¹' s) :=
  hs.bundle_preimage _

set_option backward.isDefEq.respectTransparency false in
/-- To write a linear map between tangent spaces in coordinates amounts to precomposing and
postcomposing it with derivatives of extended charts.
Concrete version of `inTangentCoordinates_eq`. -/
/-
**inTangentCoordinates_eq_mfderiv_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inTangentCoordinates_eq_mfderiv_comp {N : Type*} {f : N -> M} {g : N -> M'
} {ϕ : Π x : N, TangentSpace% (f x) ->L[𝕜] TangentSpace% (g x)} {x₀ : N} {x : N}
 (hx : f x in (chartAt H (f x₀)).source) (hy : g x in (chartAt H' (g x₀)).source
) : inTangentCoordinates I I' f g ϕ x₀ x = (mfderiv% (extChartAt I' (g x₀)) (g x
)) ∘L (ϕ x) ∘L (mfderiv[range I] (extChartAt I (f x₀)).symm (extChartAt I (f x₀)
 (f x)))
参数：f x；g x；hx : f x in (chartAt H (f x₀)).source；hy : g x in (chartAt H' (g x₀))
.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inTangentCoordinates_eq`：inTangentCoordinates_eq (f : N -> M) (g : N -> 
M') (ϕ : N -> E ->L[𝕜] E') {x₀ x : N} (hx : f x in (chartAt H (f x₀)).source) (h
y : g x in (c…
· 使用定理 `tangentBundleCore_coordChange`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `mdifferentiableAt_extChartAt`：mdifferentiableAt_extChartAt (h : y in (ch
artAt H x).source) : MDiffAt (extChartAt I x) y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.trans_refl`：trans_refl : e.trans (PartialEquiv.refl β) = e
· 使用定理 `CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type u_3} {φ : 
M → N} {ψ : N → P} {χ : outParam (M → P)} [self : CompTriple φ ψ χ],   ψ ∘ φ = χ
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mdifferentiableWithinAt_extChartAt_symm`：mdifferentiableWithinAt_extChar
tAt_symm (h : z in (extChartAt I x).target) : MDiffAt[range I] (extChartAt I x).
symm z
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
· 使用定理 `ModelWithCorners.source_eq`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {H : Type u_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ModelWithCorners.left_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFi
eld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 
E] {H : Type u_…
· 使用定理 `OpenPartialHomeomorph.left_inv`：left_inv {x : X} (h : x in e.source) : e
.symm (e x) = x

--- 原说明 ---
To write a linear map between tangent spaces in coordinates amounts to precompos
ing and
postcomposing it with derivatives of extended charts.
Concrete version of `inTangentCoordinates_eq`.
-/
lemma inTangentCoordinates_eq_mfderiv_comp
    {N : Type*} {f : N → M} {g : N → M'}
    {ϕ : Π x : N, TangentSpace% (f x) →L[𝕜] TangentSpace% (g x)} {x₀ : N} {x : N}
    (hx : f x ∈ (chartAt H (f x₀)).source) (hy : g x ∈ (chartAt H' (g x₀)).source) :
    inTangentCoordinates I I' f g ϕ x₀ x =
    (mfderiv% (extChartAt I' (g x₀)) (g x)) ∘L (ϕ x) ∘L
      (mfderiv[range I] (extChartAt I (f x₀)).symm (extChartAt I (f x₀) (f x))) := by
  rw [inTangentCoordinates_eq _ _ _ hx hy, tangentBundleCore_coordChange]
  congr
  · have : MDiffAt (extChartAt I' (g x₀)) (g x) := mdifferentiableAt_extChartAt hy
    simp_all [mfderiv]
  · simp only [mfderivWithin, writtenInExtChartAt, modelWithCornersSelf_coe, range_id, inter_univ]
    rw [if_pos]
    · simp [Function.comp_def, OpenPartialHomeomorph.left_inv (chartAt H (f x₀)) hx]
    · apply mdifferentiableWithinAt_extChartAt_symm
      apply (extChartAt I (f x₀)).map_source
      simpa using hx

open Bundle
variable (I) in
/-- The canonical identification between the tangent bundle to the model space and the product,
as a diffeomorphism. -/
/-
**tangentBundleModelSpaceDiffeomorph** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tangentBundleModelSpaceDiffeomorph (n : Nat∞) : TangentBundle I H ≃ₘ^n⟮I.t
angent, I.prod 𝓘(𝕜, E)⟯ ModelProd H E where __
参数：n : Nat∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical identification between the tangent bundle to the model space and t
he product,
as a diffeomorphism.
-/
def tangentBundleModelSpaceDiffeomorph (n : ℕ∞) :
    TangentBundle I H ≃ₘ^n⟮I.tangent, I.prod 𝓘(𝕜, E)⟯ ModelProd H E where
  __ := TotalSpace.toProd H E
  contMDiff_toFun := contMDiff_tangentBundleModelSpaceHomeomorph
  contMDiff_invFun := contMDiff_tangentBundleModelSpaceHomeomorph_symm
