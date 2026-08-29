/-
Copyright (c) 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Floris van Doorn
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Standard constructions on fiber bundles

This file contains several standard constructions on fiber bundles:

* `Bundle.Trivial.fiberBundle 𝕜 B F`: the trivial fiber bundle with model fiber `F` over the base
  `B`

* `FiberBundle.prod`: for fiber bundles `E₁` and `E₂` over a common base, a fiber bundle structure
  on their fiberwise product `E₁ ×ᵇ E₂` (the notation stands for `fun x ↦ E₁ x × E₂ x`).

* `FiberBundle.pullback`: for a fiber bundle `E` over `B`, a fiber bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags

fiber bundle, fibre bundle, fiberwise product, pullback

-/

@[expose] public section

open Bundle Filter Set TopologicalSpace Topology

/-! ### The trivial bundle -/

namespace Bundle

namespace Trivial

variable (B : Type*) (F : Type*)

-- TODO: use `TotalSpace.toProd`
/--
Instance `topologicalSpace` / 实例 `topologicalSpace`

English:
instance topologicalSpace
  signature: [t₁ : TopologicalSpace B]
  body: induced TotalSpace.proj t₁ ⊓ induced (TotalSpace.trivialSnd B F) t₂

中文:
实例 topologicalSpace
  签名: [t₁ : 拓扑空间 B]
  定义体: induced TotalSpace.proj t₁ ⊓ induced (TotalSpace.trivialSnd B F) t₂

Depends on / 依赖: TotalSpace, TotalSpace.proj, TotalSpace.trivialSnd, induced, trivialSnd
-/
instance topologicalSpace [t₁ : TopologicalSpace B]
    [t₂ : TopologicalSpace F] : TopologicalSpace (TotalSpace F (Trivial B F)) :=
  induced TotalSpace.proj t₁ ⊓ induced (TotalSpace.trivialSnd B F) t₂

variable [TopologicalSpace B] [TopologicalSpace F]

/--
theorem `isInducing_toProd` / 定理 `isInducing_toProd`

English:
theorem isInducing_toProd
  statement: IsInducing (TotalSpace.toProd B F)
  proof: ⟨by simp only [instTopologicalSpaceProd, induced_inf, induced_compose]; rfl⟩

中文:
定理 isInducing_toProd
  结论: 是Inducing (全空间.toProd B F)
  证明: ⟨by simp only [instTopologicalSpaceProd, induced_inf, induced_compose]; rfl⟩

Depends on / 依赖: induced_compose, induced_inf, instTopologicalSpaceProd
-/
theorem isInducing_toProd : IsInducing (TotalSpace.toProd B F) :=
  ⟨by simp only [instTopologicalSpaceProd, induced_inf, induced_compose]; rfl⟩

/-- Homeomorphism between the total space of the trivial bundle and the Cartesian product. -/
@[simps!]
/--
Definition of `homeomorphProd` / `homeomorphProd` 的定义

English:
definition homeomorphProd
  signature: : TotalSpace F (Trivial B F) ≃ₜ B × F
  body: (TotalSpace.toProd _ _).toHomeomorphOfIsInducing (isInducing_toProd B F)

中文:
定义 homeomorphProd
  签名: : 全空间 F (平凡 B F) ≃ₜ B × F
  定义体: (TotalSpace.toProd _ _).toHomeomorphOfIsInducing (isInducing_toProd B F)

Depends on / 依赖: TotalSpace, TotalSpace.toProd, isInducing_toProd, toHomeomorphOfIsInducing, toProd
-/
def homeomorphProd : TotalSpace F (Trivial B F) ≃ₜ B × F :=
  (TotalSpace.toProd _ _).toHomeomorphOfIsInducing (isInducing_toProd B F)

/-- Local trivialization for trivial bundle. -/
@[simps!]
/--
Definition of `trivialization` / `trivialization` 的定义

English:
definition trivialization
  signature: : Trivialization F (π F (Bundle.Trivial B F)) where
  body: (homeomorphProd B F).toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := univ_prod_univ.symm
  proj_toFun _ _ := rfl

中文:
定义 trivialization
  签名: : Trivialization F (π F (Bundle.平凡 B F)) where
  定义体: (homeomorphProd B F).toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := univ_prod_univ.symm
  proj_toFun _ _ := rfl

Depends on / 依赖: homeomorphProd, toOpenPartialHomeomorph
-/
def trivialization : Trivialization F (π F (Bundle.Trivial B F)) where
  toOpenPartialHomeomorph := (homeomorphProd B F).toOpenPartialHomeomorph
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := univ_prod_univ.symm
  proj_toFun _ _ := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `trivialization_symm_apply` / 引理 `trivialization_symm_apply`

English:
lemma trivialization_symm_apply
  given: [Zero F] (b : B) (f : F)
  proof: by
  simp [trivialization, homeomorphProd, TotalSpace.toProd, Trivialization.symm,
    Pretrivialization.symm, Trivialization.toPretrivialization]

中文:
引理 trivialization_symm_apply
  条件: [零 F] (b : B) (f : F)
  证明: by
  simp [trivialization, homeomorphProd, TotalSpace.toProd, Trivialization.symm,
    Pretrivialization.symm, Trivialization.toPretrivialization]
-/
@[simp] lemma trivialization_symm_apply [Zero F] (b : B) (f : F) :
    (trivialization B F).symm b f = f := by
  simp [trivialization, homeomorphProd, TotalSpace.toProd, Trivialization.symm,
    Pretrivialization.symm, Trivialization.toPretrivialization]

/--
lemma `toOpenPartialHomeomorph_trivialization_symm_apply` / 引理 `toOpenPartialHomeomorph_trivialization_symm_apply`

English:
lemma toOpenPartialHomeomorph_trivialization_symm_apply
  given: (v : B × F)
  proof: rfl

中文:
引理 toOpenPartialHomeomorph_trivialization_symm_apply
  条件: (v : B × F)
  证明: rfl
-/
@[simp] lemma toOpenPartialHomeomorph_trivialization_symm_apply (v : B × F) :
    (trivialization B F).toOpenPartialHomeomorph.symm v = ⟨v.1, v.2⟩ := rfl

/--
Instance `fiberBundle` / 实例 `fiberBundle`

English:
instance fiberBundle
  signature: : FiberBundle F (Bundle.Trivial B F) where
  body: {trivialization B F}
  trivializationAt' _ := trivialization B F
  mem_baseSet_trivializationAt' := mem_univ
  trivialization_mem_atlas' _ := mem_singleton _
  totalSpaceMk_isInducing' _ := (homeomorphProd B F).symm.isInducing.comp
    (isInducing_const_prod.2 .id)

中文:
实例 fiberBundle
  签名: : 纤维丛 F (Bundle.平凡 B F) where
  定义体: {trivialization B F}
  trivializationAt' _ := trivialization B F
  mem_baseSet_trivializationAt' := mem_univ
  trivialization_mem_atlas' _ := mem_singleton _
  totalSpaceMk_isInducing' _ := (homeomorphProd B F).symm.isInducing.comp
    (isInducing_const_prod.2 .id)
-/
@[simps] instance fiberBundle : FiberBundle F (Bundle.Trivial B F) where
  trivializationAtlas' := {trivialization B F}
  trivializationAt' _ := trivialization B F
  mem_baseSet_trivializationAt' := mem_univ
  trivialization_mem_atlas' _ := mem_singleton _
  totalSpaceMk_isInducing' _ := (homeomorphProd B F).symm.isInducing.comp
    (isInducing_const_prod.2 .id)

/--
theorem `eq_trivialization` / 定理 `eq_trivialization`

English:
theorem eq_trivialization
  statement: (e : Trivialization F (π F (Bundle.Trivial B F)))
  proof: i.out

中文:
定理 eq_trivialization
  结论: (e : Trivialization F (π F (Bundle.平凡 B F)))
  证明: i.out

Depends on / 依赖: i.out
-/
theorem eq_trivialization (e : Trivialization F (π F (Bundle.Trivial B F)))
    [i : MemTrivializationAtlas e] : e = trivialization B F := i.out

end Trivial

end Bundle

/-! ### Fibrewise product of two bundles -/


section Prod

variable {B : Type*}

section Defs

variable (F₁ : Type*) (E₁ : B -> Type*) (F₂ : Type*) (E₂ : B -> Type*)
variable [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]

/--
Instance `FiberBundle.Prod.topologicalSpace` / 实例 `FiberBundle.Prod.topologicalSpace`

English:
instance FiberBundle.Prod.topologicalSpace
  signature: : TopologicalSpace (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂))
  body: TopologicalSpace.induced
    (fun p => ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂)))
    inferInstance

中文:
实例 纤维丛.积类型.topologicalSpace
  签名: : 拓扑空间 (全空间 (F₁ × F₂) (E₁ ×ᵇ E₂))
  定义体: TopologicalSpace.induced
    (fun p => ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂)))
    inferInstance

Depends on / 依赖: TopologicalSpace, TopologicalSpace.induced, TotalSpace, induced
-/
instance FiberBundle.Prod.topologicalSpace : TopologicalSpace (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :=
  TopologicalSpace.induced
    (fun p => ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂)))
    inferInstance

/--
theorem `FiberBundle.Prod.isInducing_diag` / 定理 `FiberBundle.Prod.isInducing_diag`

English:
theorem FiberBundle.Prod.isInducing_diag
  proof: ⟨rfl⟩

中文:
定理 纤维丛.积类型.isInducing_diag
  证明: ⟨rfl⟩
-/
theorem FiberBundle.Prod.isInducing_diag :
    IsInducing (fun p => (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
      TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) -> TotalSpace F₁ E₁ × TotalSpace F₂ E₂) :=
  ⟨rfl⟩

end Defs

open FiberBundle

variable [TopologicalSpace B] (F₁ : Type*) [TopologicalSpace F₁] (E₁ : B -> Type*)
  [TopologicalSpace (TotalSpace F₁ E₁)] (F₂ : Type*) [TopologicalSpace F₂] (E₂ : B -> Type*)
  [TopologicalSpace (TotalSpace F₂ E₂)]

namespace Bundle.Trivialization

variable {F₁ E₁ F₂ E₂}
variable (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))

/--
Definition of `Prod.toFun'` / `Prod.toFun'` 的定义

English:
definition Prod.toFun'
  signature: : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) -> B × F₁ × F₂
  body: fun p => ⟨p.1, (e₁ ⟨p.1, p.2.1⟩).2, (e₂ ⟨p.1, p.2.2⟩).2⟩

中文:
定义 积类型.toFun'
  签名: : 全空间 (F₁ × F₂) (E₁ ×ᵇ E₂) -> B × F₁ × F₂
  定义体: fun p => ⟨p.1, (e₁ ⟨p.1, p.2.1⟩).2, (e₂ ⟨p.1, p.2.2⟩).2⟩
-/
def Prod.toFun' : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) -> B × F₁ × F₂ :=
  fun p => ⟨p.1, (e₁ ⟨p.1, p.2.1⟩).2, (e₂ ⟨p.1, p.2.2⟩).2⟩

variable {e₁ e₂}

/--
theorem `Prod.continuous_to_fun` / 定理 `Prod.continuous_to_fun`

English:
theorem Prod.continuous_to_fun
  statement: ContinuousOn (Prod.toFun' e₁ e₂)
  proof: by
  let f₁ : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) -> TotalSpace F₁ E₁ × TotalSpace F₂ E₂ :=
    fun p => ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂))
  let f₂ : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ -> (B × F₁) × B × F₂ := fun p => ⟨e₁ p.1, e₂ p.2⟩
  let f₃ : (B × F₁) × B × F₂ ->

中文:
定理 积类型.continuous_to_fun
  结论: ContinuousOn (积类型.toFun' e₁ e₂)
  证明: by
  let f₁ : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) -> TotalSpace F₁ E₁ × TotalSpace F₂ E₂ :=
    fun p => ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂))
  let f₂ : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ -> (B × F₁) × B × F₂ := fun p => ⟨e₁ p.1, e₂ p.2⟩
  let f₃ : (B × F₁) × B × F₂ ->

Depends on / 依赖: Continuous, ContinuousOn, Prod.isInducing_diag, TotalSpace, continu, continuous, isInducing_diag, source, toOpenPartialHomeomorph, toOpenPartialHomeomorph.continu
-/
theorem Prod.continuous_to_fun : ContinuousOn (Prod.toFun' e₁ e₂)
    (π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet inter e₂.baseSet)) := by
  let f₁ : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) -> TotalSpace F₁ E₁ × TotalSpace F₂ E₂ :=
    fun p => ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂))
  let f₂ : TotalSpace F₁ E₁ × TotalSpace F₂ E₂ -> (B × F₁) × B × F₂ := fun p => ⟨e₁ p.1, e₂ p.2⟩
  let f₃ : (B × F₁) × B × F₂ -> B × F₁ × F₂ := fun p => ⟨p.1.1, p.1.2, p.2.2⟩
  have hf₁ : Continuous f₁ := (Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous
  have hf₂ : ContinuousOn f₂ (e₁.source ×ˢ e₂.source) :=
    e₁.toOpenPartialHomeomorph.continuousOn.prodMap e₂.toOpenPartialHomeomorph.continuousOn
  have hf₃ : Continuous f₃ := by fun_prop
  refine ((hf₃.comp_continuousOn hf₂).comp hf₁.continuousOn ?_).congr ?_
  · rw [e₁.source_eq, e₂.source_eq]
    exact mapsTo_preimage _ _
  rintro ⟨b, v₁, v₂⟩ ⟨hb₁, _⟩
  simp only [f₁, f₂, f₃, Prod.toFun', Prod.mk_inj, Function.comp_apply, and_true]
  rw [e₁.coe_fst]
  rw [e₁.source_eq]; rw [mem_preimage]
  exact hb₁

variable (e₁ e₂) [forall x, Zero (E₁ x)] [forall x, Zero (E₂ x)]

/--
Definition of `Prod.invFun'` / `Prod.invFun'` 的定义

English:
definition Prod.invFun'
  signature: (p : B × F₁ × F₂)
  body: ⟨p.1, e₁.symm p.1 p.2.1, e₂.symm p.1 p.2.2⟩

中文:
定义 积类型.invFun'
  签名: (p : B × F₁ × F₂)
  定义体: ⟨p.1, e₁.symm p.1 p.2.1, e₂.symm p.1 p.2.2⟩
-/
noncomputable def Prod.invFun' (p : B × F₁ × F₂) : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) :=
  ⟨p.1, e₁.symm p.1 p.2.1, e₂.symm p.1 p.2.2⟩

variable {e₁ e₂}

/--
theorem `Prod.left_inv` / 定理 `Prod.left_inv`

English:
theorem Prod.left_inv
  statement: {x : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)}
  proof: by
  obtain ⟨x, v₁, v₂⟩ := x
  obtain ⟨h₁ : x in e₁.baseSet, h₂ : x in e₂.baseSet⟩ := h
  simp [Prod.toFun', Prod.invFun', h₁, h₂]

中文:
定理 积类型.left_inv
  结论: {x : 全空间 (F₁ × F₂) (E₁ ×ᵇ E₂)}
  证明: by
  obtain ⟨x, v₁, v₂⟩ := x
  obtain ⟨h₁ : x in e₁.baseSet, h₂ : x in e₂.baseSet⟩ := h
  simp [Prod.toFun', Prod.invFun', h₁, h₂]

Depends on / 依赖: Prod.invFun, Prod.toFun, baseSet, invFun
-/
theorem Prod.left_inv {x : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)}
    (h : x in π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet inter e₂.baseSet)) :
    Prod.invFun' e₁ e₂ (Prod.toFun' e₁ e₂ x) = x := by
  obtain ⟨x, v₁, v₂⟩ := x
  obtain ⟨h₁ : x in e₁.baseSet, h₂ : x in e₂.baseSet⟩ := h
  simp [Prod.toFun', Prod.invFun', h₁, h₂]

/--
theorem `Prod.right_inv` / 定理 `Prod.right_inv`

English:
theorem Prod.right_inv
  statement: {x : B × F₁ × F₂}
  proof: by
  obtain ⟨x, w₁, w₂⟩ := x
  obtain ⟨⟨h₁ : x in e₁.baseSet, h₂ : x in e₂.baseSet⟩, -⟩ := h
  simp [Prod.toFun', Prod.invFun', h₁, h₂]

中文:
定理 积类型.right_inv
  结论: {x : B × F₁ × F₂}
  证明: by
  obtain ⟨x, w₁, w₂⟩ := x
  obtain ⟨⟨h₁ : x in e₁.baseSet, h₂ : x in e₂.baseSet⟩, -⟩ := h
  simp [Prod.toFun', Prod.invFun', h₁, h₂]

Depends on / 依赖: Prod.invFun, Prod.toFun, baseSet, invFun
-/
theorem Prod.right_inv {x : B × F₁ × F₂}
    (h : x in (e₁.baseSet inter e₂.baseSet) ×ˢ (univ : Set (F₁ × F₂))) :
    Prod.toFun' e₁ e₂ (Prod.invFun' e₁ e₂ x) = x := by
  obtain ⟨x, w₁, w₂⟩ := x
  obtain ⟨⟨h₁ : x in e₁.baseSet, h₂ : x in e₂.baseSet⟩, -⟩ := h
  simp [Prod.toFun', Prod.invFun', h₁, h₂]

/--
theorem `Prod.continuous_inv_fun` / 定理 `Prod.continuous_inv_fun`

English:
theorem Prod.continuous_inv_fun
  proof: by
  rw [(Prod.isInducing_diag F₁ E₁ F₂ E₂).continuousOn_iff]
  have H₁ : Continuous fun p : B × F₁ × F₂ => ((p.1, p.2.1), (p.1, p.2.2)) := by fun_prop
  refine (e₁.continuousOn_symm.prodMap e₂.continuousOn_symm).comp H₁.continuousOn ?_
  exact fun x h => ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩

中文:
定理 积类型.continuous_inv_fun
  证明: by
  rw [(Prod.isInducing_diag F₁ E₁ F₂ E₂).continuousOn_iff]
  have H₁ : Continuous fun p : B × F₁ × F₂ => ((p.1, p.2.1), (p.1, p.2.2)) := by fun_prop
  refine (e₁.continuousOn_symm.prodMap e₂.continuousOn_symm).comp H₁.continuousOn ?_
  exact fun x h => ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩

Depends on / 依赖: Continuous, Prod.isInducing_diag, continuousOn, continuousOn_iff, continuousOn_symm, continuousOn_symm.prodMap, fun_prop, isInducing_diag, mem_univ, prodMap
-/
theorem Prod.continuous_inv_fun :
    ContinuousOn (Prod.invFun' e₁ e₂) ((e₁.baseSet inter e₂.baseSet) ×ˢ univ) := by
  rw [(Prod.isInducing_diag F₁ E₁ F₂ E₂).continuousOn_iff]
  have H₁ : Continuous fun p : B × F₁ × F₂ => ((p.1, p.2.1), (p.1, p.2.2)) := by fun_prop
  refine (e₁.continuousOn_symm.prodMap e₂.continuousOn_symm).comp H₁.continuousOn ?_
  exact fun x h => ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩

variable (e₁ e₂)

/-- Given trivializations `e₁`, `e₂` for bundle types `E₁`, `E₂` over a base `B`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`, whose base set is
`e₁.baseSet ∩ e₂.baseSet`. -/
@[simps!]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂)) where
  body: Prod.toFun' e₁ e₂
  invFun := Prod.invFun' e₁ e₂
  source := π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet inter e₂.baseSet)
  target := (e₁.baseSet inter e₂.baseSet) ×ˢ Set.univ
  map_source' _ h := ⟨h, Set.mem_univ _⟩
  map_target' _ h := h.1
  left_inv' _ := Prod.left_inv
  right_inv' _ := Prod.right_in

中文:
定义 乘积
  签名: : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂)) where
  定义体: Prod.toFun' e₁ e₂
  invFun := Prod.invFun' e₁ e₂
  source := π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet inter e₂.baseSet)
  target := (e₁.baseSet inter e₂.baseSet) ×ˢ Set.univ
  map_source' _ h := ⟨h, Set.mem_univ _⟩
  map_target' _ h := h.1
  left_inv' _ := Prod.left_inv
  right_inv' _ := Prod.right_in

Depends on / 依赖: Prod.toFun
-/
noncomputable def prod : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂)) where
  toFun := Prod.toFun' e₁ e₂
  invFun := Prod.invFun' e₁ e₂
  source := π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet inter e₂.baseSet)
  target := (e₁.baseSet inter e₂.baseSet) ×ˢ Set.univ
  map_source' _ h := ⟨h, Set.mem_univ _⟩
  map_target' _ h := h.1
  left_inv' _ := Prod.left_inv
  right_inv' _ := Prod.right_inv
  open_source := by
    convert!
      (e₁.open_source.prod e₂.open_source).preimage
        (FiberBundle.Prod.isInducing_diag F₁ E₁ F₂ E₂).continuous
    ext x
    simp only [Trivialization.source_eq, mfld_simps]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).prod isOpen_univ
  continuousOn_toFun := Prod.continuous_to_fun
  continuousOn_invFun := Prod.continuous_inv_fun
  baseSet := e₁.baseSet inter e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

/--
theorem `prod_symm_apply` / 定理 `prod_symm_apply`

English:
theorem prod_symm_apply
  given: (x : B) (w₁ : F₁) (w₂ : F₂)
  proof: rfl

中文:
定理 prod_symm_apply
  条件: (x : B) (w₁ : F₁) (w₂ : F₂)
  证明: rfl
-/
theorem prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) :
    (prod e₁ e₂).toPartialEquiv.symm (x, w₁, w₂) = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩ := rfl

end Bundle.Trivialization

open Bundle Trivialization

variable [forall x, Zero (E₁ x)] [forall x, Zero (E₂ x)] [forall x : B, TopologicalSpace (E₁ x)]
  [forall x : B, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

/--
Instance `FiberBundle.prod` / 实例 `FiberBundle.prod`

English:
instance FiberBundle.prod
  signature: : FiberBundle (F₁ × F₂) (E₁ ×ᵇ E₂) where
  body: by
    rw [← (Prod.isInducing_diag F₁ E₁ F₂ E₂).of_comp_iff]
    exact (totalSpaceMk_isInducing F₁ E₁ b).prodMap (totalSpaceMk_isInducing F₂ E₂ b)
  trivializationAtlas' := { e |
    exists (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_

中文:
实例 纤维丛.乘积
  签名: : 纤维丛 (F₁ × F₂) (E₁ ×ᵇ E₂) where
  定义体: by
    rw [← (Prod.isInducing_diag F₁ E₁ F₂ E₂).of_comp_iff]
    exact (totalSpaceMk_isInducing F₁ E₁ b).prodMap (totalSpaceMk_isInducing F₂ E₂ b)
  trivializationAtlas' := { e |
    exists (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_
-/
@[simps] noncomputable instance FiberBundle.prod : FiberBundle (F₁ × F₂) (E₁ ×ᵇ E₂) where
  totalSpaceMk_isInducing' b := by
    rw [← (Prod.isInducing_diag F₁ E₁ F₂ E₂).of_comp_iff]
    exact (totalSpaceMk_isInducing F₁ E₁ b).prodMap (totalSpaceMk_isInducing F₂ E₂ b)
  trivializationAtlas' := { e |
    exists (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
      (_ : MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂),
      e = Trivialization.prod e₁ e₂ }
  trivializationAt' b := (trivializationAt F₁ E₁ b).prod (trivializationAt F₂ E₂ b)
  mem_baseSet_trivializationAt' b :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ b, mem_baseSet_trivializationAt F₂ E₂ b⟩
  trivialization_mem_atlas' b :=
    ⟨trivializationAt F₁ E₁ b, trivializationAt F₂ E₂ b, inferInstance, inferInstance, rfl⟩

instance {e₁ : Trivialization F₁ (π F₁ E₁)} {e₂ : Trivialization F₂ (π F₂ E₂)}
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] :
    MemTrivializationAtlas (e₁.prod e₂ : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂))) where
  out := ⟨e₁, e₂, inferInstance, inferInstance, rfl⟩

end Prod

/-! ### Pullbacks of fiber bundles -/

open Bundle

section

universe u v w₁ w₂ U

variable {B : Type u} (F : Type v) (E : B -> Type w₁) {B' : Type w₂} (f : B' -> B)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: x
  body: inferInstanceAs (forall x, TopologicalSpace (E (f x)))

中文:
实例 [对任意
  签名: x
  定义体: inferInstanceAs (forall x, TopologicalSpace (E (f x)))

Depends on / 依赖: TopologicalSpace
-/
instance [forall x : B, TopologicalSpace (E x)] : forall x : B', TopologicalSpace ((f *ᵖ E) x) :=
  inferInstanceAs (forall x, TopologicalSpace (E (f x)))

variable [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)]

-- adding `@[instance_reducible]` causes downstream breakage
set_option warn.classDefReducibility false in
/-- Definition of `Pullback.TotalSpace.topologicalSpace`, which we make irreducible. -/
irreducible_def pullbackTopology : TopologicalSpace (TotalSpace F (f *ᵖ E)) :=
  induced TotalSpace.proj ‹TopologicalSpace B'› ⊓
    induced (Pullback.lift f) ‹TopologicalSpace (TotalSpace F E)›

/--
Instance `Pullback.TotalSpace.topologicalSpace` / 实例 `Pullback.TotalSpace.topologicalSpace`

English:
instance Pullback.TotalSpace.topologicalSpace
  signature: : TopologicalSpace (TotalSpace F (f *ᵖ E))
  body: pullbackTopology F E f

中文:
实例 拉回.全空间.topologicalSpace
  签名: : 拓扑空间 (全空间 F (f *ᵖ E))
  定义体: pullbackTopology F E f

Depends on / 依赖: pullbackTopology
-/
instance Pullback.TotalSpace.topologicalSpace : TopologicalSpace (TotalSpace F (f *ᵖ E)) :=
  pullbackTopology F E f

/--
theorem `Pullback.continuous_proj` / 定理 `Pullback.continuous_proj`

English:
theorem Pullback.continuous_proj
  given: (f : B' -> B)
  statement: Continuous (π F (f *ᵖ E))
  proof: by
  rw [continuous_iff_le_induced]; rw [Pullback.TotalSpace.topologicalSpace]; rw [pullbackTopology_def]
  exact inf_le_left

中文:
定理 拉回.continuous_proj
  条件: (f : B' -> B)
  结论: 连续 (π F (f *ᵖ E))
  证明: by
  rw [continuous_iff_le_induced]; rw [Pullback.TotalSpace.topologicalSpace]; rw [pullbackTopology_def]
  exact inf_le_left

Depends on / 依赖: Pullback, Pullback.TotalSpace.topologicalSpace, TotalSpace, continuous_iff_le_induced, inf_le_left, pullbackTopology_def, topologicalSpace
-/
theorem Pullback.continuous_proj (f : B' -> B) : Continuous (π F (f *ᵖ E)) := by
  rw [continuous_iff_le_induced]; rw [Pullback.TotalSpace.topologicalSpace]; rw [pullbackTopology_def]
  exact inf_le_left

/--
theorem `Pullback.continuous_lift` / 定理 `Pullback.continuous_lift`

English:
theorem Pullback.continuous_lift
  given: (f : B' -> B)
  statement: Continuous (@Pullback.lift B F E B' f)
  proof: by
  rw [continuous_iff_le_induced]; rw [Pullback.TotalSpace.topologicalSpace]; rw [pullbackTopology_def]
  exact inf_le_right

中文:
定理 拉回.continuous_lift
  条件: (f : B' -> B)
  结论: 连续 (@拉回.lift B F E B' f)
  证明: by
  rw [continuous_iff_le_induced]; rw [Pullback.TotalSpace.topologicalSpace]; rw [pullbackTopology_def]
  exact inf_le_right

Depends on / 依赖: Pullback, Pullback.TotalSpace.topologicalSpace, TotalSpace, continuous_iff_le_induced, inf_le_right, pullbackTopology_def, topologicalSpace
-/
theorem Pullback.continuous_lift (f : B' -> B) : Continuous (@Pullback.lift B F E B' f) := by
  rw [continuous_iff_le_induced]; rw [Pullback.TotalSpace.topologicalSpace]; rw [pullbackTopology_def]
  exact inf_le_right

/--
theorem `inducing_pullbackTotalSpaceEmbedding` / 定理 `inducing_pullbackTotalSpaceEmbedding`

English:
theorem inducing_pullbackTotalSpaceEmbedding
  given: (f : B' -> B)
  proof: by
  constructor
  simp_rw [instTopologicalSpaceProd, induced_inf, induced_compose,
    Pullback.TotalSpace.topologicalSpace, pullbackTopology_def]
  rfl

中文:
定理 inducing_pullbackTotalSpaceEmbedding
  条件: (f : B' -> B)
  证明: by
  constructor
  simp_rw [instTopologicalSpaceProd, induced_inf, induced_compose,
    Pullback.TotalSpace.topologicalSpace, pullbackTopology_def]
  rfl

Depends on / 依赖: Pullback, Pullback.TotalSpace.topologicalSpace, TotalSpace, induced_compose, induced_inf, instTopologicalSpaceProd, pullbackTopology_def, simp_rw, topologicalSpace
-/
theorem inducing_pullbackTotalSpaceEmbedding (f : B' -> B) :
    IsInducing (@pullbackTotalSpaceEmbedding B F E B' f) := by
  constructor
  simp_rw [instTopologicalSpaceProd, induced_inf, induced_compose,
    Pullback.TotalSpace.topologicalSpace, pullbackTopology_def]
  rfl

section FiberBundle

variable [TopologicalSpace F] [TopologicalSpace B]

/--
theorem `Pullback.continuous_totalSpaceMk` / 定理 `Pullback.continuous_totalSpaceMk`

English:
theorem Pullback.continuous_totalSpaceMk
  statement: [forall x, TopologicalSpace (E x)] [FiberBundle F E]
  proof: by
  simp only [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, induced_compose,
    induced_inf, Function.comp_def, induced_const, top_inf_eq, pullbackTopology_def]
  exact (FiberBundle.totalSpaceMk_isInducing F E (f x)).eq_induced.le

中文:
定理 拉回.continuous_totalSpaceMk
  结论: [对任意 x, 拓扑空间 (E x)] [纤维丛 F E]
  证明: by
  simp only [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, induced_compose,
    induced_inf, Function.comp_def, induced_const, top_inf_eq, pullbackTopology_def]
  exact (FiberBundle.totalSpaceMk_isInducing F E (f x)).eq_induced.le

Depends on / 依赖: FiberBundle, FiberBundle.totalSpaceMk_isInducing, Function, Function.comp_def, Pullback, Pullback.TotalSpace.topologicalSpace, TotalSpace, comp_def, continuous_iff_le_induced, eq_induced, eq_induced.le, induced_compose, induced_const, induced_inf, pullbackTopology_def, top_inf_eq, topologicalSpace, totalSpaceMk_isInducing
-/
theorem Pullback.continuous_totalSpaceMk [forall x, TopologicalSpace (E x)] [FiberBundle F E]
    {f : B' -> B} {x : B'} : Continuous (@TotalSpace.mk _ F (f *ᵖ E) x) := by
  simp only [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, induced_compose,
    induced_inf, Function.comp_def, induced_const, top_inf_eq, pullbackTopology_def]
  exact (FiberBundle.totalSpaceMk_isInducing F E (f x)).eq_induced.le

variable {E F}
variable [forall _b, Nonempty (E _b)] {K : Type U} [FunLike K B' B] [ContinuousMapClass K B' B]

set_option backward.isDefEq.respectTransparency false in
/-- A fiber bundle trivialization can be pulled back to a trivialization on the pullback bundle. -/
@[simps]
/--
Definition of `Bundle.Trivialization.pullback` / `Bundle.Trivialization.pullback` 的定义

English:
definition Bundle.Trivialization.pullback
  signature: (e : Trivialization F (π F E)) (f : K)
  body: (z.proj, (e (Pullback.lift f z)).2)
  invFun y := TotalSpace.mk' F y.1 (e.symm (f y.1) y.2)
  source := Pullback.lift f ⁻¹' e.source
  baseSet := f ⁻¹' e.baseSet
  target := (f ⁻¹' e.baseSet) ×ˢ univ
  map_source' x h := by
    simp_rw [e.source_eq, mem_preimage, Pullback.lift_proj] at h
    simp_rw

中文:
定义 Bundle.Trivialization.pullback
  签名: (e : Trivialization F (π F E)) (f : K)
  定义体: (z.proj, (e (Pullback.lift f z)).2)
  invFun y := TotalSpace.mk' F y.1 (e.symm (f y.1) y.2)
  source := Pullback.lift f ⁻¹' e.source
  baseSet := f ⁻¹' e.baseSet
  target := (f ⁻¹' e.baseSet) ×ˢ univ
  map_source' x h := by
    simp_rw [e.source_eq, mem_preimage, Pullback.lift_proj] at h
    simp_rw

Depends on / 依赖: Pullback, Pullback.lift, z.proj
-/
noncomputable def Bundle.Trivialization.pullback (e : Trivialization F (π F E)) (f : K) :
    Trivialization F (π F ((f : B' -> B) *ᵖ E)) where
  toFun z := (z.proj, (e (Pullback.lift f z)).2)
  invFun y := TotalSpace.mk' F y.1 (e.symm (f y.1) y.2)
  source := Pullback.lift f ⁻¹' e.source
  baseSet := f ⁻¹' e.baseSet
  target := (f ⁻¹' e.baseSet) ×ˢ univ
  map_source' x h := by
    simp_rw [e.source_eq, mem_preimage, Pullback.lift_proj] at h
    simp_rw [prodMk_mem_set_prod_eq, mem_univ, and_true, mem_preimage, h]
  map_target' y h := by
    rw [mem_prod]; rw [mem_preimage] at h
    simp_rw [e.source_eq, mem_preimage, Pullback.lift_proj, h.1]
  left_inv' x h := by
    simp_rw [mem_preimage, e.mem_source, Pullback.lift_proj] at h
    simp_rw [Pullback.lift, e.symm_apply_apply_mk h]
  right_inv' x h := by
    simp_rw [mem_prod, mem_preimage, mem_univ, and_true] at h
    simp_rw [Pullback.lift_mk, e.apply_mk_symm h]
  open_source := by
    simp_rw [e.source_eq, ← preimage_comp]
    exact e.open_baseSet.preimage ((map_continuous f).comp <| Pullback.continuous_proj F E f)
  open_target := ((map_continuous f).isOpen_preimage _ e.open_baseSet).prod isOpen_univ
  open_baseSet := (map_continuous f).isOpen_preimage _ e.open_baseSet
  continuousOn_toFun :=
    (Pullback.continuous_proj F E f).continuousOn.prodMk
      (continuous_snd.comp_continuousOn <|
        e.continuousOn.comp (Pullback.continuous_lift F E f).continuousOn Subset.rfl)
  continuousOn_invFun := by
    simp_rw [(inducing_pullbackTotalSpaceEmbedding F E f).continuousOn_iff, Function.comp_def,
      pullbackTotalSpaceEmbedding]
    exact continuousOn_fst.prodMk
      (e.continuousOn_symm.comp ((map_continuous f).prodMap continuous_id).continuousOn Subset.rfl)
  source_eq := by
    rw [e.source_eq]
    rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

@[simps]
/--
Instance `FiberBundle.pullback` / 实例 `FiberBundle.pullback`

English:
instance FiberBundle.pullback
  signature: [forall x, TopologicalSpace (E x)] [FiberBundle F E]
  body: (totalSpaceMk_isInducing F E (f x)).of_comp (Pullback.continuous_totalSpaceMk F E)
      (Pullback.continuous_lift F E f)
  trivializationAtlas' :=
    { ef | exists (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e), ef = e.pullback f }
  trivializationAt' x := (trivializationAt F E (f x

中文:
实例 纤维丛.pullback
  签名: [对任意 x, 拓扑空间 (E x)] [纤维丛 F E]
  定义体: (totalSpaceMk_isInducing F E (f x)).of_comp (Pullback.continuous_totalSpaceMk F E)
      (Pullback.continuous_lift F E f)
  trivializationAtlas' :=
    { ef | exists (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e), ef = e.pullback f }
  trivializationAt' x := (trivializationAt F E (f x

Depends on / 依赖: MemTrivializationAtlas, Pullback, Pullback.continuous_lift, Pullback.continuous_totalSpaceMk, Trivialization, continuous_lift, continuous_totalSpaceMk, e.pullback, mem_baseSet_trivializationAt, of_comp, pullback, totalSpaceMk_isInducing, trivializationAt, trivializationAtlas, trivialization_mem_atlas
-/
noncomputable instance FiberBundle.pullback [forall x, TopologicalSpace (E x)] [FiberBundle F E]
    (f : K) : FiberBundle F ((f : B' -> B) *ᵖ E) where
  totalSpaceMk_isInducing' x :=
    (totalSpaceMk_isInducing F E (f x)).of_comp (Pullback.continuous_totalSpaceMk F E)
      (Pullback.continuous_lift F E f)
  trivializationAtlas' :=
    { ef | exists (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e), ef = e.pullback f }
  trivializationAt' x := (trivializationAt F E (f x)).pullback f
  mem_baseSet_trivializationAt' x := mem_baseSet_trivializationAt F E (f x)
  trivialization_mem_atlas' x := ⟨trivializationAt F E (f x), inferInstance, rfl⟩

end FiberBundle

end
