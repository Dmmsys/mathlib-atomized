/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.PartialHomeomorph.Defs

/-!
# Partial homeomorphisms: basic theory


## Main definitions

* `PartialHomeomorph.refl`: the identity partial homeomorphism
* `IsEmbedding.toPartialHomeomorph`: an embedding of `X` into `Y`, with `X` nonempty,
  defines a partial homeomorphism whose source is all of `X`.
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace PartialHomeomorph

/-- The identity on the whole space as a partial homeomorphism. -/
@[simps! -fullyApplied apply, simps! -isSimp source target]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (X : Type*) [TopologicalSpace X]
  body: (Homeomorph.refl X).toPartialHomeomorph

@[simp]

中文:
定义 refl
  签名: (X : 类型) [拓扑空间 X]
  定义体: (Homeomorph.refl X).toPartialHomeomorph

@[simp]
-/
protected def refl (X : Type*) [TopologicalSpace X] : PartialHomeomorph X X :=
  (Homeomorph.refl X).toPartialHomeomorph

@[simp]
/--
theorem `refl_partialEquiv` / 定理 `refl_partialEquiv`

English:
theorem refl_partialEquiv
  statement: (PartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X
  proof: rfl

@[simp]

中文:
定理 refl_partialEquiv
  结论: (PartialHomeomorph.refl X).toPartialEquiv = 部分等价.refl X
  证明: rfl

@[simp]
-/
theorem refl_partialEquiv : (PartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X :=
  rfl

@[simp]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (PartialHomeomorph.refl X).symm = PartialHomeomorph.refl X
  proof: rfl

中文:
定理 refl_symm
  结论: (PartialHomeomorph.refl X).symm = PartialHomeomorph.refl X
  证明: rfl
-/
theorem refl_symm : (PartialHomeomorph.refl X).symm = PartialHomeomorph.refl X :=
  rfl

variable (e : PartialHomeomorph X Y)

/--
theorem `source_preimage_target` / 定理 `source_preimage_target`

English:
theorem source_preimage_target
  statement: e.source subseteq e ⁻¹' e.target
  proof: e.mapsTo

中文:
定理 source_preimage_target
  结论: e.source subseteq e ⁻¹' e.target
  证明: e.mapsTo

Depends on / 依赖: e.mapsTo, mapsTo
-/
theorem source_preimage_target : e.source subseteq e ⁻¹' e.target :=
  e.mapsTo

/--
theorem `image_eq_target_inter_inv_preimage` / 定理 `image_eq_target_inter_inv_preimage`

English:
theorem image_eq_target_inter_inv_preimage
  given: {s : Set X} (h : s subseteq e.source)
  proof: e.toPartialEquiv.image_eq_target_inter_inv_preimage h

中文:
定理 image_eq_target_inter_inv_preimage
  条件: {s : 集合 X} (h : s subseteq e.source)
  证明: e.toPartialEquiv.image_eq_target_inter_inv_preimage h

Depends on / 依赖: e.toPartialEquiv.image_eq_target_inter_inv_preimage, image_eq_target_inter_inv_preimage, toPartialEquiv
-/
theorem image_eq_target_inter_inv_preimage {s : Set X} (h : s subseteq e.source) :
    e '' s = e.target inter e.symm ⁻¹' s :=
  e.toPartialEquiv.image_eq_target_inter_inv_preimage h

/--
theorem `image_source_inter_eq'` / 定理 `image_source_inter_eq'`

English:
theorem image_source_inter_eq'
  given: (s : Set X)
  statement: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
  proof: e.toPartialEquiv.image_source_inter_eq' s

中文:
定理 image_source_inter_eq'
  条件: (s : 集合 X)
  结论: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
  证明: e.toPartialEquiv.image_source_inter_eq' s

Depends on / 依赖: e.toPartialEquiv.image_source_inter_eq, image_source_inter_eq, toPartialEquiv
-/
theorem image_source_inter_eq' (s : Set X) : e '' (e.source inter s) = e.target inter e.symm ⁻¹' s :=
  e.toPartialEquiv.image_source_inter_eq' s

/--
theorem `image_source_inter_eq` / 定理 `image_source_inter_eq`

English:
theorem image_source_inter_eq
  given: (s : Set X)
  proof: e.toPartialEquiv.image_source_inter_eq s

中文:
定理 image_source_inter_eq
  条件: (s : 集合 X)
  证明: e.toPartialEquiv.image_source_inter_eq s

Depends on / 依赖: e.toPartialEquiv.image_source_inter_eq, image_source_inter_eq, toPartialEquiv
-/
theorem image_source_inter_eq (s : Set X) :
    e '' (e.source inter s) = e.target inter e.symm ⁻¹' (e.source inter s) :=
  e.toPartialEquiv.image_source_inter_eq s

/--
theorem `symm_image_eq_source_inter_preimage` / 定理 `symm_image_eq_source_inter_preimage`

English:
theorem symm_image_eq_source_inter_preimage
  given: {s : Set Y} (h : s subseteq e.target)
  proof: e.symm.image_eq_target_inter_inv_preimage h

中文:
定理 symm_image_eq_source_inter_preimage
  条件: {s : 集合 Y} (h : s subseteq e.target)
  证明: e.symm.image_eq_target_inter_inv_preimage h

Depends on / 依赖: e.symm.image_eq_target_inter_inv_preimage, image_eq_target_inter_inv_preimage
-/
theorem symm_image_eq_source_inter_preimage {s : Set Y} (h : s subseteq e.target) :
    e.symm '' s = e.source inter e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h

/--
theorem `symm_image_target_inter_eq` / 定理 `symm_image_target_inter_eq`

English:
theorem symm_image_target_inter_eq
  given: (s : Set Y)
  proof: e.symm.image_source_inter_eq _

中文:
定理 symm_image_target_inter_eq
  条件: (s : 集合 Y)
  证明: e.symm.image_source_inter_eq _

Depends on / 依赖: e.symm.image_source_inter_eq, image_source_inter_eq
-/
theorem symm_image_target_inter_eq (s : Set Y) :
    e.symm '' (e.target inter s) = e.source inter e ⁻¹' (e.target inter s) :=
  e.symm.image_source_inter_eq _

/--
theorem `source_inter_preimage_inv_preimage` / 定理 `source_inter_preimage_inv_preimage`

English:
theorem source_inter_preimage_inv_preimage
  given: (s : Set X)
  proof: e.toPartialEquiv.source_inter_preimage_inv_preimage s

中文:
定理 source_inter_preimage_inv_preimage
  条件: (s : 集合 X)
  证明: e.toPartialEquiv.source_inter_preimage_inv_preimage s

Depends on / 依赖: e.toPartialEquiv.source_inter_preimage_inv_preimage, source_inter_preimage_inv_preimage, toPartialEquiv
-/
theorem source_inter_preimage_inv_preimage (s : Set X) :
    e.source inter e ⁻¹' (e.symm ⁻¹' s) = e.source inter s :=
  e.toPartialEquiv.source_inter_preimage_inv_preimage s

/--
theorem `target_inter_inv_preimage_preimage` / 定理 `target_inter_inv_preimage_preimage`

English:
theorem target_inter_inv_preimage_preimage
  given: (s : Set Y)
  proof: e.symm.source_inter_preimage_inv_preimage _

中文:
定理 target_inter_inv_preimage_preimage
  条件: (s : 集合 Y)
  证明: e.symm.source_inter_preimage_inv_preimage _

Depends on / 依赖: e.symm.source_inter_preimage_inv_preimage, source_inter_preimage_inv_preimage
-/
theorem target_inter_inv_preimage_preimage (s : Set Y) :
    e.target inter e.symm ⁻¹' (e ⁻¹' s) = e.target inter s :=
  e.symm.source_inter_preimage_inv_preimage _

/--
theorem `source_inter_preimage_target_inter` / 定理 `source_inter_preimage_target_inter`

English:
theorem source_inter_preimage_target_inter
  given: (s : Set Y)
  proof: e.toPartialEquiv.source_inter_preimage_target_inter s

中文:
定理 source_inter_preimage_target_inter
  条件: (s : 集合 Y)
  证明: e.toPartialEquiv.source_inter_preimage_target_inter s

Depends on / 依赖: e.toPartialEquiv.source_inter_preimage_target_inter, source_inter_preimage_target_inter, toPartialEquiv
-/
theorem source_inter_preimage_target_inter (s : Set Y) :
    e.source inter e ⁻¹' (e.target inter s) = e.source inter e ⁻¹' s :=
  e.toPartialEquiv.source_inter_preimage_target_inter s

/--
theorem `image_source_eq_target` / 定理 `image_source_eq_target`

English:
theorem image_source_eq_target
  statement: e '' e.source = e.target
  proof: e.toPartialEquiv.image_source_eq_target

中文:
定理 image_source_eq_target
  结论: e '' e.source = e.target
  证明: e.toPartialEquiv.image_source_eq_target

Depends on / 依赖: e.toPartialEquiv.image_source_eq_target, image_source_eq_target, toPartialEquiv
-/
theorem image_source_eq_target : e '' e.source = e.target :=
  e.toPartialEquiv.image_source_eq_target

/--
theorem `symm_image_target_eq_source` / 定理 `symm_image_target_eq_source`

English:
theorem symm_image_target_eq_source
  statement: e.symm '' e.target = e.source
  proof: e.symm.image_source_eq_target

中文:
定理 symm_image_target_eq_source
  结论: e.symm '' e.target = e.source
  证明: e.symm.image_source_eq_target

Depends on / 依赖: e.symm.image_source_eq_target, image_source_eq_target
-/
theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target

/-- A `PartialEquiv` which is continuous on its source and has open forward map (on its source) is a
`PartialHomeomorph`. -/
@[simps toPartialEquiv]
/--
Definition of `ofContinuousOpenRestrict` / `ofContinuousOpenRestrict` 的定义

English:
definition ofContinuousOpenRestrict
  signature: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
  body: e
  continuousOn_toFun := hc
  continuousOn_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn

@[simp]

中文:
定义 ofContinuousOpenRestrict
  签名: (e : 部分等价 X Y) (hc : ContinuousOn e e.source)
  定义体: e
  continuousOn_toFun := hc
  continuousOn_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn

@[simp]
-/
def ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) : PartialHomeomorph X Y where
  toPartialEquiv := e
  continuousOn_toFun := hc
  continuousOn_invFun := e.image_source_eq_target ▸ ho.continuousOn_image_of_leftInvOn e.leftInvOn

@[simp]
/--
theorem `coe_ofContinuousOpenRestrict` / 定理 `coe_ofContinuousOpenRestrict`

English:
theorem coe_ofContinuousOpenRestrict
  statement: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
  proof: rfl

@[simp]

中文:
定理 coe_ofContinuousOpenRestrict
  结论: (e : 部分等价 X Y) (hc : ContinuousOn e e.source)
  证明: rfl

@[simp]
-/
theorem coe_ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) : ⇑(ofContinuousOpenRestrict e hc ho) = e :=
  rfl

@[simp]
/--
theorem `coe_ofContinuousOpenRestrict_symm` / 定理 `coe_ofContinuousOpenRestrict_symm`

English:
theorem coe_ofContinuousOpenRestrict_symm
  statement: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
  proof: rfl

中文:
定理 coe_ofContinuousOpenRestrict_symm
  结论: (e : 部分等价 X Y) (hc : ContinuousOn e e.source)
  证明: rfl
-/
theorem coe_ofContinuousOpenRestrict_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) :
    ⇑(ofContinuousOpenRestrict e hc ho).symm = e.symm :=
  rfl

/-- A `PartialEquiv` which is continuous on its source and has open forward map (on its source) and
open source is a `PartialHomeomorph`. -/
@[simps! toPartialEquiv]
/--
Definition of `ofContinuousOpen` / `ofContinuousOpen` 的定义

English:
definition ofContinuousOpen
  signature: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
  body: ofContinuousOpenRestrict e hc (ho.domRestrict hs)

@[simp]

中文:
定义 ofContinuousOpen
  签名: (e : 部分等价 X Y) (hc : ContinuousOn e e.source) (ho : 是开映射 e)
  定义体: ofContinuousOpenRestrict e hc (ho.domRestrict hs)

@[simp]

Depends on / 依赖: domRestrict, ho.domRestrict, ofContinuousOpenRestrict
-/
def ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : PartialHomeomorph X Y :=
  ofContinuousOpenRestrict e hc (ho.domRestrict hs)

@[simp]
/--
theorem `coe_ofContinuousOpen` / 定理 `coe_ofContinuousOpen`

English:
theorem coe_ofContinuousOpen
  statement: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
  proof: rfl

@[simp]

中文:
定理 coe_ofContinuousOpen
  结论: (e : 部分等价 X Y) (hc : ContinuousOn e e.source)
  证明: rfl

@[simp]
-/
theorem coe_ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap e) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpen e hc ho hs) = e :=
  rfl

@[simp]
/--
theorem `coe_ofContinuousOpen_symm` / 定理 `coe_ofContinuousOpen_symm`

English:
theorem coe_ofContinuousOpen_symm
  statement: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
  proof: rfl

中文:
定理 coe_ofContinuousOpen_symm
  结论: (e : 部分等价 X Y) (hc : ContinuousOn e e.source)
  证明: rfl
-/
theorem coe_ofContinuousOpen_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap e) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpen e hc ho hs).symm = e.symm :=
  rfl

/-- The homeomorphism obtained by restricting a `PartialHomeomorph` to a subset of the source.
-/
@[simps]
/--
Definition of `homeomorphOfImageSubsetSource` / `homeomorphOfImageSubsetSource` 的定义

English:
definition homeomorphOfImageSubsetSource
  signature: {s : Set X} {t : Set Y} (hs : s subseteq e.source) (ht : e '' s = t)
  body: have h₁ : MapsTo e s t := mapsTo_iff_image_subset.2 ht.subset
  have h₂ : t subseteq e.target := ht ▸ e.image_source_eq_target ▸ image_mono hs
  have h₃ : MapsTo e.symm t s := ht ▸ forall_mem_image.2 fun _x hx =>
      (e.left_inv (hs hx)).symm ▸ hx
  { toFun := MapsTo.restrict e s t h₁
    invFun := MapsTo.restrict e.symm t s h₃
    left_inv := fun a => Subtype.ext (e.left_inv (hs a.2))
right_inv := fun b => Subtype.ext e.right_inv (h₂ b.2)
    continuous_toFun := (e.continuousOn.mono hs).mapsToRestrict h₁
    continuous_invFun := (e.continuousOn_symm.mono h₂).mapsToRestrict h₃ }

中文:
定义 homeomorphOfImageSubsetSource
  签名: {s : 集合 X} {t : 集合 Y} (hs : s subseteq e.source) (ht : e '' s = t)
  定义体: have h₁ : MapsTo e s t := mapsTo_iff_image_subset.2 ht.subset
  have h₂ : t subseteq e.target := ht ▸ e.image_source_eq_target ▸ image_mono hs
  have h₃ : MapsTo e.symm t s := ht ▸ forall_mem_image.2 fun _x hx =>
      (e.left_inv (hs hx)).symm ▸ hx
  { toFun := MapsTo.restrict e s t h₁
    invFun := MapsTo.restrict e.symm t s h₃
    left_inv := fun a => Subtype.ext (e.left_inv (hs a.2))
right_inv := fun b => Subtype.ext e.right_inv (h₂ b.2)
    continuous_toFun := (e.continuousOn.mono hs).mapsToRestrict h₁
    continuous_invFun := (e.continuousOn_symm.mono h₂).mapsToRestrict h₃ }

Depends on / 依赖: MapsTo, MapsTo.restrict, Subtype, Subtype.ext, continuousOn, continuous_, continuous_toFun, e.continuousOn.mono, e.image_source_eq_target, e.left_inv, e.right_inv, e.symm, e.target, forall_mem_image, ht.subset, image_mono, image_source_eq_target, invFun, left_inv, mapsToRestrict
-/
def homeomorphOfImageSubsetSource {s : Set X} {t : Set Y} (hs : s subseteq e.source) (ht : e '' s = t) :
    s ≃ₜ t :=
  have h₁ : MapsTo e s t := mapsTo_iff_image_subset.2 ht.subset
  have h₂ : t subseteq e.target := ht ▸ e.image_source_eq_target ▸ image_mono hs
  have h₃ : MapsTo e.symm t s := ht ▸ forall_mem_image.2 fun _x hx =>
      (e.left_inv (hs hx)).symm ▸ hx
  { toFun := MapsTo.restrict e s t h₁
    invFun := MapsTo.restrict e.symm t s h₃
    left_inv := fun a => Subtype.ext (e.left_inv (hs a.2))
right_inv := fun b => Subtype.ext e.right_inv (h₂ b.2)
    continuous_toFun := (e.continuousOn.mono hs).mapsToRestrict h₁
    continuous_invFun := (e.continuousOn_symm.mono h₂).mapsToRestrict h₃ }

/-- A partial homeomorphism defines a homeomorphism between its source and target. -/
@[simps!]
/--
Definition of `toHomeomorphSourceTarget` / `toHomeomorphSourceTarget` 的定义

English:
definition toHomeomorphSourceTarget
  signature: : e.source ≃ₜ e.target
  body: e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target

中文:
定义 toHomeomorphSourceTarget
  签名: : e.source ≃ₜ e.target
  定义体: e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target

Depends on / 依赖: e.homeomorphOfImageSubsetSource, e.image_source_eq_target, homeomorphOfImageSubsetSource, image_source_eq_target, subset_rfl
-/
def toHomeomorphSourceTarget : e.source ≃ₜ e.target :=
  e.homeomorphOfImageSubsetSource subset_rfl e.image_source_eq_target

/--
theorem `secondCountableTopology_source` / 定理 `secondCountableTopology_source`

English:
theorem secondCountableTopology_source
  given: [SecondCountableTopology Y]
  proof: e.toHomeomorphSourceTarget.secondCountableTopology

中文:
定理 secondCountableTopology_source
  条件: [第二可数拓扑 Y]
  证明: e.toHomeomorphSourceTarget.secondCountableTopology

Depends on / 依赖: e.toHomeomorphSourceTarget.secondCountableTopology, secondCountableTopology, toHomeomorphSourceTarget
-/
theorem secondCountableTopology_source [SecondCountableTopology Y] :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.secondCountableTopology

/-- If a partial homeomorphism has source and target equal to univ, then it induces a
homeomorphism between the whole spaces, expressed in this definition. -/
@[simps -fullyApplied apply symm_apply]
-- TODO: add a `PartialEquiv` version
/--
Definition of `toHomeomorphOfSourceEqUnivTargetEqUniv` / `toHomeomorphOfSourceEqUnivTargetEqUniv` 的定义

English:
definition toHomeomorphOfSourceEqUnivTargetEqUniv
  signature: (h : e.source = (univ : Set X)) (h' : e.target = univ)
  body: e
  invFun := e.symm
  left_inv x :=
e.left_inv by
      rw [h]
      exact mem_univ _
  right_inv x :=
e.right_inv by
      rw [h']
      exact mem_univ _
  continuous_toFun := by
    simpa only [continuousOn_univ, h] using e.continuousOn
  continuous_invFun := by
    simpa only [continuousOn_univ, h'] using e.continuousOn_symm

中文:
定义 toHomeomorphOfSourceEqUnivTargetEqUniv
  签名: (h : e.source = (univ : 集合 X)) (h' : e.target = univ)
  定义体: e
  invFun := e.symm
  left_inv x :=
e.left_inv by
      rw [h]
      exact mem_univ _
  right_inv x :=
e.right_inv by
      rw [h']
      exact mem_univ _
  continuous_toFun := by
    simpa only [continuousOn_univ, h] using e.continuousOn
  continuous_invFun := by
    simpa only [continuousOn_univ, h'] using e.continuousOn_symm
-/
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set X)) (h' : e.target = univ) :
    X ≃ₜ Y where
  toFun := e
  invFun := e.symm
  left_inv x :=
e.left_inv by
      rw [h]
      exact mem_univ _
  right_inv x :=
e.right_inv by
      rw [h']
      exact mem_univ _
  continuous_toFun := by
    simpa only [continuousOn_univ, h] using e.continuousOn
  continuous_invFun := by
    simpa only [continuousOn_univ, h'] using e.continuousOn_symm

/--
theorem `isEmbedding_restrict` / 定理 `isEmbedding_restrict`

English:
theorem isEmbedding_restrict
  statement: IsEmbedding (e.source.domRestrict e.toFun)
  proof: by
  rw [isEmbedding_iff]
  constructor
  · apply Topology.IsInducing.of_codRestrict (t := e.target) (by simp)
    rw [← PartialEquiv.toEquiv_eq_codRestrict_restrict]
    exact e.toHomeomorphSourceTarget.isInducing
  · rw [domRestrict_eq, toFun_eq_coe e, e.injOn.injective_iff e.source (by simp)]
    exact Subtype.val_injective

中文:
定理 isEmbedding_restrict
  结论: 是嵌入 (e.source.domRestrict e.toFun)
  证明: by
  rw [isEmbedding_iff]
  constructor
  · apply Topology.IsInducing.of_codRestrict (t := e.target) (by simp)
    rw [← PartialEquiv.toEquiv_eq_codRestrict_restrict]
    exact e.toHomeomorphSourceTarget.isInducing
  · rw [domRestrict_eq, toFun_eq_coe e, e.injOn.injective_iff e.source (by simp)]
    exact Subtype.val_injective

Depends on / 依赖: IsInducing, PartialEquiv, PartialEquiv.toEquiv_eq_codRestrict_restrict, Subtype, Subtype.val_injective, Topology, Topology.IsInducing.of_codRestrict, domRestrict_eq, e.injOn.injective_iff, e.source, e.target, e.toHomeomorphSourceTarget.isInducing, injective_iff, isEmbedding_iff, isInducing, of_codRestrict, source, target, toEquiv_eq_codRestrict_restrict, toFun_eq_coe
-/
theorem isEmbedding_restrict : IsEmbedding (e.source.domRestrict e.toFun) := by
  rw [isEmbedding_iff]
  constructor
  · apply Topology.IsInducing.of_codRestrict (t := e.target) (by simp)
    rw [← PartialEquiv.toEquiv_eq_codRestrict_restrict]
    exact e.toHomeomorphSourceTarget.isInducing
  · rw [domRestrict_eq, toFun_eq_coe e, e.injOn.injective_iff e.source (by simp)]
    exact Subtype.val_injective

/--
theorem `isEmbedding` / 定理 `isEmbedding`

English:
theorem isEmbedding
  given: (h : e.source = Set.univ)
  statement: IsEmbedding e
  proof: e.isEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isEmbedding

中文:
定理 isEmbedding
  条件: (h : e.source = 集合.univ)
  结论: 是嵌入 e
  证明: e.isEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isEmbedding

Depends on / 依赖: Homeomorph, Homeomorph.Set.univ, Homeomorph.setCongr, e.isEmbedding_restrict.comp, isEmbedding, isEmbedding_restrict, setCongr, symm.isEmbedding
-/
theorem isEmbedding (h : e.source = Set.univ) : IsEmbedding e :=
  e.isEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isEmbedding

/--
Definition of `ofIsHomeomorphToEquiv` / `ofIsHomeomorphToEquiv` 的定义

English:
definition ofIsHomeomorphToEquiv
  signature: (f : PartialEquiv X Y) (h : IsHomeomorph (f.toEquiv))
  body: f
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]; rw [← continuous_codRestrict_iff (s := f.target) (by simp)]
    exact h.continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]; rw [← continuous_codRestrict_iff (s := f.source) (by simp)]
    exact ((Equiv.isHomeomorph_iff _).1 h).2

中文:
定义 ofIsHomeomorphToEquiv
  签名: (f : 部分等价 X Y) (h : 是同胚 (f.toEquiv))
  定义体: f
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]; rw [← continuous_codRestrict_iff (s := f.target) (by simp)]
    exact h.continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]; rw [← continuous_codRestrict_iff (s := f.source) (by simp)]
    exact ((Equiv.isHomeomorph_iff _).1 h).2
-/
def ofIsHomeomorphToEquiv (f : PartialEquiv X Y) (h : IsHomeomorph (f.toEquiv)) :
    PartialHomeomorph X Y where
  toPartialEquiv := f
  continuousOn_toFun := by
    rw [continuousOn_iff_continuous_domRestrict]; rw [← continuous_codRestrict_iff (s := f.target) (by simp)]
    exact h.continuous
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]; rw [← continuous_codRestrict_iff (s := f.source) (by simp)]
    exact ((Equiv.isHomeomorph_iff _).1 h).2

end PartialHomeomorph

/-!
## Embeddings
-/

namespace Topology.IsEmbedding

variable (f : X -> Y) (h : IsEmbedding f)

/-- An embedding of `X` into `Y`, with `X` nonempty, defines a partial homeomorphism
whose source is all of `X`. The converse is also true; see `PartialHomeomorph.isEmbedding`. -/
@[simps! -fullyApplied apply source target]
/--
Definition of `toPartialHomeomorph` / `toPartialHomeomorph` 的定义

English:
definition toPartialHomeomorph
  signature: [Nonempty X]
  body: PartialHomeomorph.ofIsHomeomorphToEquiv (h.injective.injOn.toPartialEquiv f univ) (by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨?_, Equiv.surjective _⟩
    rw [PartialEquiv.toEquiv_eq_codRestrict_restrict]
    apply IsEmbedding.codRestrict
    simpa! [domRestrict_eq] using h.comp subtypeVal)

中文:
定义 toPartialHomeomorph
  签名: [非空 X]
  定义体: PartialHomeomorph.ofIsHomeomorphToEquiv (h.injective.injOn.toPartialEquiv f univ) (by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨?_, Equiv.surjective _⟩
    rw [PartialEquiv.toEquiv_eq_codRestrict_restrict]
    apply IsEmbedding.codRestrict
    simpa! [domRestrict_eq] using h.comp subtypeVal)

Depends on / 依赖: Equiv.surjective, IsEmbedding, IsEmbedding.codRestrict, PartialEquiv, PartialEquiv.toEquiv_eq_codRestrict_restrict, PartialHomeomorph, PartialHomeomorph.ofIsHomeomorphToEquiv, codRestrict, domRestrict_eq, h.comp, h.injective.injOn.toPartialEquiv, injective, isHomeomorph_iff_isEmbedding_surjective, ofIsHomeomorphToEquiv, subtypeVal, surjective, toEquiv_eq_codRestrict_restrict, toPartialEquiv
-/
noncomputable def toPartialHomeomorph [Nonempty X] : PartialHomeomorph X Y :=
  PartialHomeomorph.ofIsHomeomorphToEquiv (h.injective.injOn.toPartialEquiv f univ) (by
    rw [isHomeomorph_iff_isEmbedding_surjective]
    refine ⟨?_, Equiv.surjective _⟩
    rw [PartialEquiv.toEquiv_eq_codRestrict_restrict]
    apply IsEmbedding.codRestrict
    simpa! [domRestrict_eq] using h.comp subtypeVal)

variable [Nonempty X]

/--
lemma `toPartialHomeomorph_left_inv` / 引理 `toPartialHomeomorph_left_inv`

English:
lemma toPartialHomeomorph_left_inv
  given: {x : X}
  statement: (h.toPartialHomeomorph f).symm (f x) = x
  proof: by
  rw [← congr_fun (h.toPartialHomeomorph_apply f)]; rw [PartialHomeomorph.left_inv]
  exact Set.mem_univ _

中文:
引理 toPartialHomeomorph_left_inv
  条件: {x : X}
  结论: (h.toPartialHomeomorph f).symm (f x) = x
  证明: by
  rw [← congr_fun (h.toPartialHomeomorph_apply f)]; rw [PartialHomeomorph.left_inv]
  exact Set.mem_univ _

Depends on / 依赖: PartialHomeomorph, PartialHomeomorph.left_inv, Set.mem_univ, congr_fun, h.toPartialHomeomorph_apply, left_inv, mem_univ, toPartialHomeomorph_apply
-/
lemma toPartialHomeomorph_left_inv {x : X} : (h.toPartialHomeomorph f).symm (f x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f)]; rw [PartialHomeomorph.left_inv]
  exact Set.mem_univ _

/--
lemma `toPartialHomeomorph_right_inv` / 引理 `toPartialHomeomorph_right_inv`

English:
lemma toPartialHomeomorph_right_inv
  given: {x : Y} (hx : x in Set.range f)
  proof: by
  rw [← congr_fun (h.toPartialHomeomorph_apply f)]; rw [PartialHomeomorph.right_inv]
  rwa [toPartialHomeomorph_target]

中文:
引理 toPartialHomeomorph_right_inv
  条件: {x : Y} (hx : x in 集合.range f)
  证明: by
  rw [← congr_fun (h.toPartialHomeomorph_apply f)]; rw [PartialHomeomorph.right_inv]
  rwa [toPartialHomeomorph_target]

Depends on / 依赖: PartialHomeomorph, PartialHomeomorph.right_inv, congr_fun, h.toPartialHomeomorph_apply, right_inv, toPartialHomeomorph_apply, toPartialHomeomorph_target
-/
lemma toPartialHomeomorph_right_inv {x : Y} (hx : x in Set.range f) :
    f ((h.toPartialHomeomorph f).symm x) = x := by
  rw [← congr_fun (h.toPartialHomeomorph_apply f)]; rw [PartialHomeomorph.right_inv]
  rwa [toPartialHomeomorph_target]

end Topology.IsEmbedding

/-! inclusion of a set in a topological space -/
namespace Set

/- `Nonempty s` is not a type class argument because `s`, being a subset, rarely comes with a type
class instance. Then we'd have to manually provide the instance every time we use the following
lemmas, tediously using `haveI := ...` or `@foobar _ _ _ ...`. -/
variable (s : Set X) (hs : Nonempty s)

/--
Definition of `partialHomeomorphSubtypeCoe` / `partialHomeomorphSubtypeCoe` 的定义

English:
definition partialHomeomorphSubtypeCoe
  signature: : PartialHomeomorph s X
  body: IsEmbedding.subtypeVal.toPartialHomeomorph _

@[simp]

中文:
定义 partialHomeomorphSubtypeCoe
  签名: : PartialHomeomorph s X
  定义体: IsEmbedding.subtypeVal.toPartialHomeomorph _

@[simp]

Depends on / 依赖: IsEmbedding, IsEmbedding.subtypeVal.toPartialHomeomorph, subtypeVal, toPartialHomeomorph
-/
noncomputable def partialHomeomorphSubtypeCoe : PartialHomeomorph s X :=
  IsEmbedding.subtypeVal.toPartialHomeomorph _

@[simp]
/--
theorem `partialHomeomorphSubtypeCoe_coe` / 定理 `partialHomeomorphSubtypeCoe_coe`

English:
theorem partialHomeomorphSubtypeCoe_coe
  proof: rfl

@[simp]

中文:
定理 partialHomeomorphSubtypeCoe_coe
  证明: rfl

@[simp]
-/
theorem partialHomeomorphSubtypeCoe_coe :
    (s.partialHomeomorphSubtypeCoe hs : s -> X) = (↑) :=
  rfl

@[simp]
/--
theorem `partialHomeomorphSubtypeCoe_source` / 定理 `partialHomeomorphSubtypeCoe_source`

English:
theorem partialHomeomorphSubtypeCoe_source
  proof: rfl

@[simp]

中文:
定理 partialHomeomorphSubtypeCoe_source
  证明: rfl

@[simp]
-/
theorem partialHomeomorphSubtypeCoe_source :
    (s.partialHomeomorphSubtypeCoe hs).source = Set.univ :=
  rfl

@[simp]
/--
theorem `partialHomeomorphSubtypeCoe_target` / 定理 `partialHomeomorphSubtypeCoe_target`

English:
theorem partialHomeomorphSubtypeCoe_target
  proof: by
  simp [partialHomeomorphSubtypeCoe]

中文:
定理 partialHomeomorphSubtypeCoe_target
  证明: by
  simp [partialHomeomorphSubtypeCoe]

Depends on / 依赖: partialHomeomorphSubtypeCoe
-/
theorem partialHomeomorphSubtypeCoe_target :
    (s.partialHomeomorphSubtypeCoe hs).target = s := by
  simp [partialHomeomorphSubtypeCoe]

end Set
