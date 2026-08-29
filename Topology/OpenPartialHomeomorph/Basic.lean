/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Topology.PartialHomeomorph.Basic
/-!
# Partial homeomorphisms: basic theory


## Main definitions

* `OpenPartialHomeomorph.refl`: the identity open partial homeomorphism
* `Topology.IsOpenEmbedding.toOpenPartialHomeomorph`: construct an open partial homeomorphism from
  an open embedding
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

/-- The identity on the whole space as an open partial homeomorphism. -/
@[simps! (attr := mfld_simps) -fullyApplied apply, simps! -isSimp source target]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (X : Type*) [TopologicalSpace X]
  body: (Homeomorph.refl X).toOpenPartialHomeomorph

@[simp, mfld_simps]

中文:
定义 refl
  签名: (X : 类型) [TopologicalSpace X]
  定义体: (Homeomorph.refl X).toOpenPartialHomeomorph

@[simp, mfld_simps]
-/
protected def refl (X : Type*) [TopologicalSpace X] : OpenPartialHomeomorph X X :=
  (Homeomorph.refl X).toOpenPartialHomeomorph

@[simp, mfld_simps]
/--
theorem `refl_partialEquiv` / 定理 `refl_partialEquiv`

English:
theorem refl_partialEquiv
  statement: (OpenPartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X
  proof: rfl

@[simp, mfld_simps]

中文:
定理 refl_partialEquiv
  结论: (OpenPartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X
  证明: rfl

@[simp, mfld_simps]
-/
theorem refl_partialEquiv : (OpenPartialHomeomorph.refl X).toPartialEquiv = PartialEquiv.refl X :=
  rfl

@[simp, mfld_simps]
/--
theorem `refl_symm` / 定理 `refl_symm`

English:
theorem refl_symm
  statement: (OpenPartialHomeomorph.refl X).symm = OpenPartialHomeomorph.refl X
  proof: rfl

中文:
定理 refl_symm
  结论: (OpenPartialHomeomorph.refl X).symm = OpenPartialHomeomorph.refl X
  证明: rfl
-/
theorem refl_symm : (OpenPartialHomeomorph.refl X).symm = OpenPartialHomeomorph.refl X :=
  rfl

variable (e : OpenPartialHomeomorph X Y)

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
  条件: {s : Set X} (h : s subseteq e.source)
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
  条件: (s : Set X)
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
  条件: (s : Set X)
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
  条件: {s : Set Y} (h : s subseteq e.target)
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
  条件: (s : Set Y)
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
  条件: (s : Set X)
  证明: e.toPartialEquiv.source_inter_preimage_inv_preimage s

Depends on / 依赖: e.toPartialEquiv.source_inter_preimage_inv_preimage, source_inter_preimage_inv_preimage, toPartialEquiv
-/
theorem source_inter_preimage_inv_preimage (s : Set X) :
    e.source inter e ⁻¹' e.symm ⁻¹' s = e.source inter s :=
  e.toPartialEquiv.source_inter_preimage_inv_preimage s

/--
theorem `target_inter_inv_preimage_preimage` / 定理 `target_inter_inv_preimage_preimage`

English:
theorem target_inter_inv_preimage_preimage
  given: (s : Set Y)
  proof: e.symm.source_inter_preimage_inv_preimage _

中文:
定理 target_inter_inv_preimage_preimage
  条件: (s : Set Y)
  证明: e.symm.source_inter_preimage_inv_preimage _

Depends on / 依赖: e.symm.source_inter_preimage_inv_preimage, source_inter_preimage_inv_preimage
-/
theorem target_inter_inv_preimage_preimage (s : Set Y) :
    e.target inter e.symm ⁻¹' e ⁻¹' s = e.target inter s :=
  e.symm.source_inter_preimage_inv_preimage _

/--
theorem `source_inter_preimage_target_inter` / 定理 `source_inter_preimage_target_inter`

English:
theorem source_inter_preimage_target_inter
  given: (s : Set Y)
  proof: e.toPartialEquiv.source_inter_preimage_target_inter s

中文:
定理 source_inter_preimage_target_inter
  条件: (s : Set Y)
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

/--
theorem `isOpen_inter_preimage` / 定理 `isOpen_inter_preimage`

English:
theorem isOpen_inter_preimage
  given: {s : Set Y} (hs : IsOpen s)
  statement: IsOpen (e.source inter e ⁻¹' s)
  proof: e.continuousOn.isOpen_inter_preimage e.open_source hs

中文:
定理 isOpen_inter_preimage
  条件: {s : Set Y} (hs : IsOpen s)
  结论: IsOpen (e.source inter e ⁻¹' s)
  证明: e.continuousOn.isOpen_inter_preimage e.open_source hs

Depends on / 依赖: continuousOn, e.continuousOn.isOpen_inter_preimage, e.open_source, isOpen_inter_preimage, open_source
-/
theorem isOpen_inter_preimage {s : Set Y} (hs : IsOpen s) : IsOpen (e.source inter e ⁻¹' s) :=
  e.continuousOn.isOpen_inter_preimage e.open_source hs

/--
theorem `isOpen_inter_preimage_symm` / 定理 `isOpen_inter_preimage_symm`

English:
theorem isOpen_inter_preimage_symm
  given: {s : Set X} (hs : IsOpen s)
  statement: IsOpen (e.target inter e.symm ⁻¹' s)
  proof: e.symm.continuousOn.isOpen_inter_preimage e.open_target hs

中文:
定理 isOpen_inter_preimage_symm
  条件: {s : Set X} (hs : IsOpen s)
  结论: IsOpen (e.target inter e.symm ⁻¹' s)
  证明: e.symm.continuousOn.isOpen_inter_preimage e.open_target hs

Depends on / 依赖: continuousOn, e.open_target, e.symm.continuousOn.isOpen_inter_preimage, isOpen_inter_preimage, open_target
-/
theorem isOpen_inter_preimage_symm {s : Set X} (hs : IsOpen s) : IsOpen (e.target inter e.symm ⁻¹' s) :=
  e.symm.continuousOn.isOpen_inter_preimage e.open_target hs

/--
lemma `isOpen_image_of_subset_source` / 引理 `isOpen_image_of_subset_source`

English:
lemma isOpen_image_of_subset_source
  given: {s : Set X} (hs : IsOpen s) (hse : s subseteq e.source)
  proof: by
  rw [(image_eq_target_inter_inv_preimage (e := e) hse)]
  exact e.continuousOn_invFun.isOpen_inter_preimage e.open_target hs

中文:
引理 isOpen_image_of_subset_source
  条件: {s : Set X} (hs : IsOpen s) (hse : s subseteq e.source)
  证明: by
  rw [(image_eq_target_inter_inv_preimage (e := e) hse)]
  exact e.continuousOn_invFun.isOpen_inter_preimage e.open_target hs

Depends on / 依赖: continuousOn_invFun, e.continuousOn_invFun.isOpen_inter_preimage, e.open_target, image_eq_target_inter_inv_preimage, isOpen_inter_preimage, open_target
-/
lemma isOpen_image_of_subset_source {s : Set X} (hs : IsOpen s) (hse : s subseteq e.source) :
    IsOpen (e '' s) := by
  rw [(image_eq_target_inter_inv_preimage (e := e) hse)]
  exact e.continuousOn_invFun.isOpen_inter_preimage e.open_target hs

/--
theorem `isOpen_image_source_inter` / 定理 `isOpen_image_source_inter`

English:
theorem isOpen_image_source_inter
  given: {s : Set X} (hs : IsOpen s)
  proof: e.isOpen_image_of_subset_source (e.open_source.inter hs) inter_subset_left

中文:
定理 isOpen_image_source_inter
  条件: {s : Set X} (hs : IsOpen s)
  证明: e.isOpen_image_of_subset_source (e.open_source.inter hs) inter_subset_left

Depends on / 依赖: e.isOpen_image_of_subset_source, e.open_source.inter, inter_subset_left, isOpen_image_of_subset_source, open_source
-/
theorem isOpen_image_source_inter {s : Set X} (hs : IsOpen s) :
    IsOpen (e '' (e.source inter s)) :=
  e.isOpen_image_of_subset_source (e.open_source.inter hs) inter_subset_left

/--
lemma `isOpen_image_symm_of_subset_target` / 引理 `isOpen_image_symm_of_subset_target`

English:
lemma isOpen_image_symm_of_subset_target
  given: {t : Set Y} (ht : IsOpen t) (hte : t subseteq e.target)
  proof: isOpen_image_of_subset_source e.symm ht (e.symm_source ▸ hte)

中文:
引理 isOpen_image_symm_of_subset_target
  条件: {t : Set Y} (ht : IsOpen t) (hte : t subseteq e.target)
  证明: isOpen_image_of_subset_source e.symm ht (e.symm_source ▸ hte)

Depends on / 依赖: e.symm, e.symm_source, isOpen_image_of_subset_source, symm_source
-/
lemma isOpen_image_symm_of_subset_target {t : Set Y} (ht : IsOpen t) (hte : t subseteq e.target) :
    IsOpen (e.symm '' t) :=
  isOpen_image_of_subset_source e.symm ht (e.symm_source ▸ hte)

/--
lemma `isOpen_symm_image_iff_of_subset_target` / 引理 `isOpen_symm_image_iff_of_subset_target`

English:
lemma isOpen_symm_image_iff_of_subset_target
  given: {t : Set Y} (hs : t subseteq e.target)
  proof: by
  refine ⟨fun h => ?_, fun h => e.symm.isOpen_image_of_subset_source h hs⟩
  have hs' : e.symm '' t subseteq e.source := by
    rw [e.symm_image_eq_source_inter_preimage hs]
    apply Set.inter_subset_left
  rw [← e.image_symm_image_of_subset_target hs]
  exact e.isOpen_image_of_subset_source h h

中文:
引理 isOpen_symm_image_iff_of_subset_target
  条件: {t : Set Y} (hs : t subseteq e.target)
  证明: by
  refine ⟨fun h => ?_, fun h => e.symm.isOpen_image_of_subset_source h hs⟩
  have hs' : e.symm '' t subseteq e.source := by
    rw [e.symm_image_eq_source_inter_preimage hs]
    apply Set.inter_subset_left
  rw [← e.image_symm_image_of_subset_target hs]
  exact e.isOpen_image_of_subset_source h h

Depends on / 依赖: Set.inter_subset_left, e.image_symm_image_of_subset_target, e.isOpen_image_of_subset_source, e.source, e.symm, e.symm.isOpen_image_of_subset_source, e.symm_image_eq_source_inter_preimage, image_symm_image_of_subset_target, inter_subset_left, isOpen_image_of_subset_source, source, subseteq, symm_image_eq_source_inter_preimage
-/
lemma isOpen_symm_image_iff_of_subset_target {t : Set Y} (hs : t subseteq e.target) :
    IsOpen (e.symm '' t) ↔ IsOpen t := by
  refine ⟨fun h => ?_, fun h => e.symm.isOpen_image_of_subset_source h hs⟩
  have hs' : e.symm '' t subseteq e.source := by
    rw [e.symm_image_eq_source_inter_preimage hs]
    apply Set.inter_subset_left
  rw [← e.image_symm_image_of_subset_target hs]
  exact e.isOpen_image_of_subset_source h hs'

/--
theorem `isOpen_image_iff_of_subset_source` / 定理 `isOpen_image_iff_of_subset_source`

English:
theorem isOpen_image_iff_of_subset_source
  given: {s : Set X} (hs : s subseteq e.source)
  proof: by
  rw [← e.symm.isOpen_symm_image_iff_of_subset_target hs]; rw [e.symm_symm]

中文:
定理 isOpen_image_iff_of_subset_source
  条件: {s : Set X} (hs : s subseteq e.source)
  证明: by
  rw [← e.symm.isOpen_symm_image_iff_of_subset_target hs]; rw [e.symm_symm]

Depends on / 依赖: e.symm.isOpen_symm_image_iff_of_subset_target, e.symm_symm, isOpen_symm_image_iff_of_subset_target, symm_symm
-/
theorem isOpen_image_iff_of_subset_source {s : Set X} (hs : s subseteq e.source) :
    IsOpen (e '' s) ↔ IsOpen s := by
  rw [← e.symm.isOpen_symm_image_iff_of_subset_target hs]; rw [e.symm_symm]

/-- A `PartialEquiv` which is continuous on its source and has open forward map (on its source)
and open source is an `OpenPartialHomeomorph`. -/
@[simps! toPartialHomeomorph]
/--
Definition of `ofContinuousOpenRestrict` / `ofContinuousOpenRestrict` 的定义

English:
definition ofContinuousOpenRestrict
  signature: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
  body: PartialHomeomorph.ofContinuousOpenRestrict e hc ho
  open_source := hs
  open_target := by simpa [e.image_source_eq_target] using ho.isOpen_range

@[simp]

中文:
定义 ofContinuousOpenRestrict
  签名: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
  定义体: PartialHomeomorph.ofContinuousOpenRestrict e hc ho
  open_source := hs
  open_target := by simpa [e.image_source_eq_target] using ho.isOpen_range

@[simp]

Depends on / 依赖: PartialHomeomorph, PartialHomeomorph.ofContinuousOpenRestrict, ofContinuousOpenRestrict
-/
def ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) (hs : IsOpen e.source) :
    OpenPartialHomeomorph X Y where
  toPartialHomeomorph := PartialHomeomorph.ofContinuousOpenRestrict e hc ho
  open_source := hs
  open_target := by simpa [e.image_source_eq_target] using ho.isOpen_range

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
  结论: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
  证明: rfl

@[simp]
-/
theorem coe_ofContinuousOpenRestrict (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpenRestrict e hc ho hs) = e :=
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
  结论: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
  证明: rfl
-/
theorem coe_ofContinuousOpenRestrict_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap (e.source.domRestrict e)) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpenRestrict e hc ho hs).symm = e.symm :=
  rfl

/-- A `PartialEquiv` which is continuous on its source and has open forward map (on its source) and
open source is an `OpenPartialHomeomorph`. -/
@[simps! toPartialHomeomorph]
/--
Definition of `ofContinuousOpen` / `ofContinuousOpen` 的定义

English:
definition ofContinuousOpen
  signature: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
  body: ofContinuousOpenRestrict e hc (ho.domRestrict hs) hs

@[simp]

中文:
定义 ofContinuousOpen
  签名: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
  定义体: ofContinuousOpenRestrict e hc (ho.domRestrict hs) hs

@[simp]

Depends on / 依赖: domRestrict, ho.domRestrict, ofContinuousOpenRestrict
-/
def ofContinuousOpen (e : PartialEquiv X Y) (hc : ContinuousOn e e.source) (ho : IsOpenMap e)
    (hs : IsOpen e.source) : OpenPartialHomeomorph X Y :=
  ofContinuousOpenRestrict e hc (ho.domRestrict hs) hs

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
  结论: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
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
  结论: (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
  证明: rfl
-/
theorem coe_ofContinuousOpen_symm (e : PartialEquiv X Y) (hc : ContinuousOn e e.source)
    (ho : IsOpenMap e) (hs : IsOpen e.source) :
    ⇑(ofContinuousOpen e hc ho hs).symm = e.symm :=
  rfl

/-- The homeomorphism obtained by restricting an `OpenPartialHomeomorph` to a subset of the source.
-/
@[simps!]
/--
Definition of `homeomorphOfImageSubsetSource` / `homeomorphOfImageSubsetSource` 的定义

English:
definition homeomorphOfImageSubsetSource
  signature: {s : Set X} {t : Set Y} (hs : s subseteq e.source) (ht : e '' s = t)
  body: e.toPartialHomeomorph.homeomorphOfImageSubsetSource hs ht

中文:
定义 homeomorphOfImageSubsetSource
  签名: {s : Set X} {t : Set Y} (hs : s subseteq e.source) (ht : e '' s = t)
  定义体: e.toPartialHomeomorph.homeomorphOfImageSubsetSource hs ht

Depends on / 依赖: e.toPartialHomeomorph.homeomorphOfImageSubsetSource, homeomorphOfImageSubsetSource, toPartialHomeomorph
-/
def homeomorphOfImageSubsetSource {s : Set X} {t : Set Y} (hs : s subseteq e.source) (ht : e '' s = t) :
    s ≃ₜ t :=
  e.toPartialHomeomorph.homeomorphOfImageSubsetSource hs ht

/-- An open partial homeomorphism defines a homeomorphism between its source and target. -/
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
  条件: [SecondCountableTopology Y]
  证明: e.toHomeomorphSourceTarget.secondCountableTopology

Depends on / 依赖: e.toHomeomorphSourceTarget.secondCountableTopology, secondCountableTopology, toHomeomorphSourceTarget
-/
theorem secondCountableTopology_source [SecondCountableTopology Y] :
    SecondCountableTopology e.source :=
  e.toHomeomorphSourceTarget.secondCountableTopology

/--
theorem `nhds_eq_comap_inf_principal` / 定理 `nhds_eq_comap_inf_principal`

English:
theorem nhds_eq_comap_inf_principal
  given: {x} (hx : x in e.source)
  proof: by
  lift x to e.source using hx
  rw [← e.open_source.nhdsWithin_eq x.2]; rw [← map_nhds_subtype_val]; rw [← map_comap_setCoe_val]; rw [e.toHomeomorphSourceTarget.nhds_eq_comap]; rw [nhds_subtype_eq_comap]
  simp only [Function.comp_def, toHomeomorphSourceTarget_apply_coe, comap_comap]

中文:
定理 nhds_eq_comap_inf_principal
  条件: {x} (hx : x in e.source)
  证明: by
  lift x to e.source using hx
  rw [← e.open_source.nhdsWithin_eq x.2]; rw [← map_nhds_subtype_val]; rw [← map_comap_setCoe_val]; rw [e.toHomeomorphSourceTarget.nhds_eq_comap]; rw [nhds_subtype_eq_comap]
  simp only [Function.comp_def, toHomeomorphSourceTarget_apply_coe, comap_comap]

Depends on / 依赖: Function, Function.comp_def, comap_comap, comp_def, e.open_source.nhdsWithin_eq, e.source, e.toHomeomorphSourceTarget.nhds_eq_comap, map_comap_setCoe_val, map_nhds_subtype_val, nhdsWithin_eq, nhds_eq_comap, nhds_subtype_eq_comap, open_source, source, toHomeomorphSourceTarget, toHomeomorphSourceTarget_apply_coe
-/
theorem nhds_eq_comap_inf_principal {x} (hx : x in e.source) :
    𝓝 x = comap e (𝓝 (e x)) ⊓ 𝓟 e.source := by
  lift x to e.source using hx
  rw [← e.open_source.nhdsWithin_eq x.2]; rw [← map_nhds_subtype_val]; rw [← map_comap_setCoe_val]; rw [e.toHomeomorphSourceTarget.nhds_eq_comap]; rw [nhds_subtype_eq_comap]
  simp only [Function.comp_def, toHomeomorphSourceTarget_apply_coe, comap_comap]

/-- If an open partial homeomorphism has source and target equal to univ, then it induces a
homeomorphism between the whole spaces, expressed in this definition. -/
@[simps! (attr := mfld_simps) -fullyApplied apply symm_apply]
-- TODO: add a `PartialEquiv` version
/--
Definition of `toHomeomorphOfSourceEqUnivTargetEqUniv` / `toHomeomorphOfSourceEqUnivTargetEqUniv` 的定义

English:
definition toHomeomorphOfSourceEqUnivTargetEqUniv
  signature: (h : e.source = (univ : Set X)) (h' : e.target = univ)
  body: e.toPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv h h'

中文:
定义 toHomeomorphOfSourceEqUnivTargetEqUniv
  签名: (h : e.source = (univ : Set X)) (h' : e.target = univ)
  定义体: e.toPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv h h'

Depends on / 依赖: e.toPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv, toHomeomorphOfSourceEqUnivTargetEqUniv, toPartialHomeomorph
-/
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.source = (univ : Set X)) (h' : e.target = univ) :
    X ≃ₜ Y :=
  e.toPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv h h'

/--
theorem `isOpenEmbedding_restrict` / 定理 `isOpenEmbedding_restrict`

English:
theorem isOpenEmbedding_restrict
  statement: IsOpenEmbedding (e.source.domRestrict e) where
  proof: e.isEmbedding_restrict
  isOpen_range := by
    rw [range_domRestrict]; rw [image_source_eq_target]
    exact e.open_target

中文:
定理 isOpenEmbedding_restrict
  结论: IsOpenEmbedding (e.source.domRestrict e) where
  证明: e.isEmbedding_restrict
  isOpen_range := by
    rw [range_domRestrict]; rw [image_source_eq_target]
    exact e.open_target

Depends on / 依赖: e.isEmbedding_restrict, isEmbedding_restrict
-/
theorem isOpenEmbedding_restrict : IsOpenEmbedding (e.source.domRestrict e) where
  toIsEmbedding := e.isEmbedding_restrict
  isOpen_range := by
    rw [range_domRestrict]; rw [image_source_eq_target]
    exact e.open_target

/--
theorem `isOpenEmbedding` / 定理 `isOpenEmbedding`

English:
theorem isOpenEmbedding
  given: (h : e.source = Set.univ)
  statement: IsOpenEmbedding e
  proof: e.isOpenEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isOpenEmbedding

@[deprecated (since := "2026-07-17")] alias to_isOpenEmbedding := isOpenEmbedding

中文:
定理 isOpenEmbedding
  条件: (h : e.source = Set.univ)
  结论: IsOpenEmbedding e
  证明: e.isOpenEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isOpenEmbedding

@[deprecated (since := "2026-07-17")] alias to_isOpenEmbedding := isOpenEmbedding

Depends on / 依赖: Homeomorph, Homeomorph.Set.univ, Homeomorph.setCongr, e.isOpenEmbedding_restrict.comp, isOpenEmbedding, isOpenEmbedding_restrict, setCongr, symm.isOpenEmbedding
-/
theorem isOpenEmbedding (h : e.source = Set.univ) : IsOpenEmbedding e :=
  e.isOpenEmbedding_restrict.comp
    ((Homeomorph.setCongr h).trans <| Homeomorph.Set.univ X).symm.isOpenEmbedding

@[deprecated (since := "2026-07-17")] alias to_isOpenEmbedding := isOpenEmbedding

end OpenPartialHomeomorph

/-!
## Open embeddings
-/
namespace Topology.IsOpenEmbedding

variable (f : X -> Y) (h : IsOpenEmbedding f)

/-- An open embedding of `X` into `Y`, with `X` nonempty, defines an open partial homeomorphism
whose source is all of `X`. The converse is also true; see
`OpenPartialHomeomorph.isOpenEmbedding`. -/
@[simps! (attr := mfld_simps) -fullyApplied apply source target]
/--
Definition of `toOpenPartialHomeomorph` / `toOpenPartialHomeomorph` 的定义

English:
definition toOpenPartialHomeomorph
  signature: [Nonempty X]
  body: OpenPartialHomeomorph.ofContinuousOpen (h.isEmbedding.injective.injOn.toPartialEquiv f univ)
    h.continuous.continuousOn h.isOpenMap isOpen_univ

中文:
定义 toOpenPartialHomeomorph
  签名: [Nonempty X]
  定义体: OpenPartialHomeomorph.ofContinuousOpen (h.isEmbedding.injective.injOn.toPartialEquiv f univ)
    h.continuous.continuousOn h.isOpenMap isOpen_univ

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.ofContinuousOpen, continuous, continuousOn, h.continuous.continuousOn, h.isEmbedding.injective.injOn.toPartialEquiv, h.isOpenMap, injective, isEmbedding, isOpenMap, isOpen_univ, ofContinuousOpen, toPartialEquiv
-/
noncomputable def toOpenPartialHomeomorph [Nonempty X] : OpenPartialHomeomorph X Y :=
  OpenPartialHomeomorph.ofContinuousOpen (h.isEmbedding.injective.injOn.toPartialEquiv f univ)
    h.continuous.continuousOn h.isOpenMap isOpen_univ

variable [Nonempty X]

/--
lemma `toOpenPartialHomeomorph_left_inv` / 引理 `toOpenPartialHomeomorph_left_inv`

English:
lemma toOpenPartialHomeomorph_left_inv
  given: {x : X}
  statement: (h.toOpenPartialHomeomorph f).symm (f x) = x
  proof: by
  rw [← congr_fun (h.toOpenPartialHomeomorph_apply f)]; rw [OpenPartialHomeomorph.left_inv]
  exact Set.mem_univ _

中文:
引理 toOpenPartialHomeomorph_left_inv
  条件: {x : X}
  结论: (h.toOpenPartialHomeomorph f).symm (f x) = x
  证明: by
  rw [← congr_fun (h.toOpenPartialHomeomorph_apply f)]; rw [OpenPartialHomeomorph.left_inv]
  exact Set.mem_univ _

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.left_inv, Set.mem_univ, congr_fun, h.toOpenPartialHomeomorph_apply, left_inv, mem_univ, toOpenPartialHomeomorph_apply
-/
lemma toOpenPartialHomeomorph_left_inv {x : X} : (h.toOpenPartialHomeomorph f).symm (f x) = x := by
  rw [← congr_fun (h.toOpenPartialHomeomorph_apply f)]; rw [OpenPartialHomeomorph.left_inv]
  exact Set.mem_univ _

/--
lemma `toOpenPartialHomeomorph_right_inv` / 引理 `toOpenPartialHomeomorph_right_inv`

English:
lemma toOpenPartialHomeomorph_right_inv
  given: {x : Y} (hx : x in Set.range f)
  proof: by
  rw [← congr_fun (h.toOpenPartialHomeomorph_apply f)]; rw [OpenPartialHomeomorph.right_inv]
  rwa [toOpenPartialHomeomorph_target]

中文:
引理 toOpenPartialHomeomorph_right_inv
  条件: {x : Y} (hx : x in Set.range f)
  证明: by
  rw [← congr_fun (h.toOpenPartialHomeomorph_apply f)]; rw [OpenPartialHomeomorph.right_inv]
  rwa [toOpenPartialHomeomorph_target]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.right_inv, congr_fun, h.toOpenPartialHomeomorph_apply, right_inv, toOpenPartialHomeomorph_apply, toOpenPartialHomeomorph_target
-/
lemma toOpenPartialHomeomorph_right_inv {x : Y} (hx : x in Set.range f) :
    f ((h.toOpenPartialHomeomorph f).symm x) = x := by
  rw [← congr_fun (h.toOpenPartialHomeomorph_apply f)]; rw [OpenPartialHomeomorph.right_inv]
  rwa [toOpenPartialHomeomorph_target]

end Topology.IsOpenEmbedding

/-! inclusion of an open set in a topological space -/
namespace TopologicalSpace.Opens

/- `Nonempty s` is not a type class argument because `s`, being a subset, rarely comes with a type
class instance. Then we'd have to manually provide the instance every time we use the following
lemmas, tediously using `haveI := ...` or `@foobar _ _ _ ...`. -/
variable (s : Opens X) (hs : Nonempty s)

/--
Definition of `openPartialHomeomorphSubtypeCoe` / `openPartialHomeomorphSubtypeCoe` 的定义

English:
definition openPartialHomeomorphSubtypeCoe
  signature: : OpenPartialHomeomorph s X
  body: IsOpenEmbedding.toOpenPartialHomeomorph _ s.2.isOpenEmbedding_subtypeVal

@[simp, mfld_simps]

中文:
定义 openPartialHomeomorphSubtypeCoe
  签名: : OpenPartialHomeomorph s X
  定义体: IsOpenEmbedding.toOpenPartialHomeomorph _ s.2.isOpenEmbedding_subtypeVal

@[simp, mfld_simps]

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.toOpenPartialHomeomorph, isOpenEmbedding_subtypeVal, toOpenPartialHomeomorph
-/
noncomputable def openPartialHomeomorphSubtypeCoe : OpenPartialHomeomorph s X :=
  IsOpenEmbedding.toOpenPartialHomeomorph _ s.2.isOpenEmbedding_subtypeVal

@[simp, mfld_simps]
/--
theorem `openPartialHomeomorphSubtypeCoe_coe` / 定理 `openPartialHomeomorphSubtypeCoe_coe`

English:
theorem openPartialHomeomorphSubtypeCoe_coe
  proof: rfl

@[simp, mfld_simps]

中文:
定理 openPartialHomeomorphSubtypeCoe_coe
  证明: rfl

@[simp, mfld_simps]
-/
theorem openPartialHomeomorphSubtypeCoe_coe :
    (s.openPartialHomeomorphSubtypeCoe hs : s -> X) = (↑) :=
  rfl

@[simp, mfld_simps]
/--
theorem `openPartialHomeomorphSubtypeCoe_source` / 定理 `openPartialHomeomorphSubtypeCoe_source`

English:
theorem openPartialHomeomorphSubtypeCoe_source
  proof: rfl

@[simp, mfld_simps]

中文:
定理 openPartialHomeomorphSubtypeCoe_source
  证明: rfl

@[simp, mfld_simps]
-/
theorem openPartialHomeomorphSubtypeCoe_source :
    (s.openPartialHomeomorphSubtypeCoe hs).source = Set.univ :=
  rfl

@[simp, mfld_simps]
/--
theorem `openPartialHomeomorphSubtypeCoe_target` / 定理 `openPartialHomeomorphSubtypeCoe_target`

English:
theorem openPartialHomeomorphSubtypeCoe_target
  proof: by
  simp [openPartialHomeomorphSubtypeCoe]

中文:
定理 openPartialHomeomorphSubtypeCoe_target
  证明: by
  simp [openPartialHomeomorphSubtypeCoe]

Depends on / 依赖: openPartialHomeomorphSubtypeCoe
-/
theorem openPartialHomeomorphSubtypeCoe_target :
    (s.openPartialHomeomorphSubtypeCoe hs).target = s := by
  simp [openPartialHomeomorphSubtypeCoe]

end TopologicalSpace.Opens
