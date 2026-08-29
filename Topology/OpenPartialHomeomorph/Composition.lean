/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.IsImage
/-!
# Partial homeomorphisms: composition

## Main definitions

* `OpenPartialHomeomorph.trans`: the composition of two open partial homeomorphisms
-/

@[expose] public section

open Function Set Filter Topology

variable {X X' : Type*} {Y Y' : Type*} {Z Z' : Type*}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Y']
  [TopologicalSpace Z] [TopologicalSpace Z']

namespace OpenPartialHomeomorph

variable (e : OpenPartialHomeomorph X Y)

/-!
## Composition

`trans`: composition of two open partial homeomorphisms
-/
section trans

variable (e' : OpenPartialHomeomorph Y Z)

/-- Composition of two open partial homeomorphisms when the target of the first and the source of
the second coincide. -/
@[simps! apply symm_apply toPartialHomeomorph, simps! -isSimp source target]
/--
Definition of `trans'` / `trans'` 的定义

English:
definition trans'
  signature: (h : e.target = e'.source)
  body: PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv h
  open_source := e.open_source
  open_target := e'.open_target
continuousOn_toFun := e'.continuousOn.comp e.continuousOn h ▸ e.mapsTo
continuousOn_invFun := e.continuousOn_symm.comp e'.continuousOn_symm h.symm ▸ e'.mapsTo_symm

中文:
定义 trans'
  签名: (h : e.target = e'.source)
  定义体: PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv h
  open_source := e.open_source
  open_target := e'.open_target
continuousOn_toFun := e'.continuousOn.comp e.continuousOn h ▸ e.mapsTo
continuousOn_invFun := e.continuousOn_symm.comp e'.continuousOn_symm h.symm ▸ e'.mapsTo_symm
-/
protected def trans' (h : e.target = e'.source) : OpenPartialHomeomorph X Z where
  toPartialEquiv := PartialEquiv.trans' e.toPartialEquiv e'.toPartialEquiv h
  open_source := e.open_source
  open_target := e'.open_target
continuousOn_toFun := e'.continuousOn.comp e.continuousOn h ▸ e.mapsTo
continuousOn_invFun := e.continuousOn_symm.comp e'.continuousOn_symm h.symm ▸ e'.mapsTo_symm

/-- Composing two open partial homeomorphisms, by restricting to the maximal domain where their
composition is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ₕ f` for this. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: : OpenPartialHomeomorph X Z
  body: OpenPartialHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])

@[simp, mfld_simps]

中文:
定义 trans
  签名: : OpenPartialHomeomorph X Z
  定义体: OpenPartialHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])

@[simp, mfld_simps]
-/
protected def trans : OpenPartialHomeomorph X Z :=
  OpenPartialHomeomorph.trans' (e.symm.restrOpen e'.source e'.open_source).symm
    (e'.restrOpen e.target e.open_target) (by simp [inter_comm])

@[simp, mfld_simps]
/--
theorem `trans_toPartialEquiv` / 定理 `trans_toPartialEquiv`

English:
theorem trans_toPartialEquiv
  proof: rfl

@[simp, mfld_simps]

中文:
定理 trans_toPartialEquiv
  证明: rfl

@[simp, mfld_simps]
-/
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  rfl

@[simp, mfld_simps]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  statement: (e.trans e' : X -> Z) = e' ∘ e
  proof: rfl

@[simp, mfld_simps]

中文:
定理 coe_trans
  结论: (e.trans e' : X -> Z) = e' ∘ e
  证明: rfl

@[simp, mfld_simps]
-/
theorem coe_trans : (e.trans e' : X -> Z) = e' ∘ e :=
  rfl

@[simp, mfld_simps]
/--
theorem `coe_trans_symm` / 定理 `coe_trans_symm`

English:
theorem coe_trans_symm
  statement: ((e.trans e').symm : Z -> X) = e.symm ∘ e'.symm
  proof: rfl

中文:
定理 coe_trans_symm
  结论: ((e.trans e').symm : Z -> X) = e.symm ∘ e'.symm
  证明: rfl
-/
theorem coe_trans_symm : ((e.trans e').symm : Z -> X) = e.symm ∘ e'.symm :=
  rfl

/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: {x : X}
  statement: (e.trans e') x = e' (e x)
  proof: rfl

中文:
定理 trans_apply
  条件: {x : X}
  结论: (e.trans e') x = e' (e x)
  证明: rfl
-/
theorem trans_apply {x : X} : (e.trans e') x = e' (e x) :=
  rfl

/--
theorem `trans_symm_eq_symm_trans_symm` / 定理 `trans_symm_eq_symm_trans_symm`

English:
theorem trans_symm_eq_symm_trans_symm
  statement: (e.trans e').symm = e'.symm.trans e.symm
  proof: rfl

中文:
定理 trans_symm_eq_symm_trans_symm
  结论: (e.trans e').symm = e'.symm.trans e.symm
  证明: rfl
-/
theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl

/--
theorem `trans_source` / 定理 `trans_source`

English:
theorem trans_source
  statement: (e.trans e').source = e.source inter e ⁻¹' e'.source
  proof: PartialEquiv.trans_source e.toPartialEquiv e'.toPartialEquiv

中文:
定理 trans_source
  结论: (e.trans e').source = e.source inter e ⁻¹' e'.source
  证明: PartialEquiv.trans_source e.toPartialEquiv e'.toPartialEquiv

Depends on / 依赖: PartialEquiv, PartialEquiv.trans_source, e.toPartialEquiv, toPartialEquiv, trans_source
-/
theorem trans_source : (e.trans e').source = e.source inter e ⁻¹' e'.source :=
  PartialEquiv.trans_source e.toPartialEquiv e'.toPartialEquiv

/--
theorem `trans_source'` / 定理 `trans_source'`

English:
theorem trans_source'
  statement: (e.trans e').source = e.source inter e ⁻¹' (e.target inter e'.source)
  proof: PartialEquiv.trans_source' e.toPartialEquiv e'.toPartialEquiv

中文:
定理 trans_source'
  结论: (e.trans e').source = e.source inter e ⁻¹' (e.target inter e'.source)
  证明: PartialEquiv.trans_source' e.toPartialEquiv e'.toPartialEquiv

Depends on / 依赖: PartialEquiv, PartialEquiv.trans_source, e.toPartialEquiv, toPartialEquiv, trans_source
-/
theorem trans_source' : (e.trans e').source = e.source inter e ⁻¹' (e.target inter e'.source) :=
  PartialEquiv.trans_source' e.toPartialEquiv e'.toPartialEquiv

/--
theorem `trans_source''` / 定理 `trans_source''`

English:
theorem trans_source''
  statement: (e.trans e').source = e.symm '' (e.target inter e'.source)
  proof: PartialEquiv.trans_source'' e.toPartialEquiv e'.toPartialEquiv

中文:
定理 trans_source''
  结论: (e.trans e').source = e.symm '' (e.target inter e'.source)
  证明: PartialEquiv.trans_source'' e.toPartialEquiv e'.toPartialEquiv

Depends on / 依赖: PartialEquiv, PartialEquiv.trans_source, e.toPartialEquiv, toPartialEquiv, trans_source
-/
theorem trans_source'' : (e.trans e').source = e.symm '' (e.target inter e'.source) :=
  PartialEquiv.trans_source'' e.toPartialEquiv e'.toPartialEquiv

/--
theorem `image_trans_source` / 定理 `image_trans_source`

English:
theorem image_trans_source
  statement: e '' (e.trans e').source = e.target inter e'.source
  proof: PartialEquiv.image_trans_source e.toPartialEquiv e'.toPartialEquiv

中文:
定理 image_trans_source
  结论: e '' (e.trans e').source = e.target inter e'.source
  证明: PartialEquiv.image_trans_source e.toPartialEquiv e'.toPartialEquiv

Depends on / 依赖: PartialEquiv, PartialEquiv.image_trans_source, e.toPartialEquiv, image_trans_source, toPartialEquiv
-/
theorem image_trans_source : e '' (e.trans e').source = e.target inter e'.source :=
  PartialEquiv.image_trans_source e.toPartialEquiv e'.toPartialEquiv

/--
theorem `trans_target` / 定理 `trans_target`

English:
theorem trans_target
  statement: (e.trans e').target = e'.target inter e'.symm ⁻¹' e.target
  proof: rfl

中文:
定理 trans_target
  结论: (e.trans e').target = e'.target inter e'.symm ⁻¹' e.target
  证明: rfl
-/
theorem trans_target : (e.trans e').target = e'.target inter e'.symm ⁻¹' e.target :=
  rfl

/--
theorem `trans_target'` / 定理 `trans_target'`

English:
theorem trans_target'
  statement: (e.trans e').target = e'.target inter e'.symm ⁻¹' (e'.source inter e.target)
  proof: trans_source' e'.symm e.symm

中文:
定理 trans_target'
  结论: (e.trans e').target = e'.target inter e'.symm ⁻¹' (e'.source inter e.target)
  证明: trans_source' e'.symm e.symm

Depends on / 依赖: e.symm, trans_source
-/
theorem trans_target' : (e.trans e').target = e'.target inter e'.symm ⁻¹' (e'.source inter e.target) :=
  trans_source' e'.symm e.symm

/--
theorem `trans_target''` / 定理 `trans_target''`

English:
theorem trans_target''
  statement: (e.trans e').target = e' '' (e'.source inter e.target)
  proof: trans_source'' e'.symm e.symm

中文:
定理 trans_target''
  结论: (e.trans e').target = e' '' (e'.source inter e.target)
  证明: trans_source'' e'.symm e.symm

Depends on / 依赖: e.symm, trans_source
-/
theorem trans_target'' : (e.trans e').target = e' '' (e'.source inter e.target) :=
  trans_source'' e'.symm e.symm

/--
theorem `inv_image_trans_target` / 定理 `inv_image_trans_target`

English:
theorem inv_image_trans_target
  statement: e'.symm '' (e.trans e').target = e'.source inter e.target
  proof: image_trans_source e'.symm e.symm

中文:
定理 inv_image_trans_target
  结论: e'.symm '' (e.trans e').target = e'.source inter e.target
  证明: image_trans_source e'.symm e.symm

Depends on / 依赖: e.symm, image_trans_source
-/
theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source inter e.target :=
  image_trans_source e'.symm e.symm

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: (e'' : OpenPartialHomeomorph Z Z')
  proof: toPartialEquiv_injective e.1.trans_assoc _ _

@[simp, mfld_simps]

中文:
定理 trans_assoc
  条件: (e'' : OpenPartialHomeomorph Z Z')
  证明: toPartialEquiv_injective e.1.trans_assoc _ _

@[simp, mfld_simps]

Depends on / 依赖: toPartialEquiv_injective, trans_assoc
-/
theorem trans_assoc (e'' : OpenPartialHomeomorph Z Z') :
    (e.trans e').trans e'' = e.trans (e'.trans e'') :=
toPartialEquiv_injective e.1.trans_assoc _ _

@[simp, mfld_simps]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  statement: e.trans (OpenPartialHomeomorph.refl Y) = e
  proof: toPartialHomeomorph_injective (PartialHomeomorph.toPartialEquiv_injective e.1.trans_refl)

@[simp, mfld_simps]

中文:
定理 trans_refl
  结论: e.trans (OpenPartialHomeomorph.refl Y) = e
  证明: toPartialHomeomorph_injective (PartialHomeomorph.toPartialEquiv_injective e.1.trans_refl)

@[simp, mfld_simps]

Depends on / 依赖: PartialHomeomorph, PartialHomeomorph.toPartialEquiv_injective, toPartialEquiv_injective, toPartialHomeomorph_injective, trans_refl
-/
theorem trans_refl : e.trans (OpenPartialHomeomorph.refl Y) = e :=
  toPartialHomeomorph_injective (PartialHomeomorph.toPartialEquiv_injective e.1.trans_refl)

@[simp, mfld_simps]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  statement: (OpenPartialHomeomorph.refl X).trans e = e
  proof: toPartialHomeomorph_injective (PartialHomeomorph.toPartialEquiv_injective e.1.refl_trans)

中文:
定理 refl_trans
  结论: (OpenPartialHomeomorph.refl X).trans e = e
  证明: toPartialHomeomorph_injective (PartialHomeomorph.toPartialEquiv_injective e.1.refl_trans)

Depends on / 依赖: PartialHomeomorph, PartialHomeomorph.toPartialEquiv_injective, refl_trans, toPartialEquiv_injective, toPartialHomeomorph_injective
-/
theorem refl_trans : (OpenPartialHomeomorph.refl X).trans e = e :=
  toPartialHomeomorph_injective (PartialHomeomorph.toPartialEquiv_injective e.1.refl_trans)

/--
theorem `trans_ofSet` / 定理 `trans_ofSet`

English:
theorem trans_ofSet
  given: {s : Set Y} (hs : IsOpen s)
  statement: e.trans (ofSet s hs) = e.restr (e ⁻¹' s)
  proof: OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) by
    rw [trans_source]; rw [restr_source]; rw [ofSet_source]; rw [← preimage_interior]; rw [hs.interior_eq]

中文:
定理 trans_ofSet
  条件: {s : 集合 Y} (hs : 是开集 s)
  结论: e.trans (ofSet s hs) = e.restr (e ⁻¹' s)
  证明: OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) by
    rw [trans_source]; rw [restr_source]; rw [ofSet_source]; rw [← preimage_interior]; rw [hs.interior_eq]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.ext, hs.interior_eq, interior_eq, ofSet_source, preimage_interior, restr_source, trans_source
-/
theorem trans_ofSet {s : Set Y} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl) by
    rw [trans_source]; rw [restr_source]; rw [ofSet_source]; rw [← preimage_interior]; rw [hs.interior_eq]

/--
theorem `trans_of_set'` / 定理 `trans_of_set'`

English:
theorem trans_of_set'
  given: {s : Set Y} (hs : IsOpen s)
  proof: by rw [trans_ofSet, restr_source_inter]

中文:
定理 trans_of_set'
  条件: {s : 集合 Y} (hs : 是开集 s)
  证明: by rw [trans_ofSet, restr_source_inter]

Depends on / 依赖: restr_source_inter, trans_ofSet
-/
theorem trans_of_set' {s : Set Y} (hs : IsOpen s) :
    e.trans (ofSet s hs) = e.restr (e.source inter e ⁻¹' s) := by rw [trans_ofSet, restr_source_inter]

/--
theorem `ofSet_trans` / 定理 `ofSet_trans`

English:
theorem ofSet_trans
  given: {s : Set X} (hs : IsOpen s)
  statement: (ofSet s hs).trans e = e.restr s
  proof: OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl)
    by simp [hs.interior_eq, inter_comm]

中文:
定理 ofSet_trans
  条件: {s : 集合 X} (hs : 是开集 s)
  结论: (ofSet s hs).trans e = e.restr s
  证明: OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl)
    by simp [hs.interior_eq, inter_comm]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.ext, hs.interior_eq, inter_comm, interior_eq
-/
theorem ofSet_trans {s : Set X} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
OpenPartialHomeomorph.ext _ _ (fun _ => rfl) (fun _ => rfl)
    by simp [hs.interior_eq, inter_comm]

/--
theorem `ofSet_trans'` / 定理 `ofSet_trans'`

English:
theorem ofSet_trans'
  given: {s : Set X} (hs : IsOpen s)
  proof: by
  rw [ofSet_trans]; rw [restr_source_inter]

@[simp, mfld_simps]

中文:
定理 ofSet_trans'
  条件: {s : 集合 X} (hs : 是开集 s)
  证明: by
  rw [ofSet_trans]; rw [restr_source_inter]

@[simp, mfld_simps]

Depends on / 依赖: ofSet_trans, restr_source_inter
-/
theorem ofSet_trans' {s : Set X} (hs : IsOpen s) :
    (ofSet s hs).trans e = e.restr (e.source inter s) := by
  rw [ofSet_trans]; rw [restr_source_inter]

@[simp, mfld_simps]
/--
theorem `ofSet_trans_ofSet` / 定理 `ofSet_trans_ofSet`

English:
theorem ofSet_trans_ofSet
  given: {s : Set X} (hs : IsOpen s) {s' : Set X} (hs' : IsOpen s')
  proof: by
  rw [(ofSet s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]

中文:
定理 ofSet_trans_ofSet
  条件: {s : 集合 X} (hs : 是开集 s) {s' : 集合 X} (hs' : 是开集 s')
  证明: by
  rw [(ofSet s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]

Depends on / 依赖: interior_eq, trans_ofSet
-/
theorem ofSet_trans_ofSet {s : Set X} (hs : IsOpen s) {s' : Set X} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s inter s') (IsOpen.inter hs hs') := by
  rw [(ofSet s hs).trans_ofSet hs']
  ext <;> simp [hs'.interior_eq]

/--
theorem `restr_trans` / 定理 `restr_trans`

English:
theorem restr_trans
  given: (s : Set X)
  statement: (e.restr s).trans e' = (e.trans e').restr s
  proof: toPartialEquiv_injective
    PartialEquiv.restr_trans e.toPartialEquiv e'.toPartialEquiv (interior s)

中文:
定理 restr_trans
  条件: (s : 集合 X)
  结论: (e.restr s).trans e' = (e.trans e').restr s
  证明: toPartialEquiv_injective
    PartialEquiv.restr_trans e.toPartialEquiv e'.toPartialEquiv (interior s)

Depends on / 依赖: PartialEquiv, PartialEquiv.restr_trans, e.toPartialEquiv, interior, restr_trans, toPartialEquiv, toPartialEquiv_injective
-/
theorem restr_trans (s : Set X) : (e.restr s).trans e' = (e.trans e').restr s :=
toPartialEquiv_injective
    PartialEquiv.restr_trans e.toPartialEquiv e'.toPartialEquiv (interior s)

end trans

/--
theorem `EqOnSource.trans'` / 定理 `EqOnSource.trans'`

English:
theorem EqOnSource.trans'
  statement: {e e' : OpenPartialHomeomorph X Y} {f f' : OpenPartialHomeomorph Y Z}
  proof: PartialEquiv.EqOnSource.trans' he hf

中文:
定理 EqOnSource.trans'
  结论: {e e' : OpenPartialHomeomorph X Y} {f f' : OpenPartialHomeomorph Y Z}
  证明: PartialEquiv.EqOnSource.trans' he hf
-/
theorem EqOnSource.trans' {e e' : OpenPartialHomeomorph X Y} {f f' : OpenPartialHomeomorph Y Z}
    (he : e ≈ e') (hf : f ≈ f') : e.trans f ≈ e'.trans f' :=
  PartialEquiv.EqOnSource.trans' he hf

/--
theorem `self_trans_symm` / 定理 `self_trans_symm`

English:
theorem self_trans_symm
  statement: e.trans e.symm ≈ OpenPartialHomeomorph.ofSet e.source e.open_source
  proof: PartialEquiv.self_trans_symm _

中文:
定理 self_trans_symm
  结论: e.trans e.symm ≈ OpenPartialHomeomorph.ofSet e.source e.open_source
  证明: PartialEquiv.self_trans_symm _

Depends on / 依赖: PartialEquiv, PartialEquiv.self_trans_symm, self_trans_symm
-/
theorem self_trans_symm : e.trans e.symm ≈ OpenPartialHomeomorph.ofSet e.source e.open_source :=
  PartialEquiv.self_trans_symm _

/--
theorem `symm_trans_self` / 定理 `symm_trans_self`

English:
theorem symm_trans_self
  statement: e.symm.trans e ≈ OpenPartialHomeomorph.ofSet e.target e.open_target
  proof: e.symm.self_trans_symm

中文:
定理 symm_trans_self
  结论: e.symm.trans e ≈ OpenPartialHomeomorph.ofSet e.target e.open_target
  证明: e.symm.self_trans_symm

Depends on / 依赖: e.symm.self_trans_symm, self_trans_symm
-/
theorem symm_trans_self : e.symm.trans e ≈ OpenPartialHomeomorph.ofSet e.target e.open_target :=
  e.symm.self_trans_symm

variable {s : Set X}

/--
theorem `restr_symm_trans` / 定理 `restr_symm_trans`

English:
theorem restr_symm_trans
  statement: {e' : OpenPartialHomeomorph X Y}
  proof: by
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, PartialEquiv.restr_target,
      coe_toPartialEquiv_symm, PartialEquiv.restr_coe_symm, PartialEquiv.restr_source]
    rw [interior_eq_iff_is

中文:
定理 restr_symm_trans
  结论: {e' : OpenPartialHomeomorph X Y}
  证明: by
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, PartialEquiv.restr_target,
      coe_toPartialEquiv_symm, PartialEquiv.restr_coe_symm, PartialEquiv.restr_source]
    rw [interior_eq_iff_is

Depends on / 依赖: PartialEquiv, PartialEquiv.restr_coe_symm, PartialEquiv.restr_source, PartialEquiv.restr_target, PartialEquiv.symm_source, PartialEquiv.trans_source, coe_toPartialEquiv_symm, interior_eq_iff_isOpen, interior_eq_iff_isOpen.mpr, restr_coe_symm, restr_source, restr_target, restr_toPartialEquiv, symm_source, symm_toPartialEquiv, trans_source, trans_toPartialEquiv
-/
theorem restr_symm_trans {e' : OpenPartialHomeomorph X Y}
    (hs : IsOpen s) (hs' : IsOpen (e '' s)) (hs'' : s subseteq e.source) :
    (e.restr s).symm.trans e' ≈ (e.symm.trans e').restr (e '' s) := by
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, PartialEquiv.restr_target,
      coe_toPartialEquiv_symm, PartialEquiv.restr_coe_symm, PartialEquiv.restr_source]
    rw [interior_eq_iff_isOpen.mpr hs']; rw [interior_eq_iff_isOpen.mpr hs]
    -- Get rid of the middle term, which is merely distracting.
    rw [inter_assoc]; rw [inter_assoc]; rw [inter_comm _ (e '' s)]; rw [← inter_assoc]; rw [← inter_assoc]
    congr 1
    -- Now, just a bunch of rewrites: should this be a separate lemma?
    rw [← image_source_inter_eq']; rw [← image_source_eq_target]
    refine image_inter_on ?_
    intro x hx y hy h
    rw [← left_inv e hy]; rw [← left_inv e (hs'' hx)]; rw [h]
  · simp_rw [coe_trans, restr_symm_apply, restr_apply, coe_trans]
    intro x hx
    simp

/--
theorem `symm_trans_restr` / 定理 `symm_trans_restr`

English:
theorem symm_trans_restr
  given: (e' : OpenPartialHomeomorph X Y) (hs : IsOpen s)
  proof: by
  have ht : IsOpen (e'.target inter e'.symm ⁻¹' s) := by
    rw [← image_source_inter_eq']
    exact isOpen_image_source_inter e' hs
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, coe_toP

中文:
定理 symm_trans_restr
  条件: (e' : OpenPartialHomeomorph X Y) (hs : 是开集 s)
  证明: by
  have ht : IsOpen (e'.target inter e'.symm ⁻¹' s) := by
    rw [← image_source_inter_eq']
    exact isOpen_image_source_inter e' hs
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, coe_toP

Depends on / 依赖: IsOpen, PartialEquiv, PartialEquiv.restr_source, PartialEquiv.symm_source, PartialEquiv.trans_source, coe_toPartialEquiv_symm, image_source_inter_eq, isOpen_image_source_inter, preimage_inter, restr_source, restr_toPartialEquiv, symm_source, symm_toPartialEquiv, target, trans_source, trans_toPartialEquiv
-/
theorem symm_trans_restr (e' : OpenPartialHomeomorph X Y) (hs : IsOpen s) :
    e'.symm.trans (e.restr s) ≈ (e'.symm.trans e).restr (e'.target inter e'.symm ⁻¹' s) := by
  have ht : IsOpen (e'.target inter e'.symm ⁻¹' s) := by
    rw [← image_source_inter_eq']
    exact isOpen_image_source_inter e' hs
  refine ⟨?_, ?_⟩
  · simp only [trans_toPartialEquiv, symm_toPartialEquiv, restr_toPartialEquiv,
      PartialEquiv.trans_source, PartialEquiv.symm_source, coe_toPartialEquiv_symm,
      PartialEquiv.restr_source, preimage_inter]
    -- Shuffle the intersections, pull e'.target into the interior and use interior_inter.
    rw [interior_eq_iff_isOpen.mpr hs]; rw [← inter_assoc]; rw [inter_comm e'.target]; rw [inter_assoc]; rw [inter_assoc]
    congr 1
    nth_rw 2 [← interior_eq_iff_isOpen.mpr e'.open_target]
    rw [← interior_inter]; rw [← inter_assoc]; rw [inter_self]; rw [interior_eq_iff_isOpen.mpr ht]
  · simp [Set.eqOn_refl]

end OpenPartialHomeomorph

namespace Homeomorph

variable (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)

@[simp, mfld_simps]
/--
theorem `trans_toOpenPartialHomeomorph` / 定理 `trans_toOpenPartialHomeomorph`

English:
theorem trans_toOpenPartialHomeomorph
  statement: (e.trans e').toOpenPartialHomeomorph =
  proof: OpenPartialHomeomorph.toPartialHomeomorph_injective
PartialHomeomorph.toPartialEquiv_injective Equiv.trans_toPartialEquiv _ _

中文:
定理 trans_toOpenPartialHomeomorph
  结论: (e.trans e').toOpenPartialHomeomorph =
  证明: OpenPartialHomeomorph.toPartialHomeomorph_injective
PartialHomeomorph.toPartialEquiv_injective Equiv.trans_toPartialEquiv _ _

Depends on / 依赖: Equiv.trans_toPartialEquiv, OpenPartialHomeomorph, OpenPartialHomeomorph.toPartialHomeomorph_injective, PartialHomeomorph, PartialHomeomorph.toPartialEquiv_injective, toPartialEquiv_injective, toPartialHomeomorph_injective, trans_toPartialEquiv
-/
theorem trans_toOpenPartialHomeomorph : (e.trans e').toOpenPartialHomeomorph =
    e.toOpenPartialHomeomorph.trans e'.toOpenPartialHomeomorph :=
OpenPartialHomeomorph.toPartialHomeomorph_injective
PartialHomeomorph.toPartialEquiv_injective Equiv.trans_toPartialEquiv _ _

/-- Precompose an open partial homeomorphism with a homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps! -fullyApplied]
/--
Definition of `transOpenPartialHomeomorph` / `transOpenPartialHomeomorph` 的定义

English:
definition transOpenPartialHomeomorph
  signature: (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z)
  body: e.toEquiv.transPartialEquiv f'.toPartialEquiv
  open_source := f'.open_source.preimage e.continuous
  open_target := f'.open_target
  continuousOn_toFun := f'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuousOn_invFun := e.symm.continuous.comp_continuousOn f'.symm.continuousOn

中文:
定义 transOpenPartialHomeomorph
  签名: (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z)
  定义体: e.toEquiv.transPartialEquiv f'.toPartialEquiv
  open_source := f'.open_source.preimage e.continuous
  open_target := f'.open_target
  continuousOn_toFun := f'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuousOn_invFun := e.symm.continuous.comp_continuousOn f'.symm.continuousOn

Depends on / 依赖: e.toEquiv.transPartialEquiv, toEquiv, toPartialEquiv, transPartialEquiv
-/
def transOpenPartialHomeomorph (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z) :
    OpenPartialHomeomorph X Z where
  toPartialEquiv := e.toEquiv.transPartialEquiv f'.toPartialEquiv
  open_source := f'.open_source.preimage e.continuous
  open_target := f'.open_target
  continuousOn_toFun := f'.continuousOn.comp e.continuous.continuousOn fun _ => id
  continuousOn_invFun := e.symm.continuous.comp_continuousOn f'.symm.continuousOn

/--
theorem `transOpenPartialHomeomorph_eq_trans` / 定理 `transOpenPartialHomeomorph_eq_trans`

English:
theorem transOpenPartialHomeomorph_eq_trans
  given: (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z)
  proof: OpenPartialHomeomorph.toPartialEquiv_injective Equiv.transPartialEquiv_eq_trans _ _

@[simp, mfld_simps]

中文:
定理 transOpenPartialHomeomorph_eq_trans
  条件: (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z)
  证明: OpenPartialHomeomorph.toPartialEquiv_injective Equiv.transPartialEquiv_eq_trans _ _

@[simp, mfld_simps]

Depends on / 依赖: Equiv.transPartialEquiv_eq_trans, OpenPartialHomeomorph, OpenPartialHomeomorph.toPartialEquiv_injective, toPartialEquiv_injective, transPartialEquiv_eq_trans
-/
theorem transOpenPartialHomeomorph_eq_trans (e : X ≃ₜ Y) (f' : OpenPartialHomeomorph Y Z) :
    e.transOpenPartialHomeomorph f' = e.toOpenPartialHomeomorph.trans f' :=
OpenPartialHomeomorph.toPartialEquiv_injective Equiv.transPartialEquiv_eq_trans _ _

@[simp, mfld_simps]
/--
theorem `transOpenPartialHomeomorph_trans` / 定理 `transOpenPartialHomeomorph_trans`

English:
theorem transOpenPartialHomeomorph_trans
  statement: (e : X ≃ₜ Y) (f : OpenPartialHomeomorph Y Z)
  proof: by
  simp only [transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc]

@[simp, mfld_simps]

中文:
定理 transOpenPartialHomeomorph_trans
  结论: (e : X ≃ₜ Y) (f : OpenPartialHomeomorph Y Z)
  证明: by
  simp only [transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc]

@[simp, mfld_simps]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.trans_assoc, transOpenPartialHomeomorph_eq_trans, trans_assoc
-/
theorem transOpenPartialHomeomorph_trans (e : X ≃ₜ Y) (f : OpenPartialHomeomorph Y Z)
    (f' : OpenPartialHomeomorph Z Z') :
    (e.transOpenPartialHomeomorph f).trans f' = e.transOpenPartialHomeomorph (f.trans f') := by
  simp only [transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc]

@[simp, mfld_simps]
/--
theorem `trans_transOpenPartialHomeomorph` / 定理 `trans_transOpenPartialHomeomorph`

English:
theorem trans_transOpenPartialHomeomorph
  statement: (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)
  proof: by
  simp only [transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc,
    trans_toOpenPartialHomeomorph]

中文:
定理 trans_transOpenPartialHomeomorph
  结论: (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)
  证明: by
  simp only [transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc,
    trans_toOpenPartialHomeomorph]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.trans_assoc, transOpenPartialHomeomorph_eq_trans, trans_assoc, trans_toOpenPartialHomeomorph
-/
theorem trans_transOpenPartialHomeomorph (e : X ≃ₜ Y) (e' : Y ≃ₜ Z)
    (f'' : OpenPartialHomeomorph Z Z') : (e.trans e').transOpenPartialHomeomorph f'' =
      e.transOpenPartialHomeomorph (e'.transOpenPartialHomeomorph f'') := by
  simp only [transOpenPartialHomeomorph_eq_trans, OpenPartialHomeomorph.trans_assoc,
    trans_toOpenPartialHomeomorph]

end Homeomorph
