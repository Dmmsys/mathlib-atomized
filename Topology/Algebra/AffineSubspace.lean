/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Restrict
public import Mathlib.Topology.Algebra.ContinuousAffineMap
public import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Topology of affine subspaces.

This file defines the embedding map from an affine subspace to the ambient space as a continuous
affine map.

## Main definitions

* `AffineSubspace.subtypeA` is `AffineSubspace.subtype` as a `ContinuousAffineMap`.

-/

@[expose] public section


namespace AffineSubspace

variable {R V P : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace P]
  [AddTorsor V P]

/--
Definition of `subtypeA` / `subtypeA` 的定义

English:
definition subtypeA
  signature: (s : AffineSubspace R P) [Nonempty s]
  body: s.subtype
  cont := continuous_subtype_val

中文:
定义 subtypeA
  签名: (s : AffineSubspace R P) [Nonempty s]
  定义体: s.subtype
  cont := continuous_subtype_val

Depends on / 依赖: s.subtype, subtype
-/
def subtypeA (s : AffineSubspace R P) [Nonempty s] : s ->ᴬ[R] P where
  toAffineMap := s.subtype
  cont := continuous_subtype_val

/--
lemma `coe_subtypeA` / 引理 `coe_subtypeA`

English:
lemma coe_subtypeA
  given: (s : AffineSubspace R P) [Nonempty s]
  statement: ⇑s.subtypeA = Subtype.val
  proof: rfl

中文:
引理 coe_subtypeA
  条件: (s : AffineSubspace R P) [Nonempty s]
  结论: ⇑s.subtypeA = Subtype.val
  证明: rfl
-/
@[simp] lemma coe_subtypeA (s : AffineSubspace R P) [Nonempty s] : ⇑s.subtypeA = Subtype.val :=
  rfl

/--
lemma `subtypeA_toAffineMap` / 引理 `subtypeA_toAffineMap`

English:
lemma subtypeA_toAffineMap
  given: (s : AffineSubspace R P) [Nonempty s]
  proof: rfl

中文:
引理 subtypeA_toAffineMap
  条件: (s : AffineSubspace R P) [Nonempty s]
  证明: rfl
-/
@[simp] lemma subtypeA_toAffineMap (s : AffineSubspace R P) [Nonempty s] :
    s.subtypeA.toAffineMap = s.subtype :=
  rfl

/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: {s t : AffineSubspace R P} [Nonempty s] [Nonempty t]
  body: .ofEq s t h
  continuous_toFun := by subst h; exact continuous_id
  continuous_invFun := by subst h; exact continuous_id

@[simp]

中文:
定义 ofEq
  签名: {s t : AffineSubspace R P} [Nonempty s] [Nonempty t]
  定义体: .ofEq s t h
  continuous_toFun := by subst h; exact continuous_id
  continuous_invFun := by subst h; exact continuous_id

@[simp]
-/
noncomputable def ofEq {s t : AffineSubspace R P} [Nonempty s] [Nonempty t]
    (h : s = t) : s ≃ᴬ[R] t where
  toAffineEquiv := .ofEq s t h
  continuous_toFun := by subst h; exact continuous_id
  continuous_invFun := by subst h; exact continuous_id

@[simp]
/--
theorem `coe_ofEq_apply` / 定理 `coe_ofEq_apply`

English:
theorem coe_ofEq_apply
  statement: {s t : AffineSubspace R P} [Nonempty s] [Nonempty t]
  proof: AffineEquiv.coe_ofEq_apply s t h x

中文:
定理 coe_ofEq_apply
  结论: {s t : AffineSubspace R P} [Nonempty s] [Nonempty t]
  证明: AffineEquiv.coe_ofEq_apply s t h x

Depends on / 依赖: AffineEquiv, AffineEquiv.coe_ofEq_apply, coe_ofEq_apply
-/
theorem coe_ofEq_apply {s t : AffineSubspace R P} [Nonempty s] [Nonempty t]
    (h : s = t) (x : s) : (ofEq h x : P) = x := AffineEquiv.coe_ofEq_apply s t h x

end AffineSubspace

namespace ContinuousAffineEquiv

variable {R V P W Q : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace P]
  [AddTorsor V P] [AddCommGroup W] [Module R W] [TopologicalSpace Q] [AddTorsor W Q]

/--
Definition of `affineSubspaceMap` / `affineSubspaceMap` 的定义

English:
definition affineSubspaceMap
  signature: (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P) [Nonempty s]
  body: { e.toAffineEquiv.affineSubspaceMap s with
    continuous_toFun := by simpa [Topology.IsEmbedding.subtypeVal.continuous_iff] using!
      (e.continuous.comp continuous_subtype_val).congr fun _ => rfl
    continuous_invFun := by simpa [Topology.IsEmbedding.subtypeVal.continuous_iff] using!
      (e.c

中文:
定义 affineSubspaceMap
  签名: (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P) [Nonempty s]
  定义体: { e.toAffineEquiv.affineSubspaceMap s with
    continuous_toFun := by simpa [Topology.IsEmbedding.subtypeVal.continuous_iff] using!
      (e.continuous.comp continuous_subtype_val).congr fun _ => rfl
    continuous_invFun := by simpa [Topology.IsEmbedding.subtypeVal.continuous_iff] using!
      (e.c

Depends on / 依赖: AffineEquiv, AffineEquiv.affineSubspaceMap_apply_symm_apply, IsEmbedding, Topology, Topology.IsEmbedding.subtypeVal.continuous_iff, affineSubspaceMap, affineSubspaceMap_apply_symm_apply, continuous, continuous_iff, continuous_invFun, continuous_subtype_val, continuous_toFun, e.continuous.comp, e.continuous_invFun.comp, e.eq_symm_apply.mpr, e.toAffineEquiv, e.toAffineEquiv.affineSubspaceMap, eq_symm_apply, subtypeVal, toAffineEquiv
-/
noncomputable def affineSubspaceMap (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P) [Nonempty s] :
    s ≃ᴬ[R] s.map e.toAffineMap :=
  { e.toAffineEquiv.affineSubspaceMap s with
    continuous_toFun := by simpa [Topology.IsEmbedding.subtypeVal.continuous_iff] using!
      (e.continuous.comp continuous_subtype_val).congr fun _ => rfl
    continuous_invFun := by simpa [Topology.IsEmbedding.subtypeVal.continuous_iff] using!
      (e.continuous_invFun.comp continuous_subtype_val).congr fun x =>
        (e.eq_symm_apply.mpr
          (AffineEquiv.affineSubspaceMap_apply_symm_apply e.toAffineEquiv s x)).symm }

@[simp]
/--
theorem `affineSubspaceMap_apply` / 定理 `affineSubspaceMap_apply`

English:
theorem affineSubspaceMap_apply
  statement: (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P) [Nonempty s]
  proof: rfl

@[simp]

中文:
定理 affineSubspaceMap_apply
  结论: (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P) [Nonempty s]
  证明: rfl

@[simp]
-/
theorem affineSubspaceMap_apply (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P) [Nonempty s]
    (x : s) : e.affineSubspaceMap s x = e x := rfl

@[simp]
/--
theorem `affineSubspaceMap_apply_symm_apply` / 定理 `affineSubspaceMap_apply_symm_apply`

English:
theorem affineSubspaceMap_apply_symm_apply
  statement: (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P)
  proof: AffineEquiv.affineSubspaceMap_apply_symm_apply e.toAffineEquiv s x

中文:
定理 affineSubspaceMap_apply_symm_apply
  结论: (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P)
  证明: AffineEquiv.affineSubspaceMap_apply_symm_apply e.toAffineEquiv s x

Depends on / 依赖: AffineEquiv, AffineEquiv.affineSubspaceMap_apply_symm_apply, affineSubspaceMap_apply_symm_apply, e.toAffineEquiv, toAffineEquiv
-/
theorem affineSubspaceMap_apply_symm_apply (e : P ≃ᴬ[R] Q) (s : AffineSubspace R P)
    [Nonempty s] (x : s.map e.toAffineMap) : e ((e.affineSubspaceMap s).symm x) = x :=
  AffineEquiv.affineSubspaceMap_apply_symm_apply e.toAffineEquiv s x

end ContinuousAffineEquiv

namespace AffineSubspace

variable {R V P : Type*} [Ring R] [AddCommGroup V] [Module R V] [TopologicalSpace P]
  [AddTorsor V P]

variable [TopologicalSpace V] [IsTopologicalAddTorsor P]

instance {s : AffineSubspace R P} [Nonempty s] : IsTopologicalAddTorsor s where
  continuous_vadd := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    fun_prop
  continuous_vsub := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    fun_prop

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isClosed_direction_iff` / 定理 `isClosed_direction_iff`

English:
theorem isClosed_direction_iff
  given: [T1Space V] (s : AffineSubspace R P)
  proof: by
  rcases s.eq_bot_or_nonempty with (rfl | ⟨x, hx⟩); · simp
  rw [← (Homeomorph.vaddConst x).symm.isClosed_image]; rw [AffineSubspace.coe_direction_eq_vsub_set_right hx]
  simp only [Homeomorph.vaddConst_symm_apply]

中文:
定理 isClosed_direction_iff
  条件: [T1Space V] (s : AffineSubspace R P)
  证明: by
  rcases s.eq_bot_or_nonempty with (rfl | ⟨x, hx⟩); · simp
  rw [← (Homeomorph.vaddConst x).symm.isClosed_image]; rw [AffineSubspace.coe_direction_eq_vsub_set_right hx]
  simp only [Homeomorph.vaddConst_symm_apply]

Depends on / 依赖: AffineSubspace, AffineSubspace.coe_direction_eq_vsub_set_right, Homeomorph, Homeomorph.vaddConst, Homeomorph.vaddConst_symm_apply, coe_direction_eq_vsub_set_right, eq_bot_or_nonempty, isClosed_image, s.eq_bot_or_nonempty, symm.isClosed_image, vaddConst, vaddConst_symm_apply
-/
theorem isClosed_direction_iff [T1Space V] (s : AffineSubspace R P) :
    IsClosed (s.direction : Set V) ↔ IsClosed (s : Set P) := by
  rcases s.eq_bot_or_nonempty with (rfl | ⟨x, hx⟩); · simp
  rw [← (Homeomorph.vaddConst x).symm.isClosed_image]; rw [AffineSubspace.coe_direction_eq_vsub_set_right hx]
  simp only [Homeomorph.vaddConst_symm_apply]

end AffineSubspace
