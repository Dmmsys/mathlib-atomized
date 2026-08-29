/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/
module

public import Mathlib.Topology.Maps.Proper.Basic

/-! # Restriction of a closed compact set in a product space to a set of coordinates

We show that the image of a compact closed set `s` in a product `Π i : ι, α i` by
the restriction to a subset of coordinates `S : Set ι` is a closed set.

The idea of the proof is to use `isClosedMap_snd_of_compactSpace`, which is the fact that if
`X` is a compact topological space, then `Prod.snd : X × Y → Y` is a closed map.

We remark that `s` is included in the set `Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s`, and we build
a homeomorphism
`Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s ≃ₜ Sᶜ.domRestrict '' s × Π i : S, α i`.
`Sᶜ.domRestrict '' s` is a compact space since `s` is compact, and the lemma applies,
with `X = Sᶜ.domRestrict '' s` and `Y = Π i : S, α i`.

-/

@[expose] public section

open Set

variable {ι : Type*} {α : ι -> Type*} {s : Set (Π i, α i)} {i : ι} {S : Set ι}

namespace Topology

open scoped Classical in
/--
Definition of `reorderRestrictProd` / `reorderRestrictProd` 的定义

English:
definition reorderRestrictProd
  signature: (S : Set ι) (s : Set (Π j, α j))
  body: fun j => if h : j in S
    then (p.2 : Π j : ↑(S : Set ι), α j) ⟨j, h⟩
    else (p.1 : Π j : ↑(Sᶜ : Set ι), α j) ⟨j, h⟩

@[simp]

中文:
定义 reorderRestrictProd
  签名: (S : 集合 ι) (s : 集合 (Π j, α j))
  定义体: fun j => if h : j in S
    then (p.2 : Π j : ↑(S : Set ι), α j) ⟨j, h⟩
    else (p.1 : Π j : ↑(Sᶜ : Set ι), α j) ⟨j, h⟩

@[simp]
-/
noncomputable def reorderRestrictProd (S : Set ι) (s : Set (Π j, α j))
    (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) :
    Π j, α j :=
  fun j => if h : j in S
    then (p.2 : Π j : ↑(S : Set ι), α j) ⟨j, h⟩
    else (p.1 : Π j : ↑(Sᶜ : Set ι), α j) ⟨j, h⟩

@[simp]
/--
lemma `reorderRestrictProd_of_mem` / 引理 `reorderRestrictProd_of_mem`

English:
lemma reorderRestrictProd_of_mem
  given: (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) (j : S)
  proof: by
  have hj : ↑j in S := j.prop
  simp [reorderRestrictProd, hj]

@[simp]

中文:
引理 reorderRestrictProd_of_mem
  条件: (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) (j : S)
  证明: by
  have hj : ↑j in S := j.prop
  simp [reorderRestrictProd, hj]

@[simp]

Depends on / 依赖: j.prop, reorderRestrictProd
-/
lemma reorderRestrictProd_of_mem (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) (j : S) :
    reorderRestrictProd S s p j = (p.2 : Π j : ↑(S : Set ι), α j) j := by
  have hj : ↑j in S := j.prop
  simp [reorderRestrictProd, hj]

@[simp]
/--
lemma `reorderRestrictProd_of_compl` / 引理 `reorderRestrictProd_of_compl`

English:
lemma reorderRestrictProd_of_compl
  given: (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) (j : (Sᶜ : Set ι))
  proof: by
  have hj : ↑j ∉ S := j.prop
  simp [reorderRestrictProd, hj]

@[simp]

中文:
引理 reorderRestrictProd_of_compl
  条件: (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) (j : (Sᶜ : 集合 ι))
  证明: by
  have hj : ↑j ∉ S := j.prop
  simp [reorderRestrictProd, hj]

@[simp]

Depends on / 依赖: j.prop, reorderRestrictProd
-/
lemma reorderRestrictProd_of_compl (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) (j : (Sᶜ : Set ι)) :
    reorderRestrictProd S s p j = (p.1 : Π j : ↑(Sᶜ : Set ι), α j) j := by
  have hj : ↑j ∉ S := j.prop
  simp [reorderRestrictProd, hj]

@[simp]
/--
lemma `restrict_compl_reorderRestrictProd` / 引理 `restrict_compl_reorderRestrictProd`

English:
lemma restrict_compl_reorderRestrictProd
  given: (p : Sᶜ.domRestrict '' s × (Π i : S, α i))
  proof: by ext; simp

中文:
引理 restrict_compl_reorderRestrictProd
  条件: (p : Sᶜ.domRestrict '' s × (Π i : S, α i))
  证明: by ext; simp
-/
lemma restrict_compl_reorderRestrictProd (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) :
    Sᶜ.domRestrict (reorderRestrictProd S s p) = p.1 := by ext; simp

/--
lemma `continuous_reorderRestrictProd` / 引理 `continuous_reorderRestrictProd`

English:
lemma continuous_reorderRestrictProd
  given: [forall i, TopologicalSpace (α i)]
  proof: by
  refine continuous_pi fun j => ?_
  simp only [reorderRestrictProd]
  split_ifs with h
  · fun_prop
  · exact ((continuous_apply _).comp continuous_subtype_val).comp continuous_fst

中文:
引理 continuous_reorderRestrictProd
  条件: [对任意 i, 拓扑空间 (α i)]
  证明: by
  refine continuous_pi fun j => ?_
  simp only [reorderRestrictProd]
  split_ifs with h
  · fun_prop
  · exact ((continuous_apply _).comp continuous_subtype_val).comp continuous_fst

Depends on / 依赖: continuous_apply, continuous_fst, continuous_pi, continuous_subtype_val, fun_prop, reorderRestrictProd, split_ifs
-/
lemma continuous_reorderRestrictProd [forall i, TopologicalSpace (α i)] :
    Continuous (reorderRestrictProd S s) := by
  refine continuous_pi fun j => ?_
  simp only [reorderRestrictProd]
  split_ifs with h
  · fun_prop
  · exact ((continuous_apply _).comp continuous_subtype_val).comp continuous_fst

/--
lemma `reorderRestrictProd_mem_preimage_image_restrict` / 引理 `reorderRestrictProd_mem_preimage_image_restrict`

English:
lemma reorderRestrictProd_mem_preimage_image_restrict
  given: (p : Sᶜ.domRestrict '' s × (Π i : S, α i))
  proof: by
  obtain ⟨y, hy_mem_s, hy_eq⟩ := p.1.2
  exact ⟨y, hy_mem_s, hy_eq.trans (restrict_compl_reorderRestrictProd p).symm⟩

@[simp]

中文:
引理 reorderRestrictProd_mem_preimage_image_restrict
  条件: (p : Sᶜ.domRestrict '' s × (Π i : S, α i))
  证明: by
  obtain ⟨y, hy_mem_s, hy_eq⟩ := p.1.2
  exact ⟨y, hy_mem_s, hy_eq.trans (restrict_compl_reorderRestrictProd p).symm⟩

@[simp]

Depends on / 依赖: hy_eq, hy_eq.trans, hy_mem_s, restrict_compl_reorderRestrictProd
-/
lemma reorderRestrictProd_mem_preimage_image_restrict (p : Sᶜ.domRestrict '' s × (Π i : S, α i)) :
    reorderRestrictProd S s p in Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s := by
  obtain ⟨y, hy_mem_s, hy_eq⟩ := p.1.2
  exact ⟨y, hy_mem_s, hy_eq.trans (restrict_compl_reorderRestrictProd p).symm⟩

@[simp]
/--
lemma `reorderRestrictProd_restrict_compl` / 引理 `reorderRestrictProd_restrict_compl`

English:
lemma reorderRestrictProd_restrict_compl
  given: (x : Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s)
  proof: by
  ext; simp [reorderRestrictProd]

中文:
引理 reorderRestrictProd_restrict_compl
  条件: (x : Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s)
  证明: by
  ext; simp [reorderRestrictProd]

Depends on / 依赖: reorderRestrictProd
-/
lemma reorderRestrictProd_restrict_compl (x : Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s) :
    reorderRestrictProd S s ⟨⟨Sᶜ.domRestrict x, x.2⟩, fun i => (x : Π j, α j) i⟩ =
      (x : Π j, α j) := by
  ext; simp [reorderRestrictProd]

/-- Homeomorphism between the set of functions that coincide with a given set of functions away
from a given set `S`, and dependent functions away from `S` times any value on `S`. -/
noncomputable
/--
Definition of `_root_.Homeomorph.preimageImageRestrict` / `_root_.Homeomorph.preimageImageRestrict` 的定义

English:
definition _root_.Homeomorph.preimageImageRestrict
  signature: (α : ι -> Type*) [forall i, TopologicalSpace (α i)]
  body: ⟨⟨Sᶜ.domRestrict x, x.2⟩, fun i => (x : Π j, α j) i⟩
  invFun p := ⟨reorderRestrictProd S s p, reorderRestrictProd_mem_preimage_image_restrict p⟩
  left_inv x := by ext; simp
  right_inv p := by ext <;> simp
  continuous_toFun := by
    refine (Continuous.subtype_mk (by fun_prop) _).prodMk ?_
    rw

中文:
定义 _root_.同胚.preimageImageRestrict
  签名: (α : ι -> 类型) [对任意 i, 拓扑空间 (α i)]
  定义体: ⟨⟨Sᶜ.domRestrict x, x.2⟩, fun i => (x : Π j, α j) i⟩
  invFun p := ⟨reorderRestrictProd S s p, reorderRestrictProd_mem_preimage_image_restrict p⟩
  left_inv x := by ext; simp
  right_inv p := by ext <;> simp
  continuous_toFun := by
    refine (Continuous.subtype_mk (by fun_prop) _).prodMk ?_
    rw

Depends on / 依赖: domRestrict
-/
def _root_.Homeomorph.preimageImageRestrict (α : ι -> Type*) [forall i, TopologicalSpace (α i)]
    (S : Set ι) (s : Set (Π j, α j)) :
    Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s ≃ₜ Sᶜ.domRestrict '' s × (Π i : S, α i) where
  toFun x := ⟨⟨Sᶜ.domRestrict x, x.2⟩, fun i => (x : Π j, α j) i⟩
  invFun p := ⟨reorderRestrictProd S s p, reorderRestrictProd_mem_preimage_image_restrict p⟩
  left_inv x := by ext; simp
  right_inv p := by ext <;> simp
  continuous_toFun := by
    refine (Continuous.subtype_mk (by fun_prop) _).prodMk ?_
    rw [continuous_pi_iff]
    exact fun _ => (continuous_apply _).comp continuous_subtype_val
  continuous_invFun := continuous_reorderRestrictProd.subtype_mk _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `image_snd_preimageImageRestrict` / 引理 `image_snd_preimageImageRestrict`

English:
lemma image_snd_preimageImageRestrict
  given: [forall i, TopologicalSpace (α i)]
  proof: by
  ext x
  simp only [Homeomorph.preimageImageRestrict, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
    mem_image, mem_preimage, Subtype.exists, exists_and_left, Prod.exists, Prod.mk.injEq,
    exists_and_right, exists_eq_right, Subtype.mk.injEq, exists_prop]
  constructor
  · rintro ⟨y, _, z, 

中文:
引理 image_snd_preimageImageRestrict
  条件: [对任意 i, 拓扑空间 (α i)]
  证明: by
  ext x
  simp only [Homeomorph.preimageImageRestrict, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
    mem_image, mem_preimage, Subtype.exists, exists_and_left, Prod.exists, Prod.mk.injEq,
    exists_and_right, exists_eq_right, Subtype.mk.injEq, exists_prop]
  constructor
  · rintro ⟨y, _, z, 

Depends on / 依赖: Equiv.coe_fn_mk, Homeomorph, Homeomorph.homeomorph_mk_coe, Homeomorph.preimageImageRestrict, Prod.exists, Prod.mk.injEq, Subtype, Subtype.exists, Subtype.mk.injEq, coe_fn_mk, domRestrict, exists_and_left, exists_and_right, exists_eq_right, exists_prop, homeomorph_mk_coe, hz_mem, mem_image, mem_image_of_mem, mem_preimage
-/
lemma image_snd_preimageImageRestrict [forall i, TopologicalSpace (α i)] :
    Prod.snd '' (Homeomorph.preimageImageRestrict α S s ''
        ((fun (x : Sᶜ.domRestrict ⁻¹' Sᶜ.domRestrict '' s) => (x : Π j, α j)) ⁻¹' s))
      = S.domRestrict '' s := by
  ext x
  simp only [Homeomorph.preimageImageRestrict, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk,
    mem_image, mem_preimage, Subtype.exists, exists_and_left, Prod.exists, Prod.mk.injEq,
    exists_and_right, exists_eq_right, Subtype.mk.injEq, exists_prop]
  constructor
  · rintro ⟨y, _, z, hz_mem, _, hzx⟩
    exact ⟨z, hz_mem, hzx⟩
  · rintro ⟨z, hz_mem, hzx⟩
    exact ⟨Sᶜ.domRestrict z, mem_image_of_mem Sᶜ.domRestrict hz_mem, z, hz_mem,
      ⟨⟨⟨z, hz_mem, rfl⟩, rfl⟩, hzx⟩⟩

end Topology

section IsClosed

variable [forall i, TopologicalSpace (α i)]

/--
theorem `IsCompact.isClosed_image_restrict` / 定理 `IsCompact.isClosed_image_restrict`

English:
theorem IsCompact.isClosed_image_restrict
  statement: (S : Set ι)
  proof: by
  rw [← Topology.image_snd_preimageImageRestrict]
  have : CompactSpace (Sᶜ.domRestrict '' s) :=
    isCompact_iff_compactSpace.mp (hs_compact.image (Pi.continuous_domRestrict _))
  refine isClosedMap_snd_of_compactSpace _ ?_
  rw [Homeomorph.isClosed_image]
  exact hs_closed.preimage continuous_

中文:
定理 是紧集.isClosed_image_restrict
  结论: (S : 集合 ι)
  证明: by
  rw [← Topology.image_snd_preimageImageRestrict]
  have : CompactSpace (Sᶜ.domRestrict '' s) :=
    isCompact_iff_compactSpace.mp (hs_compact.image (Pi.continuous_domRestrict _))
  refine isClosedMap_snd_of_compactSpace _ ?_
  rw [Homeomorph.isClosed_image]
  exact hs_closed.preimage continuous_

Depends on / 依赖: CompactSpace, Homeomorph, Homeomorph.isClosed_image, Pi.continuous_domRestrict, Topology, Topology.image_snd_preimageImageRestrict, continuous_domRestrict, continuous_subtype_val, domRestrict, hs_closed, hs_closed.preimage, hs_compact, hs_compact.image, image_snd_preimageImageRestrict, isClosedMap_snd_of_compactSpace, isClosed_image, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, preimage
-/
theorem IsCompact.isClosed_image_restrict (S : Set ι)
    (hs_compact : IsCompact s) (hs_closed : IsClosed s) :
    IsClosed (S.domRestrict '' s) := by
  rw [← Topology.image_snd_preimageImageRestrict]
  have : CompactSpace (Sᶜ.domRestrict '' s) :=
    isCompact_iff_compactSpace.mp (hs_compact.image (Pi.continuous_domRestrict _))
  refine isClosedMap_snd_of_compactSpace _ ?_
  rw [Homeomorph.isClosed_image]
  exact hs_closed.preimage continuous_subtype_val

/--
lemma `isClosedMap_restrict_of_compactSpace` / 引理 `isClosedMap_restrict_of_compactSpace`

English:
lemma isClosedMap_restrict_of_compactSpace
  given: [forall i, CompactSpace (α i)]
  proof: fun s hs => by
  classical
  have : S.domRestrict (π := α) = Prod.fst ∘ (Homeomorph.piEquivPiSubtypeProd (· in S) α) := rfl
  rw [this]; rw [image_comp]
exact isClosedMap_fst_of_compactSpace _ (Homeomorph.isClosed_image _).mpr hs

中文:
引理 isClosedMap_restrict_of_compactSpace
  条件: [对任意 i, 紧空间 (α i)]
  证明: fun s hs => by
  classical
  have : S.domRestrict (π := α) = Prod.fst ∘ (Homeomorph.piEquivPiSubtypeProd (· in S) α) := rfl
  rw [this]; rw [image_comp]
exact isClosedMap_fst_of_compactSpace _ (Homeomorph.isClosed_image _).mpr hs

Depends on / 依赖: Homeomorph, Homeomorph.isClosed_image, Homeomorph.piEquivPiSubtypeProd, Prod.fst, S.domRestrict, classical, domRestrict, image_comp, isClosedMap_fst_of_compactSpace, isClosed_image, piEquivPiSubtypeProd
-/
lemma isClosedMap_restrict_of_compactSpace [forall i, CompactSpace (α i)] :
    IsClosedMap (S.domRestrict : (Π i, α i) -> _) := fun s hs => by
  classical
  have : S.domRestrict (π := α) = Prod.fst ∘ (Homeomorph.piEquivPiSubtypeProd (· in S) α) := rfl
  rw [this]; rw [image_comp]
exact isClosedMap_fst_of_compactSpace _ (Homeomorph.isClosed_image _).mpr hs

/--
lemma `IsClosed.isClosed_image_eval` / 引理 `IsClosed.isClosed_image_eval`

English:
lemma IsClosed.isClosed_image_eval
  statement: (i : ι)
  proof: by
  suffices IsClosed (Set.domRestrict {i} '' s) by
    have : Homeomorph.piUnique _ ∘ Set.domRestrict {i} = fun (x : Π j, α j) => x i := rfl
    rwa [← this, image_comp, Homeomorph.isClosed_image (Homeomorph.piUnique _)]
  exact hs_compact.isClosed_image_restrict {i} hs_closed

中文:
引理 是闭集.isClosed_image_eval
  结论: (i : ι)
  证明: by
  suffices IsClosed (Set.domRestrict {i} '' s) by
    have : Homeomorph.piUnique _ ∘ Set.domRestrict {i} = fun (x : Π j, α j) => x i := rfl
    rwa [← this, image_comp, Homeomorph.isClosed_image (Homeomorph.piUnique _)]
  exact hs_compact.isClosed_image_restrict {i} hs_closed

Depends on / 依赖: Homeomorph, Homeomorph.isClosed_image, Homeomorph.piUnique, IsClosed, Set.domRestrict, domRestrict, hs_closed, hs_compact, hs_compact.isClosed_image_restrict, image_comp, isClosed_image, isClosed_image_restrict, piUnique
-/
lemma IsClosed.isClosed_image_eval (i : ι)
    (hs_compact : IsCompact s) (hs_closed : IsClosed s) :
    IsClosed ((fun x => x i) '' s) := by
  suffices IsClosed (Set.domRestrict {i} '' s) by
    have : Homeomorph.piUnique _ ∘ Set.domRestrict {i} = fun (x : Π j, α j) => x i := rfl
    rwa [← this, image_comp, Homeomorph.isClosed_image (Homeomorph.piUnique _)]
  exact hs_compact.isClosed_image_restrict {i} hs_closed

end IsClosed
