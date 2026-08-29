/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.GroupTheory.ResiduallyFinite
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Profinite completion of groups

We define the profinite completion of a group as the limit of its finite quotients,
and prove its universal property.
-/

@[expose] public section

namespace OpenNormalSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- An open normal subgroup of a compact topological group has finite index. -/
@[to_additive
  /-- An open normal additive subgroup of a compact topological additive group has finite index. -/]
/--
Definition of `toFiniteIndexNormalSubgroup` / `toFiniteIndexNormalSubgroup` 的定义

English:
definition toFiniteIndexNormalSubgroup
  signature: [CompactSpace G] [ContinuousMul G]
  body: letI : H.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  FiniteIndexNormalSubgroup.ofSubgroup H.toSubgroup

@[to_additive]

中文:
定义 toFiniteIndexNormalSubgroup
  签名: [紧空间 G] [连续乘法 G]
  定义体: letI : H.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  FiniteIndexNormalSubgroup.ofSubgroup H.toSubgroup

@[to_additive]

Depends on / 依赖: FiniteIndex, FiniteIndexNormalSubgroup, FiniteIndexNormalSubgroup.ofSubgroup, H.toSubgroup, H.toSubgroup.FiniteIndex, Subgroup, Subgroup.finiteIndex_of_finite_quotient, finiteIndex_of_finite_quotient, ofSubgroup, toSubgroup
-/
def toFiniteIndexNormalSubgroup [CompactSpace G] [ContinuousMul G]
    (H : OpenNormalSubgroup G) : FiniteIndexNormalSubgroup G :=
  letI : H.toSubgroup.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  FiniteIndexNormalSubgroup.ofSubgroup H.toSubgroup

@[to_additive]
/--
theorem `toFiniteIndexNormalSubgroup_mono` / 定理 `toFiniteIndexNormalSubgroup_mono`

English:
theorem toFiniteIndexNormalSubgroup_mono
  statement: [CompactSpace G] [ContinuousMul G]
  proof: fun _ hx => h hx

@[to_additive]

中文:
定理 toFiniteIndexNormalSubgroup_mono
  结论: [紧空间 G] [连续乘法 G]
  证明: fun _ hx => h hx

@[to_additive]
-/
theorem toFiniteIndexNormalSubgroup_mono [CompactSpace G] [ContinuousMul G]
    {H K : OpenNormalSubgroup G} (h : H <= K) :
    H.toFiniteIndexNormalSubgroup <= K.toFiniteIndexNormalSubgroup :=
  fun _ hx => h hx

@[to_additive]
/--
theorem `toFiniteIndexNormalSubgroup_injective` / 定理 `toFiniteIndexNormalSubgroup_injective`

English:
theorem toFiniteIndexNormalSubgroup_injective
  given: [CompactSpace G] [ContinuousMul G]
  proof: by
  intro H K h
  apply toSubgroup_injective
  exact congrArg (fun L : FiniteIndexNormalSubgroup G => (L : Subgroup G)) h

中文:
定理 toFiniteIndexNormalSubgroup_injective
  条件: [紧空间 G] [连续乘法 G]
  证明: by
  intro H K h
  apply toSubgroup_injective
  exact congrArg (fun L : FiniteIndexNormalSubgroup G => (L : Subgroup G)) h

Depends on / 依赖: FiniteIndexNormalSubgroup, Subgroup, toSubgroup_injective
-/
theorem toFiniteIndexNormalSubgroup_injective [CompactSpace G] [ContinuousMul G] :
    Function.Injective (toFiniteIndexNormalSubgroup (G := G)) := by
  intro H K h
  apply toSubgroup_injective
  exact congrArg (fun L : FiniteIndexNormalSubgroup G => (L : Subgroup G)) h

end OpenNormalSubgroup

namespace ProfiniteGrp

open CategoryTheory

universe u

namespace ProfiniteCompletion

variable (G : GrpCat.{u})

/-- The diagram of finite quotients indexed by finite-index normal subgroups of `G`. -/
@[to_additive /-- The diagram of finite quotients indexed by finite-index normal subgroups. -/]
/--
Definition of `finiteGrpDiagram` / `finiteGrpDiagram` 的定义

English:
definition finiteGrpDiagram
  signature: : FiniteIndexNormalSubgroup G ⥤ FiniteGrp.{u} where
  body: FiniteGrp.of G ⧸ H.toSubgroup
map f := FiniteGrp.ofHom QuotientGroup.map _ _ (MonoidHom.id _) f.le
  map_id H := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

中文:
定义 finiteGrpDiagram
  签名: : FiniteIndexNormal子群 G ⥤ FiniteGrp.{u} where
  定义体: FiniteGrp.of G ⧸ H.toSubgroup
map f := FiniteGrp.ofHom QuotientGroup.map _ _ (MonoidHom.id _) f.le
  map_id H := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

Depends on / 依赖: FiniteGrp, FiniteGrp.of, H.toSubgroup, toSubgroup
-/
def finiteGrpDiagram : FiniteIndexNormalSubgroup G ⥤ FiniteGrp.{u} where
obj H := FiniteGrp.of G ⧸ H.toSubgroup
map f := FiniteGrp.ofHom QuotientGroup.map _ _ (MonoidHom.id _) f.le
  map_id H := by ext ⟨x⟩; rfl
  map_comp f g := by ext ⟨x⟩; rfl

/-- The finite-quotient diagram viewed in `ProfiniteGrp`. -/
@[to_additive /-- The finite-quotient diagram viewed in `ProfiniteAddGrp`. -/]
/--
Definition of `diagram` / `diagram` 的定义

English:
definition diagram
  signature: : FiniteIndexNormalSubgroup G ⥤ ProfiniteGrp.{u}
  body: finiteGrpDiagram _ ⋙ forget₂ _ _

中文:
定义 diagram
  签名: : FiniteIndexNormal子群 G ⥤ ProfiniteGrp.{u}
  定义体: finiteGrpDiagram _ ⋙ forget₂ _ _

Depends on / 依赖: finiteGrpDiagram
-/
def diagram : FiniteIndexNormalSubgroup G ⥤ ProfiniteGrp.{u} :=
  finiteGrpDiagram _ ⋙ forget₂ _ _

/-- The profinite completion of `G` as a projective limit. -/
@[to_additive /-- The profinite completion of `G` as a projective limit. -/]
/--
Definition of `completion` / `completion` 的定义

English:
definition completion
  signature: : ProfiniteGrp.{u}
  body: limit (diagram G)

中文:
定义 completion
  签名: : ProfiniteGrp.{u}
  定义体: limit (diagram G)

Depends on / 依赖: diagram
-/
def completion : ProfiniteGrp.{u} := limit (diagram G)

/-- The canonical map from `G` to its profinite completion, as a function. -/
@[to_additive /-- The canonical map from `G` to its profinite completion, as a function. -/]
/--
Definition of `etaFn` / `etaFn` 的定义

English:
definition etaFn
  signature: (x : G)
  body: ⟨fun _ => QuotientGroup.mk x, fun _ _ _ => rfl⟩

中文:
定义 etaFn
  签名: (x : G)
  定义体: ⟨fun _ => QuotientGroup.mk x, fun _ _ _ => rfl⟩

Depends on / 依赖: QuotientGroup, QuotientGroup.mk
-/
def etaFn (x : G) : completion G := ⟨fun _ => QuotientGroup.mk x, fun _ _ _ => rfl⟩

/-- The canonical morphism from `G` to its profinite completion. -/
@[to_additive /-- The canonical morphism from `G` to its profinite completion. -/]
/--
Definition of `eta` / `eta` 的定义

English:
definition eta
  signature: : G ⟶ GrpCat.of (completion G)
  body: GrpCat.ofHom {
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
}

中文:
定义 eta
  签名: : G ⟶ 群范畴.of (completion G)
  定义体: GrpCat.ofHom {
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
}

Depends on / 依赖: GrpCat, GrpCat.ofHom
-/
def eta : G ⟶ GrpCat.of (completion G) := GrpCat.ofHom {
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
}

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `mono_eta_iff_residuallyFinite` / 定理 `mono_eta_iff_residuallyFinite`

English:
theorem mono_eta_iff_residuallyFinite
  statement: Mono (eta G) ↔ Group.ResiduallyFinite G
  proof: by
  rw [GrpCat.mono_iff_injective]; rw [injective_iff_map_eq_one]; rw [Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  refine forall_congr' fun g => imp_congr_left ?_
  rw [Subtype.ext_iff]; rw [funext_iff]
  exact forall_congr' fun H => QuotientGroup.eq_one_iff g

@[to_additive]

中文:
定理 mono_eta_iff_residuallyFinite
  结论: 单态射 (eta G) ↔ 群.ResiduallyFinite G
  证明: by
  rw [GrpCat.mono_iff_injective]; rw [injective_iff_map_eq_one]; rw [Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  refine forall_congr' fun g => imp_congr_left ?_
  rw [Subtype.ext_iff]; rw [funext_iff]
  exact forall_congr' fun H => QuotientGroup.eq_one_iff g

@[to_additive]

Depends on / 依赖: Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup, GrpCat, GrpCat.mono_iff_injective, QuotientGroup, QuotientGroup.eq_one_iff, Subtype, Subtype.ext_iff, eq_one_iff, ext_iff, forall_congr, funext_iff, imp_congr_left, injective_iff_map_eq_one, mono_iff_injective, residuallyFinite_iff_forall_finiteIndexNormalSubgroup
-/
theorem mono_eta_iff_residuallyFinite : Mono (eta G) ↔ Group.ResiduallyFinite G := by
  rw [GrpCat.mono_iff_injective]; rw [injective_iff_map_eq_one]; rw [Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  refine forall_congr' fun g => imp_congr_left ?_
  rw [Subtype.ext_iff]; rw [funext_iff]
  exact forall_congr' fun H => QuotientGroup.eq_one_iff g

@[to_additive]
/--
theorem `etaFn_injective_iff_residuallyFinite` / 定理 `etaFn_injective_iff_residuallyFinite`

English:
theorem etaFn_injective_iff_residuallyFinite
  proof: (GrpCat.mono_iff_injective (eta G)).symm.trans (mono_eta_iff_residuallyFinite G)

中文:
定理 etaFn_injective_iff_residuallyFinite
  证明: (GrpCat.mono_iff_injective (eta G)).symm.trans (mono_eta_iff_residuallyFinite G)

Depends on / 依赖: GrpCat, GrpCat.mono_iff_injective, mono_eta_iff_residuallyFinite, mono_iff_injective, symm.trans
-/
theorem etaFn_injective_iff_residuallyFinite :
    Function.Injective (etaFn G) ↔ Group.ResiduallyFinite G :=
  (GrpCat.mono_iff_injective (eta G)).symm.trans (mono_eta_iff_residuallyFinite G)

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
lemma `denseRange` / 引理 `denseRange`

English:
lemma denseRange
  statement: DenseRange (etaFn G)
  proof: by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  rw [← hsv]; rw [Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M : Subgroup G := iInf fun (j : J) => j.val
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hMFinite : M.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  let m : FiniteIndexNormalSubgroup G := { toSubgroup := M }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use etaFn G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => (j.val.toSubgroup)) ⟨a, a_in_J⟩).hom
  rw [← (etaFn G origin).property M_to_Na]
  dsimp [etaFn] at ⊢ horigin
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).right

中文:
引理 denseRange
  结论: DenseRange (etaFn G)
  证明: by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  rw [← hsv]; rw [Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M : Subgroup G := iInf fun (j : J) => j.val
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hMFinite : M.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  let m : FiniteIndexNormalSubgroup G := { toSubgroup := M }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use etaFn G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => (j.val.toSubgroup)) ⟨a, a_in_J⟩).hom
  rw [← (etaFn G origin).property M_to_Na]
  dsimp [etaFn] at ⊢ horigin
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).right

Depends on / 依赖: FiniteIndex, FiniteIndexNormalSubgroup, M.FiniteIndex, M.Normal, Normal, QuotientGroup, QuotientGroup.mk, Set.mem_preimage, Subgroup, Subgroup.finiteIndex_iInf, Subgroup.normal_iInf_normal, _surjectiv, dense_iff_inter_open, dense_iff_inter_open.mpr, finiteIndex_iInf, hMFinite, infer_instance, isOpen_pi_iff, isOpen_pi_iff.mp, j.val
-/
lemma denseRange : DenseRange (etaFn G) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  rw [← hsv]; rw [Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M : Subgroup G := iInf fun (j : J) => j.val
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hMFinite : M.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  let m : FiniteIndexNormalSubgroup G := { toSubgroup := M }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use etaFn G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => (j.val.toSubgroup)) ⟨a, a_in_J⟩).hom
  rw [← (etaFn G origin).property M_to_Na]
  dsimp [etaFn] at ⊢ horigin
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).right

variable {G}
variable {P : ProfiniteGrp.{u}}

/-- The preimage of an open normal subgroup under a morphism to a profinite group. -/
@[to_additive /-- The preimage of an open normal subgroup under a morphism to a profinite group. -/]
/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P)
  body: H.toFiniteIndexNormalSubgroup.comap f.hom

@[to_additive]

中文:
定义 原像
  签名: (f : G ⟶ 群范畴.of P) (H : OpenNormal子群 P)
  定义体: H.toFiniteIndexNormalSubgroup.comap f.hom

@[to_additive]

Depends on / 依赖: H.toFiniteIndexNormalSubgroup.comap, f.hom, toFiniteIndexNormalSubgroup
-/
def preimage (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P) : FiniteIndexNormalSubgroup G :=
  H.toFiniteIndexNormalSubgroup.comap f.hom

@[to_additive]
/--
lemma `preimage_le` / 引理 `preimage_le`

English:
lemma preimage_le
  statement: {f : G ⟶ GrpCat.of P} {H K : OpenNormalSubgroup P}
  proof: FiniteIndexNormalSubgroup.comap_mono _ h

中文:
引理 preimage_le
  结论: {f : G ⟶ 群范畴.of P} {H K : OpenNormal子群 P}
  证明: FiniteIndexNormalSubgroup.comap_mono _ h

Depends on / 依赖: FiniteIndexNormalSubgroup, FiniteIndexNormalSubgroup.comap_mono, comap_mono
-/
lemma preimage_le {f : G ⟶ GrpCat.of P} {H K : OpenNormalSubgroup P}
    (h : H <= K) : preimage f H <= preimage f K :=
  FiniteIndexNormalSubgroup.comap_mono _ h

/-- The induced map on finite quotients coming from a morphism to `P`. -/
@[to_additive /-- The induced map on finite quotients coming from a morphism to `P`. -/]
/--
Definition of `quotientMap` / `quotientMap` 的定义

English:
definition quotientMap
  signature: (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P)
  body: FiniteGrp.ofHom QuotientGroup.map _ _ f.hom fun _ h => h

中文:
定义 quotientMap
  签名: (f : G ⟶ 群范畴.of P) (H : OpenNormal子群 P)
  定义体: FiniteGrp.ofHom QuotientGroup.map _ _ f.hom fun _ h => h

Depends on / 依赖: FiniteGrp, FiniteGrp.ofHom, QuotientGroup, QuotientGroup.map, f.hom
-/
def quotientMap (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P) :
    FiniteGrp.of (G ⧸ (preimage f H).toSubgroup) ⟶ FiniteGrp.of (P ⧸ H.toSubgroup) :=
FiniteGrp.ofHom QuotientGroup.map _ _ f.hom fun _ h => h

/-- The universal morphism from the profinite completion to `P`. -/
noncomputable
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : G ⟶ GrpCat.of P)
  body: P.isLimitCone.lift ⟨_, {
    app H := (limitCone (diagram G)).π.app _ ≫ (ofFiniteGrpHom <| quotientMap f H)
    naturality := by
      intro X Y g
      ext ⟨x, hx⟩
      -- TODO: `dsimp` should handle this `change`; investigate missing simp lemmas in the
      -- `ProfiniteGrp` / `CompHausLike` API.
      change quotientMap f Y (x <| preimage f Y) =
        P.diagram.map g (quotientMap _ _ <| x <| preimage f X)
have := hx .hom preimage_le (f := f) g.le
      obtain ⟨t, ht⟩ : exists g : G, QuotientGroup.mk g = x (preimage f X) :=
        QuotientGroup.mk_surjective (x (preimage f X))
      rw [← this]; rw [← ht]
      have := P.cone.π.naturality g
      apply_fun fun q => q (f t) at this
      exact this
  }⟩

中文:
定义 lift
  签名: (f : G ⟶ 群范畴.of P)
  定义体: P.isLimitCone.lift ⟨_, {
    app H := (limitCone (diagram G)).π.app _ ≫ (ofFiniteGrpHom <| quotientMap f H)
    naturality := by
      intro X Y g
      ext ⟨x, hx⟩
      -- TODO: `dsimp` should handle this `change`; investigate missing simp lemmas in the
      -- `ProfiniteGrp` / `CompHausLike` API.
      change quotientMap f Y (x <| preimage f Y) =
        P.diagram.map g (quotientMap _ _ <| x <| preimage f X)
have := hx .hom preimage_le (f := f) g.le
      obtain ⟨t, ht⟩ : exists g : G, QuotientGroup.mk g = x (preimage f X) :=
        QuotientGroup.mk_surjective (x (preimage f X))
      rw [← this]; rw [← ht]
      have := P.cone.π.naturality g
      apply_fun fun q => q (f t) at this
      exact this
  }⟩

Depends on / 依赖: P.isLimitCone.lift, diagram, isLimitCone, limitCone, naturality, ofFiniteGrpHom, quotientMap
-/
def lift (f : G ⟶ GrpCat.of P) : completion G ⟶ P :=
  P.isLimitCone.lift ⟨_, {
    app H := (limitCone (diagram G)).π.app _ ≫ (ofFiniteGrpHom <| quotientMap f H)
    naturality := by
      intro X Y g
      ext ⟨x, hx⟩
      -- TODO: `dsimp` should handle this `change`; investigate missing simp lemmas in the
      -- `ProfiniteGrp` / `CompHausLike` API.
      change quotientMap f Y (x <| preimage f Y) =
        P.diagram.map g (quotientMap _ _ <| x <| preimage f X)
have := hx .hom preimage_le (f := f) g.le
      obtain ⟨t, ht⟩ : exists g : G, QuotientGroup.mk g = x (preimage f X) :=
        QuotientGroup.mk_surjective (x (preimage f X))
      rw [← this]; rw [← ht]
      have := P.cone.π.naturality g
      apply_fun fun q => q (f t) at this
      exact this
  }⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `lift_eta` / 引理 `lift_eta`

English:
lemma lift_eta
  given: (f : G ⟶ GrpCat.of P)
  statement: eta G ≫ (forget₂ _ _).map (lift f) = f
  proof: by
  let e := isoLimittoFiniteQuotientFunctor P
  rw [← (forget₂ ProfiniteGrp GrpCat).mapIso e |>.cancel_iso_hom_right]
  dsimp
  rw [Category.assoc]; rw [← (forget₂ ProfiniteGrp GrpCat).map_comp (lift f) e.hom]
  change eta G ≫ ((forget₂ _ _).map ((_ ≫ e.inv) ≫ e.hom)) = _
  simp only [Category.assoc, Iso.inv_hom_id]
  rfl

@[to_additive]

中文:
引理 lift_eta
  条件: (f : G ⟶ 群范畴.of P)
  结论: eta G ≫ (forget₂ _ _).map (lift f) = f
  证明: by
  let e := isoLimittoFiniteQuotientFunctor P
  rw [← (forget₂ ProfiniteGrp GrpCat).mapIso e |>.cancel_iso_hom_right]
  dsimp
  rw [Category.assoc]; rw [← (forget₂ ProfiniteGrp GrpCat).map_comp (lift f) e.hom]
  change eta G ≫ ((forget₂ _ _).map ((_ ≫ e.inv) ≫ e.hom)) = _
  simp only [Category.assoc, Iso.inv_hom_id]
  rfl

@[to_additive]

Depends on / 依赖: Category, Category.assoc, GrpCat, Iso.inv_hom_id, ProfiniteGrp, cancel_iso_hom_right, e.hom, e.inv, inv_hom_id, isoLimittoFiniteQuotientFunctor, mapIso, map_comp
-/
lemma lift_eta (f : G ⟶ GrpCat.of P) : eta G ≫ (forget₂ _ _).map (lift f) = f := by
  let e := isoLimittoFiniteQuotientFunctor P
  rw [← (forget₂ ProfiniteGrp GrpCat).mapIso e |>.cancel_iso_hom_right]
  dsimp
  rw [Category.assoc]; rw [← (forget₂ ProfiniteGrp GrpCat).map_comp (lift f) e.hom]
  change eta G ≫ ((forget₂ _ _).map ((_ ≫ e.inv) ≫ e.hom)) = _
  simp only [Category.assoc, Iso.inv_hom_id]
  rfl

@[to_additive]
/--
lemma `lift_unique` / 引理 `lift_unique`

English:
lemma lift_unique
  statement: (f g : completion G ⟶ P)
  proof: by
  ext x
  apply congrFun
  refine (denseRange (G := G)).equalizer f.hom.continuous_toFun g.hom.continuous_toFun ?_
  funext y
  simpa [GrpCat.comp_apply] using! (ConcreteCategory.congr_hom h y)

中文:
引理 lift_unique
  结论: (f g : completion G ⟶ P)
  证明: by
  ext x
  apply congrFun
  refine (denseRange (G := G)).equalizer f.hom.continuous_toFun g.hom.continuous_toFun ?_
  funext y
  simpa [GrpCat.comp_apply] using! (ConcreteCategory.congr_hom h y)

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, GrpCat, GrpCat.comp_apply, comp_apply, congr_hom, continuous_toFun, denseRange, equalizer, f.hom.continuous_toFun, g.hom.continuous_toFun
-/
lemma lift_unique (f g : completion G ⟶ P)
    (h : eta G ≫ (forget₂ _ _).map f = eta G ≫ (forget₂ _ _).map g) : f = g := by
  ext x
  apply congrFun
  refine (denseRange (G := G)).equalizer f.hom.continuous_toFun g.hom.continuous_toFun ?_
  funext y
  simpa [GrpCat.comp_apply] using! (ConcreteCategory.congr_hom h y)

end ProfiniteCompletion

/-- The profinite completion functor. -/
@[simps]
/--
Definition of `profiniteCompletion` / `profiniteCompletion` 的定义

English:
definition profiniteCompletion
  signature: : GrpCat.{u} ⥤ ProfiniteGrp.{u} where
  body: ProfiniteCompletion.completion G
map f := ProfiniteCompletion.lift f ≫ ProfiniteCompletion.eta _
  map_id G := by
    apply ProfiniteCompletion.lift_unique
    cat_disch
  map_comp f g := by
    apply ProfiniteCompletion.lift_unique
    cat_disch

中文:
定义 profiniteCompletion
  签名: : 群范畴.{u} ⥤ ProfiniteGrp.{u} where
  定义体: ProfiniteCompletion.completion G
map f := ProfiniteCompletion.lift f ≫ ProfiniteCompletion.eta _
  map_id G := by
    apply ProfiniteCompletion.lift_unique
    cat_disch
  map_comp f g := by
    apply ProfiniteCompletion.lift_unique
    cat_disch

Depends on / 依赖: ProfiniteCompletion, ProfiniteCompletion.completion, completion
-/
noncomputable def profiniteCompletion : GrpCat.{u} ⥤ ProfiniteGrp.{u} where
  obj G := ProfiniteCompletion.completion G
map f := ProfiniteCompletion.lift f ≫ ProfiniteCompletion.eta _
  map_id G := by
    apply ProfiniteCompletion.lift_unique
    cat_disch
  map_comp f g := by
    apply ProfiniteCompletion.lift_unique
    cat_disch

namespace ProfiniteCompletion

/-- The hom-set equivalence exhibiting the adjunction. -/
noncomputable
/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: (G : GrpCat.{u}) (P : ProfiniteGrp.{u})
  body: eta G ≫ (forget₂ _ _).map f
  invFun f := lift f
  left_inv f := by apply lift_unique; simp
  right_inv f := by simp

中文:
定义 homEquiv
  签名: (G : 群范畴.{u}) (P : ProfiniteGrp.{u})
  定义体: eta G ≫ (forget₂ _ _).map f
  invFun f := lift f
  left_inv f := by apply lift_unique; simp
  right_inv f := by simp
-/
def homEquiv (G : GrpCat.{u}) (P : ProfiniteGrp.{u}) :
    (completion G ⟶ P) ≃ (G ⟶ GrpCat.of P) where
  toFun f := eta G ≫ (forget₂ _ _).map f
  invFun f := lift f
  left_inv f := by apply lift_unique; simp
  right_inv f := by simp

set_option backward.isDefEq.respectTransparency false in
/-- The profinite completion is left adjoint to the forgetful functor. -/
noncomputable
/--
Definition of `adjunction` / `adjunction` 的定义

English:
definition adjunction
  signature: : profiniteCompletion ⊣ forget₂ _ _
  body: Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm f g := by
      apply lift_unique
      simp [homEquiv]
  }

中文:
定义 adjunction
  签名: : profiniteCompletion ⊣ forget₂ _ _
  定义体: Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm f g := by
      apply lift_unique
      simp [homEquiv]
  }

Depends on / 依赖: Adjunction, Adjunction.mkOfHomEquiv, homEquiv, homEquiv_naturality_left_symm, lift_unique, mkOfHomEquiv
-/
def adjunction : profiniteCompletion ⊣ forget₂ _ _ :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm f g := by
      apply lift_unique
      simp [homEquiv]
  }

end ProfiniteCompletion

end ProfiniteGrp
