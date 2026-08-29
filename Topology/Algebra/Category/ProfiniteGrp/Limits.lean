/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Youle Fang, Jujian Zhang, Yuyang Zhao
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# A profinite group is the projective limit of finite groups

We define the topological group isomorphism between a profinite group and the projective limit of
its quotients by open normal subgroups.

## Main definitions

* `toFiniteQuotientFunctor` : The functor from `OpenNormalSubgroup P` to `FiniteGrp`
  sending an open normal subgroup `U` to `P ⧸ U`, where `P : ProfiniteGrp`.

* `toLimit` : The continuous homomorphism from a profinite group `P` to
  the projective limit of its quotients by open normal subgroups ordered by inclusion.

* `ContinuousMulEquivLimittoFiniteQuotientFunctor` : The `toLimit` is a
  `ContinuousMulEquiv`

## Main Statements

* `OpenNormalSubgroupSubClopenNhdsOfOne` : For any open neighborhood of `1` there is an
  open normal subgroup contained in it.

-/

@[expose] public section

universe u

open CategoryTheory IsTopologicalGroup

namespace ProfiniteGrp

/-- The functor from `OpenNormalSubgroup P` to `FiniteGrp` sending `U` to `P ⧸ U`,
where `P : ProfiniteGrp`. -/
@[to_additive /-- The functor from `OpenNormalAddSubgroup P` to `FiniteAddGrp` sending `U` to
`P ⧸ U`, where `P : ProfiniteAddGrp`. -/]
/--
Definition of `toFiniteQuotientFunctor` / `toFiniteQuotientFunctor` 的定义

English:
definition toFiniteQuotientFunctor
  signature: (P : ProfiniteGrp)
  body: fun H => FiniteGrp.of (P ⧸ H.toSubgroup)
  map := fun fHK => FiniteGrp.ofHom (QuotientGroup.map _ _ (.id _) (leOfHom fHK))
map_id _ := ConcreteCategory.ext QuotientGroup.map_id _
map_comp f g := ConcreteCategory.ext (QuotientGroup.map_comp_map
    _ _ _ (.id _) (.id _) (leOfHom f) (leOfHom g)).symm

中文:
定义 toFiniteQuotientFunctor
  签名: (P : ProfiniteGrp)
  定义体: fun H => FiniteGrp.of (P ⧸ H.toSubgroup)
  map := fun fHK => FiniteGrp.ofHom (QuotientGroup.map _ _ (.id _) (leOfHom fHK))
map_id _ := ConcreteCategory.ext QuotientGroup.map_id _
map_comp f g := ConcreteCategory.ext (QuotientGroup.map_comp_map
    _ _ _ (.id _) (.id _) (leOfHom f) (leOfHom g)).symm

Depends on / 依赖: FiniteGrp, FiniteGrp.of, H.toSubgroup, toSubgroup
-/
def toFiniteQuotientFunctor (P : ProfiniteGrp) : OpenNormalSubgroup P ⥤ FiniteGrp where
  obj := fun H => FiniteGrp.of (P ⧸ H.toSubgroup)
  map := fun fHK => FiniteGrp.ofHom (QuotientGroup.map _ _ (.id _) (leOfHom fHK))
map_id _ := ConcreteCategory.ext QuotientGroup.map_id _
map_comp f g := ConcreteCategory.ext (QuotientGroup.map_comp_map
    _ _ _ (.id _) (.id _) (leOfHom f) (leOfHom g)).symm

/-- The diagram of finite quotients of `P` viewed in `ProfiniteGrp`. -/
@[to_additive (attr := simps! obj map)
/-- The diagram of finite quotients of `P` viewed in `ProfiniteAddGrp`. -/]
/--
Definition of `diagram` / `diagram` 的定义

English:
definition diagram
  signature: (P : ProfiniteGrp.{u})
  body: toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp

中文:
定义 diagram
  签名: (P : ProfiniteGrp.{u})
  定义体: toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp

Depends on / 依赖: FiniteGrp, ProfiniteGrp, toFiniteQuotientFunctor
-/
def diagram (P : ProfiniteGrp.{u}) : OpenNormalSubgroup P ⥤ ProfiniteGrp.{u} :=
  toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp

/-- The `MonoidHom` from a profinite group `P` to the projective limit of its quotients by
open normal subgroups ordered by inclusion -/
@[to_additive /-- The `AddMonoidHom` from a profinite additive group `P` to the projective limit of
its quotients by open normal subgroups ordered by inclusion -/]
/--
Definition of `toLimitFun` / `toLimitFun` 的定义

English:
definition toLimitFun
  signature: (P : ProfiniteGrp.{u})
  body: ⟨fun _ => QuotientGroup.mk p, fun _ => fun _ _ => rfl⟩
  map_one' := Subtype.val_inj.mp rfl
  map_mul' _ _ := Subtype.val_inj.mp rfl

中文:
定义 toLimitFun
  签名: (P : ProfiniteGrp.{u})
  定义体: ⟨fun _ => QuotientGroup.mk p, fun _ => fun _ _ => rfl⟩
  map_one' := Subtype.val_inj.mp rfl
  map_mul' _ _ := Subtype.val_inj.mp rfl

Depends on / 依赖: QuotientGroup, QuotientGroup.mk
-/
def toLimitFun (P : ProfiniteGrp.{u}) : P ->* limit (diagram P) where
  toFun p := ⟨fun _ => QuotientGroup.mk p, fun _ => fun _ _ => rfl⟩
  map_one' := Subtype.val_inj.mp rfl
  map_mul' _ _ := Subtype.val_inj.mp rfl

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
lemma `toLimitFun_continuous` / 引理 `toLimitFun_continuous`

English:
lemma toLimitFun_continuous
  given: (P : ProfiniteGrp.{u})
  statement: Continuous (toLimitFun P)
  proof: by
  apply continuous_induced_rng.mpr (continuous_pi _)
  intro H
  dsimp only [Functor.comp_obj, CompHausLike.coe_of, Functor.comp_map,
    CompHausLike.toCompHausLike_map, CompHausLike.compHausLikeToTop_map, Set.mem_ofPred_eq,
    toLimitFun, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  apply Continuous.mk
  intro s _
  rw [← (Set.biUnion_preimage_singleton QuotientGroup.mk s)]
  refine isOpen_iUnion (fun i => isOpen_iUnion (fun _ => ?_))
  convert! IsOpen.leftCoset H.toOpenSubgroup.isOpen' (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
  exact Iff.symm (Set.mem_smul_set_iff_inv_smul_mem)

中文:
引理 toLimitFun_continuous
  条件: (P : ProfiniteGrp.{u})
  结论: 连续 (toLimitFun P)
  证明: by
  apply continuous_induced_rng.mpr (continuous_pi _)
  intro H
  dsimp only [Functor.comp_obj, CompHausLike.coe_of, Functor.comp_map,
    CompHausLike.toCompHausLike_map, CompHausLike.compHausLikeToTop_map, Set.mem_ofPred_eq,
    toLimitFun, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  apply Continuous.mk
  intro s _
  rw [← (Set.biUnion_preimage_singleton QuotientGroup.mk s)]
  refine isOpen_iUnion (fun i => isOpen_iUnion (fun _ => ?_))
  convert! IsOpen.leftCoset H.toOpenSubgroup.isOpen' (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
  exact Iff.symm (Set.mem_smul_set_iff_inv_smul_mem)

Depends on / 依赖: CompHausLike, CompHausLike.coe_of, CompHausLike.compHausLikeToTop_map, CompHausLike.toCompHausLike_map, Continuous, Continuous.mk, Function, Function.comp_apply, Functor, Functor.comp_map, Functor.comp_obj, H.toOpenSubgroup.isOpen, IsOpen, IsOpen.leftCoset, MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, Quotient, Quotient.out
-/
lemma toLimitFun_continuous (P : ProfiniteGrp.{u}) : Continuous (toLimitFun P) := by
  apply continuous_induced_rng.mpr (continuous_pi _)
  intro H
  dsimp only [Functor.comp_obj, CompHausLike.coe_of, Functor.comp_map,
    CompHausLike.toCompHausLike_map, CompHausLike.compHausLikeToTop_map, Set.mem_ofPred_eq,
    toLimitFun, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]
  apply Continuous.mk
  intro s _
  rw [← (Set.biUnion_preimage_singleton QuotientGroup.mk s)]
  refine isOpen_iUnion (fun i => isOpen_iUnion (fun _ => ?_))
  convert! IsOpen.leftCoset H.toOpenSubgroup.isOpen' (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
  exact Iff.symm (Set.mem_smul_set_iff_inv_smul_mem)

/-- The morphism in the category of `ProfiniteGrp` from a profinite group `P` to
the projective limit of its quotients by open normal subgroups ordered by inclusion -/
@[to_additive /-- The morphism in the category of `ProfiniteAddGrp` from a profinite additive group
`P` to the projective limit of its quotients by open normal subgroups ordered by inclusion -/]
/--
Definition of `toLimit` / `toLimit` 的定义

English:
definition toLimit
  signature: (P : ProfiniteGrp.{u})
  body: ofHom { toLimitFun P with
  continuous_toFun := toLimitFun_continuous P }

中文:
定义 toLimit
  签名: (P : ProfiniteGrp.{u})
  定义体: ofHom { toLimitFun P with
  continuous_toFun := toLimitFun_continuous P }

Depends on / 依赖: continuous_toFun, toLimitFun, toLimitFun_continuous
-/
def toLimit (P : ProfiniteGrp.{u}) : P ⟶ limit (diagram P) :=
  ofHom { toLimitFun P with
  continuous_toFun := toLimitFun_continuous P }

/--
theorem `denseRange_toLimit` / 定理 `denseRange_toLimit`

English:
theorem denseRange_toLimit
  given: (P : ProfiniteGrp.{u})
  statement: DenseRange (toLimit P)
  proof: by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  simp_rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M := iInf (fun (j : J) => j.1.1.1)
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => j.1.isNormal'
  have hMOpen : IsOpen (M : Set P) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
  let m : OpenNormalSubgroup P := { M with isOpen' := hMOpen }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use (toLimit P) origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => j.1.1.1) ⟨a, a_in_J⟩).hom
  rw [← (P.toLimit origin).property M_to_Na]
  change (P.toFiniteQuotientFunctor.map M_to_Na) (QuotientGroup.mk' M origin) in _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

中文:
定理 denseRange_toLimit
  条件: (P : ProfiniteGrp.{u})
  结论: DenseRange (toLimit P)
  证明: by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  simp_rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M := iInf (fun (j : J) => j.1.1.1)
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => j.1.isNormal'
  have hMOpen : IsOpen (M : Set P) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
  let m : OpenNormalSubgroup P := { M with isOpen' := hMOpen }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use (toLimit P) origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => j.1.1.1) ⟨a, a_in_J⟩).hom
  rw [← (P.toLimit origin).property M_to_Na]
  change (P.toFiniteQuotientFunctor.map M_to_Na) (QuotientGroup.mk' M origin) in _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

Depends on / 依赖: IsOpen, M.Normal, Normal, OpenNormalSubgroup, Set.mem_preimage, Subgroup, Subgroup.coe_iInf, Subgroup.normal_iInf_normal, coe_iInf, dense_iff_inter_open, dense_iff_inter_open.mpr, hMOpen, isNormal, isOpen, isOpen_iInter_of_finite, isOpen_pi_iff, isOpen_pi_iff.mp, mem_preimage, normal_iInf_normal, simp_rw
-/
theorem denseRange_toLimit (P : ProfiniteGrp.{u}) : DenseRange (toLimit P) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  simp_rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M := iInf (fun (j : J) => j.1.1.1)
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => j.1.isNormal'
  have hMOpen : IsOpen (M : Set P) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
  let m : OpenNormalSubgroup P := { M with isOpen' := hMOpen }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use (toLimit P) origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => j.1.1.1) ⟨a, a_in_J⟩).hom
  rw [← (P.toLimit origin).property M_to_Na]
  change (P.toFiniteQuotientFunctor.map M_to_Na) (QuotientGroup.mk' M origin) in _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

/--
theorem `toLimit_surjective` / 定理 `toLimit_surjective`

English:
theorem toLimit_surjective
  given: (P : ProfiniteGrp.{u})
  statement: Function.Surjective (toLimit P)
  proof: by
  have : IsClosed (Set.range P.toLimit) :=
    P.toLimit.hom.continuous_toFun.isClosedMap.isClosed_range
  rw [← Set.range_eq_univ]; rw [← closure_eq_iff_isClosed.mpr this]; rw [Dense.closure_eq (denseRange_toLimit P)]

@[to_additive]

中文:
定理 toLimit_surjective
  条件: (P : ProfiniteGrp.{u})
  结论: 函数.满射 (toLimit P)
  证明: by
  have : IsClosed (Set.range P.toLimit) :=
    P.toLimit.hom.continuous_toFun.isClosedMap.isClosed_range
  rw [← Set.range_eq_univ]; rw [← closure_eq_iff_isClosed.mpr this]; rw [Dense.closure_eq (denseRange_toLimit P)]

@[to_additive]

Depends on / 依赖: Dense.closure_eq, IsClosed, P.toLimit, P.toLimit.hom.continuous_toFun.isClosedMap.isClosed_range, Set.range, Set.range_eq_univ, closure_eq, closure_eq_iff_isClosed, closure_eq_iff_isClosed.mpr, continuous_toFun, denseRange_toLimit, isClosedMap, isClosed_range, range_eq_univ, toLimit
-/
theorem toLimit_surjective (P : ProfiniteGrp.{u}) : Function.Surjective (toLimit P) := by
  have : IsClosed (Set.range P.toLimit) :=
    P.toLimit.hom.continuous_toFun.isClosedMap.isClosed_range
  rw [← Set.range_eq_univ]; rw [← closure_eq_iff_isClosed.mpr this]; rw [Dense.closure_eq (denseRange_toLimit P)]

@[to_additive]
/--
theorem `toLimit_injective` / 定理 `toLimit_injective`

English:
theorem toLimit_injective
  given: (P : ProfiniteGrp.{u})
  statement: Function.Injective (toLimit P)
  proof: by
  change Function.Injective (toLimit P).hom.toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff]; rw [Subgroup.eq_bot_iff_forall]
  intro x h
  by_contra xne1
  rcases exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_compl_singleton)
    (Set.mem_compl_singleton_iff.mpr fun a => xne1 a.symm) with ⟨H, hH⟩
  exact hH ((QuotientGroup.eq_one_iff x).mp (congrFun (Subtype.val_inj.mpr h) H)) rfl

中文:
定理 toLimit_injective
  条件: (P : ProfiniteGrp.{u})
  结论: 函数.单射 (toLimit P)
  证明: by
  change Function.Injective (toLimit P).hom.toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff]; rw [Subgroup.eq_bot_iff_forall]
  intro x h
  by_contra xne1
  rcases exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_compl_singleton)
    (Set.mem_compl_singleton_iff.mpr fun a => xne1 a.symm) with ⟨H, hH⟩
  exact hH ((QuotientGroup.eq_one_iff x).mp (congrFun (Subtype.val_inj.mpr h) H)) rfl

Depends on / 依赖: Function, Function.Injective, Injective, MonoidHom, MonoidHom.ker_eq_bot_iff, QuotientGroup, QuotientGroup.eq_one_iff, Set.mem_compl_singleton_iff.mpr, Subgroup, Subgroup.eq_bot_iff_forall, Subtype, Subtype.val_inj.mpr, a.symm, eq_bot_iff_forall, eq_one_iff, exist_openNormalSubgroup_sub_open_nhds_of_one, hom.toMonoidHom, isOpen_compl_singleton, ker_eq_bot_iff, mem_compl_singleton_iff
-/
theorem toLimit_injective (P : ProfiniteGrp.{u}) : Function.Injective (toLimit P) := by
  change Function.Injective (toLimit P).hom.toMonoidHom
  rw [← MonoidHom.ker_eq_bot_iff]; rw [Subgroup.eq_bot_iff_forall]
  intro x h
  by_contra xne1
  rcases exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_compl_singleton)
    (Set.mem_compl_singleton_iff.mpr fun a => xne1 a.symm) with ⟨H, hH⟩
  exact hH ((QuotientGroup.eq_one_iff x).mp (congrFun (Subtype.val_inj.mpr h) H)) rfl

/--
Definition of `continuousMulEquivLimittoFiniteQuotientFunctor` / `continuousMulEquivLimittoFiniteQuotientFunctor` 的定义

English:
definition continuousMulEquivLimittoFiniteQuotientFunctor
  signature: (P : ProfiniteGrp.{u})
  body: {
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨toLimit_injective P, toLimit_surjective P⟩)
    P.toLimit.hom.continuous_toFun) with
  map_mul' := (toLimit P).hom.map_mul' }

中文:
定义 continuousMulEquivLimittoFiniteQuotientFunctor
  签名: (P : ProfiniteGrp.{u})
  定义体: {
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨toLimit_injective P, toLimit_surjective P⟩)
    P.toLimit.hom.continuous_toFun) with
  map_mul' := (toLimit P).hom.map_mul' }
-/
noncomputable def continuousMulEquivLimittoFiniteQuotientFunctor (P : ProfiniteGrp.{u}) :
    P ≃ₜ* (limit <| diagram P) := {
  (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ ⟨toLimit_injective P, toLimit_surjective P⟩)
    P.toLimit.hom.continuous_toFun) with
  map_mul' := (toLimit P).hom.map_mul' }

/--
Instance `isIso_toLimit` / 实例 `isIso_toLimit`

English:
instance isIso_toLimit
  signature: (P : ProfiniteGrp.{u})
  body: by
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  exact ⟨toLimit_injective P, toLimit_surjective P⟩

中文:
实例 isIso_toLimit
  签名: (P : ProfiniteGrp.{u})
  定义体: by
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  exact ⟨toLimit_injective P, toLimit_surjective P⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.ConcreteCategory.isIso_iff_bijective, ConcreteCategory, isIso_iff_bijective, toLimit_injective, toLimit_surjective
-/
instance isIso_toLimit (P : ProfiniteGrp.{u}) : IsIso (toLimit P) := by
  rw [CategoryTheory.ConcreteCategory.isIso_iff_bijective]
  exact ⟨toLimit_injective P, toLimit_surjective P⟩

/--
Definition of `isoLimittoFiniteQuotientFunctor` / `isoLimittoFiniteQuotientFunctor` 的定义

English:
definition isoLimittoFiniteQuotientFunctor
  signature: (P : ProfiniteGrp.{u})
  body: ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivLimittoFiniteQuotientFunctor P)

中文:
定义 isoLimittoFiniteQuotientFunctor
  签名: (P : ProfiniteGrp.{u})
  定义体: ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivLimittoFiniteQuotientFunctor P)

Depends on / 依赖: ContinuousMulEquiv, ContinuousMulEquiv.toProfiniteGrpIso, continuousMulEquivLimittoFiniteQuotientFunctor, toProfiniteGrpIso
-/
noncomputable def isoLimittoFiniteQuotientFunctor (P : ProfiniteGrp.{u}) :
    P ≅ (limit <| diagram P) :=
  ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivLimittoFiniteQuotientFunctor P)

set_option backward.isDefEq.respectTransparency.types false in
/-- The projection from `P` to the quotient by an open normal subgroup. -/
@[to_additive /-- The projection from `P` to the quotient by an open normal subgroup. -/]
/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: {P : ProfiniteGrp.{u}} (U : OpenNormalSubgroup P)
  body: ProfiniteGrp.ofHom (Y := (diagram P).obj U) {
    toFun := QuotientGroup.mk
    map_one' := rfl
    map_mul' _ _ := rfl
    continuous_toFun := show Continuous ((limitCone <| diagram P).π.app U ∘ toLimit P) by
      fun_prop
  }

中文:
定义 proj
  签名: {P : ProfiniteGrp.{u}} (U : OpenNormal子群 P)
  定义体: ProfiniteGrp.ofHom (Y := (diagram P).obj U) {
    toFun := QuotientGroup.mk
    map_one' := rfl
    map_mul' _ _ := rfl
    continuous_toFun := show Continuous ((limitCone <| diagram P).π.app U ∘ toLimit P) by
      fun_prop
  }

Depends on / 依赖: Continuous, ProfiniteGrp, ProfiniteGrp.ofHom, QuotientGroup, QuotientGroup.mk, continuous_toFun, diagram, fun_prop, limitCone, map_mul, map_one, toLimit
-/
def proj {P : ProfiniteGrp.{u}} (U : OpenNormalSubgroup P) : P ⟶ (diagram P).obj U :=
  ProfiniteGrp.ofHom (Y := (diagram P).obj U) {
    toFun := QuotientGroup.mk
    map_one' := rfl
    map_mul' _ _ := rfl
    continuous_toFun := show Continuous ((limitCone <| diagram P).π.app U ∘ toLimit P) by
      fun_prop
  }

set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical cone over `diagram P` with point `P`. -/
@[to_additive (attr := simps) /-- The canonical cone over `diagram P` with point `P`. -/]
/--
Definition of `cone` / `cone` 的定义

English:
definition cone
  signature: (P : ProfiniteGrp.{u})
  body: P
  π := { app := proj }

中文:
定义 cone
  签名: (P : ProfiniteGrp.{u})
  定义体: P
  π := { app := proj }
-/
def cone (P : ProfiniteGrp.{u}) : Limits.Cone (diagram P) where
  pt := P
  π := { app := proj }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isLimitCone` / `isLimitCone` 的定义

English:
definition isLimitCone
  signature: (P : ProfiniteGrp.{u})
  body: Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) .symm
    Limits.Cone.ext (isoLimittoFiniteQuotientFunctor _) fun _ => rfl

中文:
定义 isLimitCone
  签名: (P : ProfiniteGrp.{u})
  定义体: Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) .symm
    Limits.Cone.ext (isoLimittoFiniteQuotientFunctor _) fun _ => rfl

Depends on / 依赖: IsLimit, Limits, Limits.Cone.ext, Limits.IsLimit.ofIsoLimit, isoLimittoFiniteQuotientFunctor, limitConeIsLimit, ofIsoLimit
-/
noncomputable def isLimitCone (P : ProfiniteGrp.{u}) : Limits.IsLimit P.cone :=
Limits.IsLimit.ofIsoLimit (limitConeIsLimit _) .symm
    Limits.Cone.ext (isoLimittoFiniteQuotientFunctor _) fun _ => rfl

end ProfiniteGrp
