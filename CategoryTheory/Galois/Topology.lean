/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Prorepresentability
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic

/-!

# Topology of fundamental group

In this file we define a natural topology on the automorphism group of a functor
`F : C ⥤ FintypeCat`: It is defined as the subspace topology induced by the natural
embedding of `Aut F` into `∀ X, Aut (F.obj X)` where
`Aut (F.obj X)` carries the discrete topology.

## References

- [Stacks 0BMQ](https://stacks.math.columbia.edu/tag/0BMQ)

-/

@[expose] public section

open Topology

universe u₁ u₂ v₁ v₂ v w

namespace CategoryTheory

namespace PreGaloisCategory

open CategoryTheory.Functor

variable {C : Type u₁} [Category.{u₂} C] (F : C ⥤ FintypeCat.{w})

/--
Definition of `autEmbedding` / `autEmbedding` 的定义

English:
definition autEmbedding
  signature: : Aut F ->* forall X, Aut (F.obj X)
  body: MonoidHom.mk' (fun σ X => σ.app X) (fun _ _ => rfl)

@[simp]

中文:
定义 autEmbedding
  签名: : Aut F ->* 对任意 X, Aut (F.obj X)
  定义体: MonoidHom.mk' (fun σ X => σ.app X) (fun _ _ => rfl)

@[simp]

Depends on / 依赖: MonoidHom, MonoidHom.mk
-/
def autEmbedding : Aut F ->* forall X, Aut (F.obj X) :=
  MonoidHom.mk' (fun σ X => σ.app X) (fun _ _ => rfl)

@[simp]
/--
lemma `autEmbedding_apply` / 引理 `autEmbedding_apply`

English:
lemma autEmbedding_apply
  given: (σ : Aut F) (X : C)
  statement: autEmbedding F σ X = σ.app X
  proof: rfl

中文:
引理 autEmbedding_apply
  条件: (σ : Aut F) (X : C)
  结论: autEmbedding F σ X = σ.app X
  证明: rfl

Depends on / 依赖: HasCoequalizers, hasReflexiveCoequalizers_of_hasCoequalizers
-/
lemma autEmbedding_apply (σ : Aut F) (X : C) : autEmbedding F σ X = σ.app X :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `autEmbedding_injective` / 引理 `autEmbedding_injective`

English:
lemma autEmbedding_injective
  statement: Function.Injective (autEmbedding F)
  proof: by
  intro σ τ h
  ext X x
  have : σ.app X = τ.app X := congr_fun h X
  rw [← Iso.app_hom]; rw [← Iso.app_hom]; rw [this]

中文:
引理 autEmbedding_injective
  结论: 函数.单射 (autEmbedding F)
  证明: by
  intro σ τ h
  ext X x
  have : σ.app X = τ.app X := congr_fun h X
  rw [← Iso.app_hom]; rw [← Iso.app_hom]; rw [this]

Depends on / 依赖: HasEqualizers, Iso.app_hom, app_hom, congr_fun, hasCoreflexiveEqualizers_of_hasEqualizers
-/
lemma autEmbedding_injective : Function.Injective (autEmbedding F) := by
  intro σ τ h
  ext X x
  have : σ.app X = τ.app X := congr_fun h X
  rw [← Iso.app_hom]; rw [← Iso.app_hom]; rw [this]

/-- We put the discrete topology on `F.obj X`. -/
scoped instance (X : C) : TopologicalSpace (F.obj X) := ⊥

@[scoped instance]
/--
lemma `obj_discreteTopology` / 引理 `obj_discreteTopology`

English:
lemma obj_discreteTopology
  given: (X : C)
  statement: DiscreteTopology (F.obj X)
  proof: ⟨rfl⟩

中文:
引理 obj_discreteTopology
  条件: (X : C)
  结论: 离散拓扑 (F.obj X)
  证明: ⟨rfl⟩
-/
lemma obj_discreteTopology (X : C) : DiscreteTopology (F.obj X) := ⟨rfl⟩

/-- We put the discrete topology on `Aut (F.obj X)`. -/
scoped instance (X : C) : TopologicalSpace (Aut (F.obj X)) := ⊥

/-- We give `F.obj X ⟶ F.obj Y` the product topology. -/
@[local simp]
scoped instance {X Y : C} : TopologicalSpace (F.obj X ⟶ F.obj Y) :=
  .coinduced (fun f => ObjectProperty.homMk (↾f)) inferInstance

scoped instance {X Y : C} : DiscreteTopology (F.obj X ⟶ F.obj Y) :=
  ⟨by simp [DiscreteTopology.eq_bot]⟩

@[scoped instance]
/--
lemma `aut_discreteTopology` / 引理 `aut_discreteTopology`

English:
lemma aut_discreteTopology
  given: (X : C)
  statement: DiscreteTopology (Aut (F.obj X))
  proof: ⟨rfl⟩

中文:
引理 aut_discreteTopology
  条件: (X : C)
  结论: 离散拓扑 (Aut (F.obj X))
  证明: ⟨rfl⟩
-/
lemma aut_discreteTopology (X : C) : DiscreteTopology (Aut (F.obj X)) := ⟨rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (Aut F)
  body: TopologicalSpace.induced (autEmbedding F) inferInstance

中文:
实例 :
  签名: 拓扑空间 (Aut F)
  定义体: TopologicalSpace.induced (autEmbedding F) inferInstance

Depends on / 依赖: TopologicalSpace, TopologicalSpace.induced, autEmbedding, induced
-/
instance : TopologicalSpace (Aut F) :=
  TopologicalSpace.induced (autEmbedding F) inferInstance

/-lemma autEmbedding_range :
    Set.range (autEmbedding F) =
      ⋂ (f : Arrow C), { a | F.map f.hom ≫ (a f.right).hom = (a f.left).hom ≫ F.map f.hom } := by
  ext a
  simp only [Set.mem_range, id_obj, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun ⟨σ, h⟩ i ↦ h.symm ▸ σ.hom.naturality i.hom, fun h ↦ ?_⟩
  · use NatIso.ofComponents a (fun {X Y} f ↦ h ⟨X, Y, f⟩)
    rfl-/

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `autEmbedding_range` / 引理 `autEmbedding_range`

English:
lemma autEmbedding_range
  proof: by
  ext a
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun ⟨σ, h⟩ i => by cat_disch, fun h => ?_⟩
  exact ⟨NatIso.ofComponents a (fun {X Y} f => by
    ext; simpa using ConcreteCategory.congr_hom (h ⟨X, Y, f⟩) _), rfl⟩

中文:
引理 autEmbedding_range
  证明: by
  ext a
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun ⟨σ, h⟩ i => by cat_disch, fun h => ?_⟩
  exact ⟨NatIso.ofComponents a (fun {X Y} f => by
    ext; simpa using ConcreteCategory.congr_hom (h ⟨X, Y, f⟩) _), rfl⟩

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, NatIso, NatIso.ofComponents, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_range, cat_disch, congr_hom, mem_iInter, mem_ofPred_eq, mem_range, ofComponents
-/
lemma autEmbedding_range :
    Set.range (autEmbedding F) = ⋂ (f : Arrow C), { a | F.map f.hom ≫ (a f.right).hom =
      (a f.left).hom ≫ F.map f.hom } := by
  ext a
  simp only [Set.mem_range, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨fun ⟨σ, h⟩ i => by cat_disch, fun h => ?_⟩
  exact ⟨NatIso.ofComponents a (fun {X Y} f => by
    ext; simpa using ConcreteCategory.congr_hom (h ⟨X, Y, f⟩) _), rfl⟩

/--
lemma `autEmbedding_range_isClosed` / 引理 `autEmbedding_range_isClosed`

English:
lemma autEmbedding_range_isClosed
  statement: IsClosed (Set.range (autEmbedding F))
  proof: by
  rw [autEmbedding_range]
  exact isClosed_iInter (fun f => isClosed_eq (by fun_prop) (by fun_prop))

中文:
引理 autEmbedding_range_isClosed
  结论: 是闭集 (集合.range (autEmbedding F))
  证明: by
  rw [autEmbedding_range]
  exact isClosed_iInter (fun f => isClosed_eq (by fun_prop) (by fun_prop))

Depends on / 依赖: autEmbedding_range, fun_prop, isClosed_eq, isClosed_iInter
-/
lemma autEmbedding_range_isClosed : IsClosed (Set.range (autEmbedding F)) := by
  rw [autEmbedding_range]
  exact isClosed_iInter (fun f => isClosed_eq (by fun_prop) (by fun_prop))

/--
lemma `autEmbedding_isClosedEmbedding` / 引理 `autEmbedding_isClosedEmbedding`

English:
lemma autEmbedding_isClosedEmbedding
  statement: IsClosedEmbedding (autEmbedding F) where
  proof: rfl
  injective := autEmbedding_injective F
  isClosed_range := autEmbedding_range_isClosed F

中文:
引理 autEmbedding_isClosedEmbedding
  结论: 是闭嵌入 (autEmbedding F) where
  证明: rfl
  injective := autEmbedding_injective F
  isClosed_range := autEmbedding_range_isClosed F
-/
lemma autEmbedding_isClosedEmbedding : IsClosedEmbedding (autEmbedding F) where
  eq_induced := rfl
  injective := autEmbedding_injective F
  isClosed_range := autEmbedding_range_isClosed F

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompactSpace (Aut F)
  body: (autEmbedding_isClosedEmbedding F).compactSpace

中文:
实例 :
  签名: 紧空间 (Aut F)
  定义体: (autEmbedding_isClosedEmbedding F).compactSpace

Depends on / 依赖: autEmbedding_isClosedEmbedding, compactSpace
-/
instance : CompactSpace (Aut F) := (autEmbedding_isClosedEmbedding F).compactSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T2Space (Aut F)
  body: T2Space.of_injective_continuous (autEmbedding_injective F) continuous_induced_dom

中文:
实例 :
  签名: T2空间 (Aut F)
  定义体: T2Space.of_injective_continuous (autEmbedding_injective F) continuous_induced_dom

Depends on / 依赖: T2Space, T2Space.of_injective_continuous, autEmbedding_injective, continuous_induced_dom, of_injective_continuous
-/
instance : T2Space (Aut F) :=
  T2Space.of_injective_continuous (autEmbedding_injective F) continuous_induced_dom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TotallyDisconnectedSpace (Aut F)
  body: (autEmbedding_isClosedEmbedding F).isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

中文:
实例 :
  签名: 全不连通空间 (Aut F)
  定义体: (autEmbedding_isClosedEmbedding F).isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

Depends on / 依赖: autEmbedding_isClosedEmbedding, isEmbedding, isEmbedding.isTotallyDisconnected_range.mp, isTotallyDisconnected_of_totallyDisconnectedSpace, isTotallyDisconnected_range
-/
instance : TotallyDisconnectedSpace (Aut F) :=
  (autEmbedding_isClosedEmbedding F).isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousMul (Aut F)
  body: (autEmbedding_isClosedEmbedding F).isInducing.continuousMul (autEmbedding F)

中文:
实例 :
  签名: 连续乘法 (Aut F)
  定义体: (autEmbedding_isClosedEmbedding F).isInducing.continuousMul (autEmbedding F)

Depends on / 依赖: StructuredArrow, StructuredArrow.mk, autEmbedding, autEmbedding_isClosedEmbedding, continuousMul, isInducing, isInducing.continuousMul
-/
instance : ContinuousMul (Aut F) :=
  (autEmbedding_isClosedEmbedding F).isInducing.continuousMul (autEmbedding F)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousInv (Aut F)
  body: (autEmbedding_isClosedEmbedding F).isInducing.continuousInv fun _ => rfl

中文:
实例 :
  签名: 连续取逆 (Aut F)
  定义体: (autEmbedding_isClosedEmbedding F).isInducing.continuousInv fun _ => rfl

Depends on / 依赖: IsConnected, IsConnected.of_induct, StructuredArrow, StructuredArrow.homMk, StructuredArrow.mk, autEmbedding_isClosedEmbedding, continuousInv, isInducing, isInducing.continuousInv, of_induct
-/
instance : ContinuousInv (Aut F) :=
  (autEmbedding_isClosedEmbedding F).isInducing.continuousInv fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsTopologicalGroup (Aut F)
  body: ⟨⟩

中文:
实例 :
  签名: 是拓扑群 (Aut F)
  定义体: ⟨⟩
-/
instance : IsTopologicalGroup (Aut F) := ⟨⟩

instance (X : C) : SMul (Aut (F.obj X)) (F.obj X) := ⟨fun σ a => σ.hom a⟩

instance (X : C) : ContinuousSMul (Aut (F.obj X)) (F.obj X) := by
  constructor
  fun_prop

/--
Instance `continuousSMul_aut_fiber` / 实例 `continuousSMul_aut_fiber`

English:
instance continuousSMul_aut_fiber
  signature: (X : C)
  body: by
    let g : Aut (F.obj X) × F.obj X -> F.obj X := fun ⟨σ, x⟩ => σ.hom x
    let h (q : Aut F × F.obj X) : Aut (F.obj X) × F.obj X :=
      ⟨((fun p => p X) ∘ autEmbedding F) q.1, q.2⟩
    change Continuous (g ∘ h)
    fun_prop

中文:
实例 continuousSMul_aut_fiber
  签名: (X : C)
  定义体: by
    let g : Aut (F.obj X) × F.obj X -> F.obj X := fun ⟨σ, x⟩ => σ.hom x
    let h (q : Aut F × F.obj X) : Aut (F.obj X) × F.obj X :=
      ⟨((fun p => p X) ∘ autEmbedding F) q.1, q.2⟩
    change Continuous (g ∘ h)
    fun_prop

Depends on / 依赖: Continuous, F.obj, autEmbedding, fun_prop
-/
instance continuousSMul_aut_fiber (X : C) : ContinuousSMul (Aut F) (F.obj X) where
  continuous_smul := by
    let g : Aut (F.obj X) × F.obj X -> F.obj X := fun ⟨σ, x⟩ => σ.hom x
    let h (q : Aut F × F.obj X) : Aut (F.obj X) × F.obj X :=
      ⟨((fun p => p X) ∘ autEmbedding F) q.1, q.2⟩
    change Continuous (g ∘ h)
    fun_prop

/--
lemma `continuous_mapAut_whiskeringRight` / 引理 `continuous_mapAut_whiskeringRight`

English:
lemma continuous_mapAut_whiskeringRight
  given: (G : FintypeCat.{w} ⥤ FintypeCat.{v})
  proof: by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing]; rw [continuous_pi_iff]
  intro X
  change Continuous fun a => G.mapAut (F.obj X) (autEmbedding F a X)
  fun_prop

中文:
引理 continuous_mapAut_whiskeringRight
  条件: (G : FintypeCat.{w} ⥤ FintypeCat.{v})
  证明: by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing]; rw [continuous_pi_iff]
  intro X
  change Continuous fun a => G.mapAut (F.obj X) (autEmbedding F a X)
  fun_prop

Depends on / 依赖: Continuous, F.obj, G.mapAut, IsInducing, Topology, Topology.IsInducing.continuous_iff, autEmbedding, autEmbedding_isClosedEmbedding, continuous_iff, continuous_pi_iff, fun_prop, isInducing, mapAut
-/
lemma continuous_mapAut_whiskeringRight (G : FintypeCat.{w} ⥤ FintypeCat.{v}) :
    Continuous (((whiskeringRight _ _ _).obj G).mapAut F) := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing]; rw [continuous_pi_iff]
  intro X
  change Continuous fun a => G.mapAut (F.obj X) (autEmbedding F a X)
  fun_prop

/--
Definition of `autEquivAutWhiskerRight` / `autEquivAutWhiskerRight` 的定义

English:
definition autEquivAutWhiskerRight
  signature: {G : FintypeCat.{w} ⥤ FintypeCat.{v}}
  body: (h.whiskeringRight C).autMulEquivOfFullyFaithful F
  continuous_toFun := continuous_mapAut_whiskeringRight F G
  continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := ((h.whiskeringRight C).autMulEquivOfFullyFaithful F).toEquiv)
    (continuous_mapAut_whiskeringRight F G)

中文:
定义 autEquivAutWhiskerRight
  签名: {G : FintypeCat.{w} ⥤ FintypeCat.{v}}
  定义体: (h.whiskeringRight C).autMulEquivOfFullyFaithful F
  continuous_toFun := continuous_mapAut_whiskeringRight F G
  continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := ((h.whiskeringRight C).autMulEquivOfFullyFaithful F).toEquiv)
    (continuous_mapAut_whiskeringRight F G)

Depends on / 依赖: autMulEquivOfFullyFaithful, h.whiskeringRight, whiskeringRight
-/
noncomputable def autEquivAutWhiskerRight {G : FintypeCat.{w} ⥤ FintypeCat.{v}}
    (h : G.FullyFaithful) :
    Aut F ≃ₜ* Aut (F ⋙ G) where
  __ := (h.whiskeringRight C).autMulEquivOfFullyFaithful F
  continuous_toFun := continuous_mapAut_whiskeringRight F G
  continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2
    (f := ((h.whiskeringRight C).autMulEquivOfFullyFaithful F).toEquiv)
    (continuous_mapAut_whiskeringRight F G)

variable [GaloisCategory C] [FiberFunctor F]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_set_ker_evaluation_subset_of_isOpen` / 引理 `exists_set_ker_evaluation_subset_of_isOpen`

English:
lemma exists_set_ker_evaluation_subset_of_isOpen
  proof: by
  obtain ⟨U, hUopen, rfl⟩ := isOpen_induced_iff.mp h
  obtain ⟨I, u, ho, ha⟩ := isOpen_pi_iff.mp hUopen 1 h1
  choose fι ff fc h4 h5 h6 using (fun X : I => has_decomp_connected_components X.val)
  refine ⟨⋃ X, Set.range (ff X), Fintype.ofFinite _, ?_, ?_⟩
  · rintro X ⟨A, ⟨Y, rfl⟩, hA2⟩
    obtai

中文:
引理 存在_set_ker_evaluation_subset_of_isOpen
  证明: by
  obtain ⟨U, hUopen, rfl⟩ := isOpen_induced_iff.mp h
  obtain ⟨I, u, ho, ha⟩ := isOpen_pi_iff.mp hUopen 1 h1
  choose fι ff fc h4 h5 h6 using (fun X : I => has_decomp_connected_components X.val)
  refine ⟨⋃ X, Set.range (ff X), Fintype.ofFinite _, ?_, ?_⟩
  · rintro X ⟨A, ⟨Y, rfl⟩, hA2⟩
    obtai

Depends on / 依赖: F.obj, Fintype, Fintype.ofFinite, Set.range, X.val, autEmbedding, hUopen, has_decomp_connected_components, hom.app, isOpen_induced_iff, isOpen_induced_iff.mp, isOpen_pi_iff, isOpen_pi_iff.mp, ofFinite
-/
lemma exists_set_ker_evaluation_subset_of_isOpen
    {H : Set (Aut F)} (h1 : 1 in H) (h : IsOpen H) :
    exists (I : Set C) (_ : Fintype I), (forall X in I, IsConnected X) ∧
      (forall σ : Aut F, (forall X : I, σ.hom.app X = 𝟙 (F.obj X)) -> σ in H) := by
  obtain ⟨U, hUopen, rfl⟩ := isOpen_induced_iff.mp h
  obtain ⟨I, u, ho, ha⟩ := isOpen_pi_iff.mp hUopen 1 h1
  choose fι ff fc h4 h5 h6 using (fun X : I => has_decomp_connected_components X.val)
  refine ⟨⋃ X, Set.range (ff X), Fintype.ofFinite _, ?_, ?_⟩
  · rintro X ⟨A, ⟨Y, rfl⟩, hA2⟩
    obtain ⟨i, rfl⟩ := hA2
    exact h5 Y i
  · refine fun σ h => ha (fun X XinI => ?_)
    suffices h : autEmbedding F σ X = 1 by
      rw [h]
      exact (ho X XinI).right
    have h : σ.hom.app X = 𝟙 (F.obj X) := by
      have : Fintype (fι ⟨X, XinI⟩) := Fintype.ofFinite _
      ext x
      obtain ⟨⟨j⟩, a, ha : F.map _ a = x⟩ := Limits.FintypeCat.jointly_surjective
        (Discrete.functor (ff ⟨X, XinI⟩) ⋙ F) _ (Limits.isColimitOfPreserves F (h4 ⟨X, XinI⟩)) x
      rw [FintypeCat.id_apply]; rw [← ha]; rw [NatTrans.naturality_apply]
      simp [h ⟨(ff _) j, ⟨Set.range (ff ⟨X, XinI⟩), ⟨⟨_, rfl⟩, ⟨j, rfl⟩⟩⟩⟩]
    exact Iso.ext h

open Limits

/--
lemma `nhds_one_has_basis_stabilizers` / 引理 `nhds_one_has_basis_stabilizers`

English:
lemma nhds_one_has_basis_stabilizers
  statement: (nhds (1 : Aut F)).HasBasis (fun _ => True)
  proof: by
    rw [mem_nhds_iff]
    refine ⟨?_, ?_⟩
    · intro ⟨U, hU, hUopen, hUone⟩
      obtain ⟨I, _, hc, hmem⟩ := exists_set_ker_evaluation_subset_of_isOpen F hUone hUopen
      let P : C := ∏ᶜ fun X : I => X.val
      obtain ⟨A, a, hgal, hbij⟩ := exists_galois_representative F P
      refine ⟨⟨A, a,

中文:
引理 nhds_one_has_basis_stabilizers
  结论: (邻域滤子 (1 : Aut F)).有基 (fun _ => 真)
  证明: by
    rw [mem_nhds_iff]
    refine ⟨?_, ?_⟩
    · intro ⟨U, hU, hUopen, hUone⟩
      obtain ⟨I, _, hc, hmem⟩ := exists_set_ker_evaluation_subset_of_isOpen F hUone hUopen
      let P : C := ∏ᶜ fun X : I => X.val
      obtain ⟨A, a, hgal, hbij⟩ := exists_galois_representative F P
      refine ⟨⟨A, a,

Depends on / 依赖: F.obj, Fintyp, IsConnected, Nonempty, X.property, X.val, exists_galois_representative, exists_set_ker_evaluation_subset_of_isOpen, hUopen, mem_nhds_iff, nonempty_fiber_of_isConnected, property, t.hom.app
-/
lemma nhds_one_has_basis_stabilizers : (nhds (1 : Aut F)).HasBasis (fun _ => True)
    (fun X : PointedGaloisObject F => MulAction.stabilizer (Aut F) X.pt) where
  mem_iff' S := by
    rw [mem_nhds_iff]
    refine ⟨?_, ?_⟩
    · intro ⟨U, hU, hUopen, hUone⟩
      obtain ⟨I, _, hc, hmem⟩ := exists_set_ker_evaluation_subset_of_isOpen F hUone hUopen
      let P : C := ∏ᶜ fun X : I => X.val
      obtain ⟨A, a, hgal, hbij⟩ := exists_galois_representative F P
      refine ⟨⟨A, a, hgal⟩, trivial, ?_⟩
      intro t (ht : t.hom.app A a = a)
      apply hU
      apply hmem
      have (X : I) : IsConnected X.val := hc X.val X.property
      have (X : I) : Nonempty (F.obj X.val) := nonempty_fiber_of_isConnected F X
      intro X
      ext x
      simp only [FintypeCat.id_apply]
      obtain ⟨z, rfl⟩ :=
        surjective_of_nonempty_fiber_of_isConnected F (Pi.π (fun X : I => X.val) X) x
      obtain ⟨f, rfl⟩ := hbij.surjective z
      rw [NatTrans.naturality_apply]; rw [NatTrans.naturality_apply]; rw [ht]
    · intro ⟨X, _, h⟩
      exact ⟨MulAction.stabilizer (Aut F) X.pt, h, stabilizer_isOpen (Aut F) X.pt,
        Subgroup.one_mem _⟩

end PreGaloisCategory

end CategoryTheory
