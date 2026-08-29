/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yuyang Zhao, Jujian Zhang
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!

# Galois Group as a profinite group

In this file, we prove that given a field extension `K/k`, there is a continuous isomorphism between
`Gal(K/k)` and the limit of `Gal(L/k)`, where `L` is a finite Galois intermediate field ordered by
inverse inclusion, thus making `Gal(K/k)` profinite as a limit of finite groups.

## Main definitions and results

In a field extension `K/k`

* `finGaloisGroup L` : The (finite) Galois group `Gal(L/k)` associated to a
  `L : FiniteGaloisIntermediateField k K` `L`.

* `finGaloisGroupMap` : For `FiniteGaloisIntermediateField` s `L₁` and `L₂` with `L₂ ≤ L₁`
  giving the restriction of `Gal(L₁/k)` to `Gal(L₂/k)`

* `finGaloisGroupFunctor` : The functor from `FiniteGaloisIntermediateField`
  (ordered by reverse inclusion) to `FiniteGrp`, mapping each `FiniteGaloisIntermediateField L`
  to `Gal (L/k)`.

* `InfiniteGalois.algEquivToLimit` : The homomorphism from `Gal(K/k)` to
  `limit (asProfiniteGaloisGroupFunctor k K)`, induced by the projections from `Gal(K/k)` to
  any `Gal(L/k)` where `L` is a `FiniteGaloisIntermediateField`.

* `InfiniteGalois.limitToAlgEquiv` : The inverse of `InfiniteGalois.algEquivToLimit`, in which
  the elements of `Gal(K/k)` are constructed pointwise.

* `InfiniteGalois.mulEquivToLimit` : The mulEquiv obtained from combining the above two.

* `InfiniteGalois.mulEquivToLimit_continuous` : The inverse of `InfiniteGalois.mulEquivToLimit`
  is continuous.

* `InfiniteGalois.continuousMulEquivToLimit` ：The `ContinuousMulEquiv` between `Gal(K/k)` and
  `limit (asProfiniteGaloisGroupFunctor k K)` given by `InfiniteGalois.mulEquivToLimit`

* `InfiniteGalois.ProfiniteGalGrp` : `Gal(K/k)` as a profinite group as there is
  a `ContinuousMulEquiv` to a `ProfiniteGrp` given above.

* `InfiniteGalois.restrictNormalHomContinuous` : Any `restrictNormalHom` is continuous.

-/

@[expose] public section

open CategoryTheory Opposite

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Profinite

/--
Definition of `FiniteGaloisIntermediateField.finGaloisGroup` / `FiniteGaloisIntermediateField.finGaloisGroup` 的定义

English:
definition FiniteGaloisIntermediateField.finGaloisGroup
  signature: (L : FiniteGaloisIntermediateField k K)
  body: letI := AlgEquiv.fintype k L
  FiniteGrp.of Gal(L/k)

中文:
定义 有限Galois中间域.finGaloisGroup
  签名: (L : 有限Galois中间域 k K)
  定义体: letI := AlgEquiv.fintype k L
  FiniteGrp.of Gal(L/k)

Depends on / 依赖: AlgEquiv, AlgEquiv.fintype, FiniteGrp, FiniteGrp.of, fintype
-/
def FiniteGaloisIntermediateField.finGaloisGroup (L : FiniteGaloisIntermediateField k K) :
    FiniteGrp :=
  letI := AlgEquiv.fintype k L
  FiniteGrp.of Gal(L/k)

/--
Definition of `finGaloisGroupMap` / `finGaloisGroupMap` 的定义

English:
definition finGaloisGroupMap
  signature: {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
  body: haveI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom le.1)
  haveI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  FiniteGrp.ofHom (AlgEquiv.restrictNormalHom L₂.unop)

中文:
定义 finGaloisGroupMap
  签名: {L₁ L₂ : (有限Galois中间域 k K)ᵒᵖ}
  定义体: haveI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom le.1)
  haveI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  FiniteGrp.ofHom (AlgEquiv.restrictNormalHom L₂.unop)

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormalHom, Algebra, FiniteGrp, FiniteGrp.ofHom, IsGalois, IsGalois.to_normal, IsScalarTower, IsScalarTower.of_algebraMap_eq, Normal, RingHom, RingHom.toAlgebra, Subsemiring, Subsemiring.inclusion, inclusion, leOfHom, of_algebraMap_eq, restrictNormalHom, toAlgebra, to_normal
-/
noncomputable def finGaloisGroupMap {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (le : L₁ ⟶ L₂) : L₁.unop.finGaloisGroup ⟶ L₂.unop.finGaloisGroup :=
  haveI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom le.1)
  haveI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  FiniteGrp.ofHom (AlgEquiv.restrictNormalHom L₂.unop)

namespace finGaloisGroupMap

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (L : (FiniteGaloisIntermediateField k K)ᵒᵖ)
  proof: ConcreteCategory.ext (AlgEquiv.restrictNormalHom_id _ _)

@[simp]

中文:
引理 map_id
  条件: (L : (有限Galois中间域 k K)ᵒᵖ)
  证明: ConcreteCategory.ext (AlgEquiv.restrictNormalHom_id _ _)

@[simp]

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormalHom_id, ConcreteCategory, ConcreteCategory.ext, restrictNormalHom_id
-/
lemma map_id (L : (FiniteGaloisIntermediateField k K)ᵒᵖ) :
    (finGaloisGroupMap (𝟙 L)) = 𝟙 L.unop.finGaloisGroup :=
  ConcreteCategory.ext (AlgEquiv.restrictNormalHom_id _ _)

@[simp]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: {L₁ L₂ L₃ : (FiniteGaloisIntermediateField k K)ᵒᵖ} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃)
  proof: by
  iterate 2
    induction L₁ with | _ L₁ => ?_
    induction L₂ with | _ L₂ => ?_
    induction L₃ with | _ L₃ => ?_
  algebraize [Subsemiring.inclusion g.unop.le, Subsemiring.inclusion f.unop.le,
    Subsemiring.inclusion (g.unop.le.trans f.unop.le)]
  have : IsScalarTower k L₂ L₁ := IsScalarTow

中文:
引理 map_comp
  条件: {L₁ L₂ L₃ : (有限Galois中间域 k K)ᵒᵖ} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃)
  证明: by
  iterate 2
    induction L₁ with | _ L₁ => ?_
    induction L₂ with | _ L₂ => ?_
    induction L₃ with | _ L₃ => ?_
  algebraize [Subsemiring.inclusion g.unop.le, Subsemiring.inclusion f.unop.le,
    Subsemiring.inclusion (g.unop.le.trans f.unop.le)]
  have : IsScalarTower k L₂ L₁ := IsScalarTow

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_, IsScalarTower.of_algebraMap_eq, Subsemiring, Subsemiring.inclusion, algebraize, f.unop.le, g.unop.le, g.unop.le.trans, inclusion, iterate, of_algebraMap_, of_algebraMap_eq
-/
lemma map_comp {L₁ L₂ L₃ : (FiniteGaloisIntermediateField k K)ᵒᵖ} (f : L₁ ⟶ L₂) (g : L₂ ⟶ L₃) :
    finGaloisGroupMap (f ≫ g) = finGaloisGroupMap f ≫ finGaloisGroupMap g := by
  iterate 2
    induction L₁ with | _ L₁ => ?_
    induction L₂ with | _ L₂ => ?_
    induction L₃ with | _ L₃ => ?_
  algebraize [Subsemiring.inclusion g.unop.le, Subsemiring.inclusion f.unop.le,
    Subsemiring.inclusion (g.unop.le.trans f.unop.le)]
  have : IsScalarTower k L₂ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k L₃ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower k L₃ L₂ := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower L₃ L₂ L₁ := IsScalarTower.of_algebraMap_eq' rfl
  ext : 1
  apply IsScalarTower.AlgEquiv.restrictNormalHom_comp k L₃ L₂ L₁

end finGaloisGroupMap

variable (k K) in
/--
Definition of `finGaloisGroupFunctor` / `finGaloisGroupFunctor` 的定义

English:
definition finGaloisGroupFunctor
  signature: : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp where
  body: L.unop.finGaloisGroup
  map := finGaloisGroupMap
  map_id := finGaloisGroupMap.map_id
  map_comp := finGaloisGroupMap.map_comp

中文:
定义 finGaloisGroupFunctor
  签名: : (有限Galois中间域 k K)ᵒᵖ ⥤ FiniteGrp where
  定义体: L.unop.finGaloisGroup
  map := finGaloisGroupMap
  map_id := finGaloisGroupMap.map_id
  map_comp := finGaloisGroupMap.map_comp

Depends on / 依赖: L.unop.finGaloisGroup, finGaloisGroup
-/
noncomputable def finGaloisGroupFunctor : (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ FiniteGrp where
  obj L := L.unop.finGaloisGroup
  map := finGaloisGroupMap
  map_id := finGaloisGroupMap.map_id
  map_comp := finGaloisGroupMap.map_comp

open FiniteGaloisIntermediateField ProfiniteGrp

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

variable (k K) in
/--
Definition of `asProfiniteGaloisGroupFunctor` / `asProfiniteGaloisGroupFunctor` 的定义

English:
abbreviation asProfiniteGaloisGroupFunctor
  signature: :
  body: (finGaloisGroupFunctor k K) ⋙ forget₂ FiniteGrp ProfiniteGrp

中文:
缩写 asProfiniteGaloisGroupFunctor
  签名: :
  定义体: (finGaloisGroupFunctor k K) ⋙ forget₂ FiniteGrp ProfiniteGrp

Depends on / 依赖: FiniteGrp, ProfiniteGrp, finGaloisGroupFunctor
-/
noncomputable abbrev asProfiniteGaloisGroupFunctor :
    (FiniteGaloisIntermediateField k K)ᵒᵖ ⥤ ProfiniteGrp :=
  (finGaloisGroupFunctor k K) ⋙ forget₂ FiniteGrp ProfiniteGrp

variable (k K) in
/--
Definition of `algEquivToLimit` / `algEquivToLimit` 的定义

English:
definition algEquivToLimit
  signature: : Gal(K/k) ->* limit (asProfiniteGaloisGroupFunctor k K) where
  body: {
    val := fun L => σ.restrictNormalHom L.unop
    property := fun {L₁ L₂} π => by
      algebraize [Subsemiring.inclusion π.1.le]
      have : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      have : IsScalarTower L₂.unop L₁.unop K := IsScalarTower.of_algebraM

中文:
定义 algEquivToLimit
  签名: : Gal(K/k) ->* limit (asProfiniteGaloisGroupFunctor k K) where
  定义体: {
    val := fun L => σ.restrictNormalHom L.unop
    property := fun {L₁ L₂} π => by
      algebraize [Subsemiring.inclusion π.1.le]
      have : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      have : IsScalarTower L₂.unop L₁.unop K := IsScalarTower.of_algebraM
-/
noncomputable def algEquivToLimit : Gal(K/k) ->* limit (asProfiniteGaloisGroupFunctor k K) where
  toFun σ := {
    val := fun L => σ.restrictNormalHom L.unop
    property := fun {L₁ L₂} π => by
      algebraize [Subsemiring.inclusion π.1.le]
      have : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      have : IsScalarTower L₂.unop L₁.unop K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
      apply (IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply L₂.unop L₁.unop σ).symm }
  map_one' := by
    simp only [map_one]
    rfl
  map_mul' x y := by
    simp only [map_mul]
    rfl

/--
theorem `restrictNormalHom_continuous` / 定理 `restrictNormalHom_continuous`

English:
theorem restrictNormalHom_continuous
  given: (L : IntermediateField k K) [Normal k L]
  proof: by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one]; rw [krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨L', _, hO⟩ := hN
have := Module.Finite.equiv AlgEquiv.toLinearEquiv IntermediateField.liftAlgEquiv L'
  apply mem_nhds_iff.mpr
  use (IntermediateFiel

中文:
定理 restrictNormalHom_continuous
  条件: (L : 中间域 k K) [正规 k L]
  证明: by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one]; rw [krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨L', _, hO⟩ := hN
have := Module.Finite.equiv AlgEquiv.toLinearEquiv IntermediateField.liftAlgEquiv L'
  apply mem_nhds_iff.mpr
  use (IntermediateFiel

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormal_commutes, AlgEquiv.toLinearEquiv, Finite, IntermediateField, IntermediateField.lift, IntermediateField.liftAlgEquiv, IntermediateField.mem_fixingSubgroup_iff, Module, Module.Finite.equiv, SetLike, SetLike.mem_coe, continuousAt_def, continuousAt_def.mpr, continuous_of_continuousAt_one, fixingSubgroup, krullTopology_mem_nhds_one_iff, liftAlgEquiv, map_one, mem_coe
-/
theorem restrictNormalHom_continuous (L : IntermediateField k K) [Normal k L] :
    Continuous (AlgEquiv.restrictNormalHom (F := k) (K₁ := K) L) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one]; rw [krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨L', _, hO⟩ := hN
have := Module.Finite.equiv AlgEquiv.toLinearEquiv IntermediateField.liftAlgEquiv L'
  apply mem_nhds_iff.mpr
  use (IntermediateField.lift L').fixingSubgroup
  constructor
  · intro x hx
    apply hO
    simp only [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hx ⊢
    intro y hy
    have := AlgEquiv.restrictNormal_commutes x L y
    dsimp at this
    rw [hx y.1 ((IntermediateField.mem_lift y).mpr hy)] at this
    exact SetLike.coe_eq_coe.mp this
  · exact ⟨IntermediateField.fixingSubgroup_isOpen (IntermediateField.lift L'), congrFun rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `algEquivToLimit_continuous` / 引理 `algEquivToLimit_continuous`

English:
lemma algEquivToLimit_continuous
  statement: Continuous (algEquivToLimit k K)
  proof: by
  rw [continuous_induced_rng]
  refine continuous_pi (fun L => ?_)
  convert! restrictNormalHom_continuous L.unop.1
  exact (DiscreteTopology.eq_bot (α := L.unop ≃ₐ[k] L.unop)).symm

中文:
引理 algEquivToLimit_continuous
  结论: 连续 (algEquivToLimit k K)
  证明: by
  rw [continuous_induced_rng]
  refine continuous_pi (fun L => ?_)
  convert! restrictNormalHom_continuous L.unop.1
  exact (DiscreteTopology.eq_bot (α := L.unop ≃ₐ[k] L.unop)).symm

Depends on / 依赖: DiscreteTopology, DiscreteTopology.eq_bot, L.unop, continuous_induced_rng, continuous_pi, convert, eq_bot, restrictNormalHom_continuous
-/
lemma algEquivToLimit_continuous : Continuous (algEquivToLimit k K) := by
  rw [continuous_induced_rng]
  refine continuous_pi (fun L => ?_)
  convert! restrictNormalHom_continuous L.unop.1
  exact (DiscreteTopology.eq_bot (α := L.unop ≃ₐ[k] L.unop)).symm

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (L : FiniteGaloisIntermediateField k K)
  body: g.val (op L)
  map_one' := rfl
  map_mul' _ _ := rfl

中文:
定义 proj
  签名: (L : 有限Galois中间域 k K)
  定义体: g.val (op L)
  map_one' := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: g.val
-/
noncomputable def proj (L : FiniteGaloisIntermediateField k K) :
    limit (asProfiniteGaloisGroupFunctor k K) ->* Gal(L/k) where
  toFun g := g.val (op L)
  map_one' := rfl
  map_mul' _ _ := rfl

/--
lemma `finGaloisGroupFunctor_map_proj_eq_proj` / 引理 `finGaloisGroupFunctor_map_proj_eq_proj`

English:
lemma finGaloisGroupFunctor_map_proj_eq_proj
  statement: (g : limit (asProfiniteGaloisGroupFunctor k K))
  proof: g.prop h.op

中文:
引理 finGaloisGroupFunctor_map_proj_eq_proj
  结论: (g : limit (asProfiniteGaloisGroupFunctor k K))
  证明: g.prop h.op

Depends on / 依赖: g.prop, h.op
-/
lemma finGaloisGroupFunctor_map_proj_eq_proj (g : limit (asProfiniteGaloisGroupFunctor k K))
    {L₁ L₂ : FiniteGaloisIntermediateField k K} (h : L₁ ⟶ L₂) :
    (finGaloisGroupFunctor k K).map h.op (proj L₂ g) = proj L₁ g :=
  g.prop h.op

/--
lemma `proj_of_le` / 引理 `proj_of_le`

English:
lemma proj_of_le
  statement: (L : FiniteGaloisIntermediateField k K)
  proof: by
  induction L with | _ L => ?_
  induction L' with | _ L' => ?_
  let : Algebra L L' := RingHom.toAlgebra (Subsemiring.inclusion h)
  let : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← finGaloisGroupFunctor_map_proj_eq_proj g h.hom]
  change (algebraMap L' K (alge

中文:
引理 proj_of_le
  结论: (L : 有限Galois中间域 k K)
  证明: by
  induction L with | _ L => ?_
  induction L' with | _ L' => ?_
  let : Algebra L L' := RingHom.toAlgebra (Subsemiring.inclusion h)
  let : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← finGaloisGroupFunctor_map_proj_eq_proj g h.hom]
  change (algebraMap L' K (alge

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormal, AlgEquiv.restrictNormal_commutes, Algebra, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.toAlgebra, Subsemiring, Subsemiring.inclusion, algebraMap, finGaloisGroupFunctor_map_proj_eq_proj, h.hom, inclusion, of_algebraMap_eq, restrictNormal, restrictNormal_commutes, toAlgebra
-/
lemma proj_of_le (L : FiniteGaloisIntermediateField k K)
    (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : L)
    (L' : FiniteGaloisIntermediateField k K) (h : L <= L') :
    (proj L g x).val = (proj L' g ⟨x, h x.2⟩).val := by
  induction L with | _ L => ?_
  induction L' with | _ L' => ?_
  let : Algebra L L' := RingHom.toAlgebra (Subsemiring.inclusion h)
  let : IsScalarTower k L L' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  rw [← finGaloisGroupFunctor_map_proj_eq_proj g h.hom]
  change (algebraMap L' K (algebraMap L L' (AlgEquiv.restrictNormal (proj (mk L') g) L x))) = _
  rw [AlgEquiv.restrictNormal_commutes (proj (mk L') g) L]
  rfl

/--
lemma `proj_adjoin_singleton_val` / 引理 `proj_adjoin_singleton_val`

English:
lemma proj_adjoin_singleton_val
  statement: [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
  proof: proj_of_le _ g y _ _

中文:
引理 proj_adjoin_singleton_val
  结论: [是Galois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
  证明: proj_of_le _ g y _ _

Depends on / 依赖: proj_of_le
-/
lemma proj_adjoin_singleton_val [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
    (x : K) (y : adjoin k {x}) (L : FiniteGaloisIntermediateField k K)
    (h : x in L.toIntermediateField) :
    (proj (adjoin k {x}) g y).val = (proj L g ⟨y, adjoin_simple_le_iff.mpr h y.2⟩).val :=
  proj_of_le _ g y _ _

set_option backward.privateInPublic true in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def toAlgEquivAux [IsGalois k K]
  body: fun x => (proj (adjoin k {x}) g ⟨x, subset_adjoin _ _ (by simp only [Set.mem_singleton_iff])⟩).val

中文:
定义 noncomputable
  签名: def toAlgEquivAux [是Galois k K]
  定义体: fun x => (proj (adjoin k {x}) g ⟨x, subset_adjoin _ _ (by simp only [Set.mem_singleton_iff])⟩).val
-/
private noncomputable def toAlgEquivAux [IsGalois k K]
    (g : limit (asProfiniteGaloisGroupFunctor k K)) : K -> K :=
  fun x => (proj (adjoin k {x}) g ⟨x, subset_adjoin _ _ (by simp only [Set.mem_singleton_iff])⟩).val

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `toAlgEquivAux_eq_proj_of_mem` / 引理 `toAlgEquivAux_eq_proj_of_mem`

English:
lemma toAlgEquivAux_eq_proj_of_mem
  statement: [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
  proof: proj_adjoin_singleton_val g _ _ L hx

中文:
引理 toAlgEquivAux_eq_proj_of_mem
  结论: [是Galois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
  证明: proj_adjoin_singleton_val g _ _ L hx

Depends on / 依赖: proj_adjoin_singleton_val
-/
lemma toAlgEquivAux_eq_proj_of_mem [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
    (x : K) (L : FiniteGaloisIntermediateField k K) (hx : x in L.toIntermediateField) :
    toAlgEquivAux g x = (proj L g ⟨x, hx⟩).val :=
  proj_adjoin_singleton_val g _ _ L hx

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `mk_toAlgEquivAux` / 引理 `mk_toAlgEquivAux`

English:
lemma mk_toAlgEquivAux
  statement: [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : K)
  proof: by
  rw [Subtype.ext_iff]; rw [Subtype.coe_mk]; rw [toAlgEquivAux_eq_proj_of_mem]

中文:
引理 mk_toAlgEquivAux
  结论: [是Galois k K] (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : K)
  证明: by
  rw [Subtype.ext_iff]; rw [Subtype.coe_mk]; rw [toAlgEquivAux_eq_proj_of_mem]

Depends on / 依赖: Subtype, Subtype.coe_mk, Subtype.ext_iff, coe_mk, ext_iff, toAlgEquivAux_eq_proj_of_mem
-/
lemma mk_toAlgEquivAux [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K)) (x : K)
    (L : FiniteGaloisIntermediateField k K) (hx' : toAlgEquivAux g x in L.toIntermediateField)
    (hx : x in L.toIntermediateField) :
    (⟨toAlgEquivAux g x, hx'⟩ : L.toIntermediateField) = proj L g ⟨x, hx⟩ := by
  rw [Subtype.ext_iff]; rw [Subtype.coe_mk]; rw [toAlgEquivAux_eq_proj_of_mem]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
lemma `toAlgEquivAux_eq_liftNormal` / 引理 `toAlgEquivAux_eq_liftNormal`

English:
lemma toAlgEquivAux_eq_liftNormal
  statement: [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
  proof: by
  rw [toAlgEquivAux_eq_proj_of_mem g x L hx]
  exact (AlgEquiv.liftNormal_commutes (proj L g) _ ⟨x, hx⟩).symm

中文:
引理 toAlgEquivAux_eq_liftNormal
  结论: [是Galois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
  证明: by
  rw [toAlgEquivAux_eq_proj_of_mem g x L hx]
  exact (AlgEquiv.liftNormal_commutes (proj L g) _ ⟨x, hx⟩).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.liftNormal_commutes, liftNormal_commutes, toAlgEquivAux_eq_proj_of_mem
-/
lemma toAlgEquivAux_eq_liftNormal [IsGalois k K] (g : limit (asProfiniteGaloisGroupFunctor k K))
    (x : K) (L : FiniteGaloisIntermediateField k K) (hx : x in L.toIntermediateField) :
    toAlgEquivAux g x = (proj L g).liftNormal K x := by
  rw [toAlgEquivAux_eq_proj_of_mem g x L hx]
  exact (AlgEquiv.liftNormal_commutes (proj L g) _ ⟨x, hx⟩).symm

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- `toAlgEquivAux` as an `AlgEquiv`.
It is done by using above lifting lemmas on bigger `FiniteGaloisIntermediateField`. -/
@[simps]
/--
Definition of `limitToAlgEquiv` / `limitToAlgEquiv` 的定义

English:
definition limitToAlgEquiv
  signature: [IsGalois k K]
  body: toAlgEquivAux g
  invFun := toAlgEquivAux g⁻¹
  left_inv x := by
    let L := adjoin k {x, toAlgEquivAux g x}
    have hx : x in L.1 := subset_adjoin _ _ (Set.mem_insert x {toAlgEquivAux g x})
    have hx' : toAlgEquivAux g x in L.1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [t

中文:
定义 limitToAlgEquiv
  签名: [是Galois k K]
  定义体: toAlgEquivAux g
  invFun := toAlgEquivAux g⁻¹
  left_inv x := by
    let L := adjoin k {x, toAlgEquivAux g x}
    have hx : x in L.1 := subset_adjoin _ _ (Set.mem_insert x {toAlgEquivAux g x})
    have hx' : toAlgEquivAux g x in L.1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [t

Depends on / 依赖: toAlgEquivAux
-/
noncomputable def limitToAlgEquiv [IsGalois k K]
    (g : limit (asProfiniteGaloisGroupFunctor k K)) : Gal(K/k) where
  toFun := toAlgEquivAux g
  invFun := toAlgEquivAux g⁻¹
  left_inv x := by
    let L := adjoin k {x, toAlgEquivAux g x}
    have hx : x in L.1 := subset_adjoin _ _ (Set.mem_insert x {toAlgEquivAux g x})
    have hx' : toAlgEquivAux g x in L.1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [toAlgEquivAux_eq_proj_of_mem _ _ L hx', map_inv, AlgEquiv.aut_inv,
      mk_toAlgEquivAux g x L hx' hx, AlgEquiv.symm_apply_apply]
  right_inv x := by
    let L := adjoin k {x, toAlgEquivAux g⁻¹ x}
    have hx : x in L.1 := subset_adjoin _ _ (Set.mem_insert x {toAlgEquivAux g⁻¹ x})
    have hx' : toAlgEquivAux g⁻¹ x in L.1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [toAlgEquivAux_eq_proj_of_mem _ _ L hx', mk_toAlgEquivAux g⁻¹ x L hx' hx, map_inv,
      AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  map_mul' x y := by
    have hx : x in (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert x {y})
    have hy : y in (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    rw [toAlgEquivAux_eq_liftNormal g x (adjoin k {x]; rw [y}) hx]; rw [toAlgEquivAux_eq_liftNormal g y (adjoin k {x]; rw [y}) hy]; rw [toAlgEquivAux_eq_liftNormal g (x * y) (adjoin k {x]; rw [y}) (mul_mem hx hy)]; rw [map_mul]
  map_add' x y := by
    have hx : x in (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert x {y})
    have hy : y in (adjoin k {x, y}).1 := subset_adjoin _ _ (Set.mem_insert_of_mem x rfl)
    simp only [toAlgEquivAux_eq_liftNormal g x (adjoin k {x, y}) hx,
      toAlgEquivAux_eq_liftNormal g y (adjoin k {x, y}) hy,
      toAlgEquivAux_eq_liftNormal g (x + y) (adjoin k {x, y}) (add_mem hx hy), map_add]
  commutes' x := by
    simp only [toAlgEquivAux_eq_liftNormal g _ ⊥ (algebraMap_mem _ x), AlgEquiv.commutes]

variable (k K) in
/--
Definition of `mulEquivToLimit` / `mulEquivToLimit` 的定义

English:
definition mulEquivToLimit
  signature: [IsGalois k K]
  body: algEquivToLimit k K
  map_mul' := map_mul _
  invFun := limitToAlgEquiv
  left_inv := fun f => AlgEquiv.ext fun x =>
    AlgEquiv.restrictNormal_commutes f (adjoin k {x}).1 ⟨x, _⟩
  right_inv := fun g => by
    apply Subtype.val_injective
    ext L
    change (limitToAlgEquiv g).restrictNormal _ = _

中文:
定义 mulEquivToLimit
  签名: [是Galois k K]
  定义体: algEquivToLimit k K
  map_mul' := map_mul _
  invFun := limitToAlgEquiv
  left_inv := fun f => AlgEquiv.ext fun x =>
    AlgEquiv.restrictNormal_commutes f (adjoin k {x}).1 ⟨x, _⟩
  right_inv := fun g => by
    apply Subtype.val_injective
    ext L
    change (limitToAlgEquiv g).restrictNormal _ = _

Depends on / 依赖: algEquivToLimit
-/
noncomputable def mulEquivToLimit [IsGalois k K] :
    Gal(K/k) ≃* limit (asProfiniteGaloisGroupFunctor k K) where
  toFun := algEquivToLimit k K
  map_mul' := map_mul _
  invFun := limitToAlgEquiv
  left_inv := fun f => AlgEquiv.ext fun x =>
    AlgEquiv.restrictNormal_commutes f (adjoin k {x}).1 ⟨x, _⟩
  right_inv := fun g => by
    apply Subtype.val_injective
    ext L
    change (limitToAlgEquiv g).restrictNormal _ = _
    ext x
    have : ((limitToAlgEquiv g).restrictNormal L.unop) x = (limitToAlgEquiv g) x.1 := by
      exact AlgEquiv.restrictNormal_commutes (limitToAlgEquiv g) L.unop x
    simp_rw [this]
    exact proj_adjoin_singleton_val _ _ _ _ x.2

open scoped Topology in
/--
lemma `krullTopology_mem_nhds_one_iff_of_isGalois` / 引理 `krullTopology_mem_nhds_one_iff_of_isGalois`

English:
lemma krullTopology_mem_nhds_one_iff_of_isGalois
  given: [IsGalois k K] (A : Set Gal(K/k))
  proof: by
  rw [krullTopology_mem_nhds_one_iff_of_normal]
  exact ⟨fun ⟨L, _, hL, hsub⟩ => ⟨{ toIntermediateField := L, isGalois := ⟨⟩ }, hsub⟩,
    fun ⟨L, hL⟩ => ⟨L, inferInstance, inferInstance, hL⟩⟩

中文:
引理 krullTopology_mem_nhds_one_iff_of_isGalois
  条件: [是Galois k K] (A : 集合 Gal(K/k))
  证明: by
  rw [krullTopology_mem_nhds_one_iff_of_normal]
  exact ⟨fun ⟨L, _, hL, hsub⟩ => ⟨{ toIntermediateField := L, isGalois := ⟨⟩ }, hsub⟩,
    fun ⟨L, hL⟩ => ⟨L, inferInstance, inferInstance, hL⟩⟩

Depends on / 依赖: isGalois, krullTopology_mem_nhds_one_iff_of_normal, toIntermediateField
-/
lemma krullTopology_mem_nhds_one_iff_of_isGalois [IsGalois k K] (A : Set Gal(K/k)) :
    A in 𝓝 1 ↔ exists (L : FiniteGaloisIntermediateField k K), (L.fixingSubgroup : Set _) subseteq A := by
  rw [krullTopology_mem_nhds_one_iff_of_normal]
  exact ⟨fun ⟨L, _, hL, hsub⟩ => ⟨{ toIntermediateField := L, isGalois := ⟨⟩ }, hsub⟩,
    fun ⟨L, hL⟩ => ⟨L, inferInstance, inferInstance, hL⟩⟩

/--
lemma `isOpen_mulEquivToLimit_image_fixingSubgroup` / 引理 `isOpen_mulEquivToLimit_image_fixingSubgroup`

English:
lemma isOpen_mulEquivToLimit_image_fixingSubgroup
  statement: [IsGalois k K]
  proof: by
  let fix1 : Set (Π L, (asProfiniteGaloisGroupFunctor k K).obj L) := {f | f (op L) = 1}
  suffices mulEquivToLimit k K '' L.1.fixingSubgroup = Set.preimage Subtype.val fix1 by
    rw [this]
    exact (isOpen_induced <| (continuous_apply (op L)).isOpen_preimage {1} trivial)
  ext x
  obtain ⟨σ, rf

中文:
引理 isOpen_mulEquivToLimit_image_fixingSubgroup
  结论: [是Galois k K]
  证明: by
  let fix1 : Set (Π L, (asProfiniteGaloisGroupFunctor k K).obj L) := {f | f (op L) = 1}
  suffices mulEquivToLimit k K '' L.1.fixingSubgroup = Set.preimage Subtype.val fix1 by
    rw [this]
    exact (isOpen_induced <| (continuous_apply (op L)).isOpen_preimage {1} trivial)
  ext x
  obtain ⟨σ, rf

Depends on / 依赖: FiniteGaloisIntermediateField, FiniteGaloisIntermediateField.mem_fixingSubgroup_iff, Set.preimage, Subtype, Subtype.val, asProfiniteGaloisGroupFunctor, continuous_apply, fixingSubgroup, isOpen_induced, isOpen_preimage, mem_fixingSubgroup_iff, mulEquivToLimit, preimage, surjective
-/
lemma isOpen_mulEquivToLimit_image_fixingSubgroup [IsGalois k K]
    (L : FiniteGaloisIntermediateField k K) : IsOpen (mulEquivToLimit k K '' L.fixingSubgroup) := by
  let fix1 : Set (Π L, (asProfiniteGaloisGroupFunctor k K).obj L) := {f | f (op L) = 1}
  suffices mulEquivToLimit k K '' L.1.fixingSubgroup = Set.preimage Subtype.val fix1 by
    rw [this]
    exact (isOpen_induced <| (continuous_apply (op L)).isOpen_preimage {1} trivial)
  ext x
  obtain ⟨σ, rfl⟩ := (mulEquivToLimit k K).surjective x
  simpa using! FiniteGaloisIntermediateField.mem_fixingSubgroup_iff σ L

/--
lemma `mulEquivToLimit_symm_continuous` / 引理 `mulEquivToLimit_symm_continuous`

English:
lemma mulEquivToLimit_symm_continuous
  given: [IsGalois k K]
  statement: Continuous (mulEquivToLimit k K).symm
  proof: by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  simp only [map_one, krullTopology_mem_nhds_one_iff_of_isGalois, ← MulEquiv.coe_toEquiv_symm,
    ← MulEquiv.toEquiv_eq_coe, ← (mulEquivToLimit k K).image_eq_preimage_symm]
  intro H ⟨L, le⟩
  rw [mem_nhds_iff]
  use mulEquivToLim

中文:
引理 mulEquivToLimit_symm_continuous
  条件: [是Galois k K]
  结论: 连续 (mulEquivToLimit k K).symm
  证明: by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  simp only [map_one, krullTopology_mem_nhds_one_iff_of_isGalois, ← MulEquiv.coe_toEquiv_symm,
    ← MulEquiv.toEquiv_eq_coe, ← (mulEquivToLimit k K).image_eq_preimage_symm]
  intro H ⟨L, le⟩
  rw [mem_nhds_iff]
  use mulEquivToLim

Depends on / 依赖: MulEquiv, MulEquiv.coe_toEquiv_symm, MulEquiv.toEquiv_eq_coe, Set.image_mono, Set.image_subset_iff.mp, coe_toEquiv_symm, continuousAt_def, continuousAt_def.mpr, continuous_of_continuousAt_one, fixingSubgroup, image_eq_preimage_symm, image_mono, image_subset_iff, isOpen_mulEquivToLimit_image_fixingSubgroup, krullTopology_mem_nhds_one_iff_of_isGalois, map_one, mem_nhds_iff, mulEquivToLimit, one_mem, toEquiv_eq_coe
-/
lemma mulEquivToLimit_symm_continuous [IsGalois k K] : Continuous (mulEquivToLimit k K).symm := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  simp only [map_one, krullTopology_mem_nhds_one_iff_of_isGalois, ← MulEquiv.coe_toEquiv_symm,
    ← MulEquiv.toEquiv_eq_coe, ← (mulEquivToLimit k K).image_eq_preimage_symm]
  intro H ⟨L, le⟩
  rw [mem_nhds_iff]
  use mulEquivToLimit k K '' L.1.fixingSubgroup
  simp only [isOpen_mulEquivToLimit_image_fixingSubgroup L]
  simpa [one_mem] using Set.image_subset_iff.mp (Set.image_mono le)

variable (k K)

/--
Definition of `continuousMulEquivToLimit` / `continuousMulEquivToLimit` 的定义

English:
definition continuousMulEquivToLimit
  signature: [IsGalois k K]
  body: mulEquivToLimit k K
  continuous_toFun := algEquivToLimit_continuous
  continuous_invFun := mulEquivToLimit_symm_continuous

中文:
定义 continuousMulEquivToLimit
  签名: [是Galois k K]
  定义体: mulEquivToLimit k K
  continuous_toFun := algEquivToLimit_continuous
  continuous_invFun := mulEquivToLimit_symm_continuous

Depends on / 依赖: mulEquivToLimit
-/
noncomputable def continuousMulEquivToLimit [IsGalois k K] :
    Gal(K/k) ≃ₜ* limit (asProfiniteGaloisGroupFunctor k K) where
  toMulEquiv := mulEquivToLimit k K
  continuous_toFun := algEquivToLimit_continuous
  continuous_invFun := mulEquivToLimit_symm_continuous

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsGalois
  signature: k K] : CompactSpace Gal(K/k)
  body: (continuousMulEquivToLimit k K).symm.compactSpace

中文:
实例 [是Galois
  签名: k K] : 紧空间 Gal(K/k)
  定义体: (continuousMulEquivToLimit k K).symm.compactSpace

Depends on / 依赖: compactSpace, continuousMulEquivToLimit, symm.compactSpace
-/
instance [IsGalois k K] : CompactSpace Gal(K/k) :=
  (continuousMulEquivToLimit k K).symm.compactSpace

/--
Definition of `profiniteGalGrp` / `profiniteGalGrp` 的定义

English:
definition profiniteGalGrp
  signature: [IsGalois k K]
  body: ProfiniteGrp.of Gal(K/k)

中文:
定义 profiniteGalGrp
  签名: [是Galois k K]
  定义体: ProfiniteGrp.of Gal(K/k)

Depends on / 依赖: ProfiniteGrp, ProfiniteGrp.of
-/
noncomputable def profiniteGalGrp [IsGalois k K] : ProfiniteGrp :=
  ProfiniteGrp.of Gal(K/k)

/--
Definition of `profiniteGalGrpIsoLimit` / `profiniteGalGrpIsoLimit` 的定义

English:
definition profiniteGalGrpIsoLimit
  signature: [IsGalois k K]
  body: ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivToLimit k K)

中文:
定义 profiniteGalGrpIsoLimit
  签名: [是Galois k K]
  定义体: ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivToLimit k K)

Depends on / 依赖: ContinuousMulEquiv, ContinuousMulEquiv.toProfiniteGrpIso, continuousMulEquivToLimit, toProfiniteGrpIso
-/
noncomputable def profiniteGalGrpIsoLimit [IsGalois k K] :
    profiniteGalGrp k K ≅ limit (asProfiniteGaloisGroupFunctor k K) :=
  ContinuousMulEquiv.toProfiniteGrpIso (continuousMulEquivToLimit k K)

end InfiniteGalois

end Profinite
