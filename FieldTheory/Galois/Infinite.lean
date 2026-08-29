/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!

# The Fundamental Theorem of Infinite Galois Theory

In this file, we prove the fundamental theorem of infinite Galois theory and the special case for
open subgroups and normal subgroups. We first verify that `IntermediateField.fixingSubgroup` and
`IntermediateField.fixedField` are inverses of each other between intermediate fields and
closed subgroups of the Galois group.

## Main definitions and results

In `K/k`, for any intermediate field `L` :

* `fixingSubgroup_isClosed` : the subgroup fixing `L` (`Gal(K/L)`) is closed.

* `fixedField_fixingSubgroup` : the field fixed by the
  subgroup fixing `L` is equal to `L` itself.

For any subgroup `H` of `Gal(K/k)` :

* `restrict_fixedField` : For a Galois intermediate field `M`, the fixed field of the image of `H`
  restricted to `M` is equal to the fixed field of `H` intersected with `M`.
* `fixingSubgroup_fixedField` : If `H` is closed, the fixing subgroup of the fixed field of `H`
  is equal to `H` itself.

The fundamental theorem of infinite Galois theory :

* `IntermediateFieldEquivClosedSubgroup` : The order equivalence is given by mapping any
  intermediate field `L` to the subgroup fixing `L`, and the inverse maps any
  closed subgroup of `Gal(K/k)` `H` to the fixed field of `H`. The composition is equal to
  the identity as described in the lemmas above, and compatibility with the order follows easily.

Special cases :

* `isOpen_iff_finite` : The fixing subgroup of an intermediate field `L` is open if and only if
  `L` is finite-dimensional.

* `normal_iff_isGalois` : The fixing subgroup of an intermediate field `L` is normal if and only if
  `L` is Galois.

-/

@[expose] public section

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

namespace InfiniteGalois

open scoped Pointwise
open FiniteGaloisIntermediateField AlgEquiv
--Note: The `adjoin`s below are `FiniteGaloisIntermediateField.adjoin`

/--
lemma `fixingSubgroup_isClosed` / 引理 `fixingSubgroup_isClosed`

English:
lemma fixingSubgroup_isClosed
  given: (L : IntermediateField k K) [IsGalois k K]
  proof: isOpen_iff_mem_nhds.mpr fun σ h => by
    apply mem_nhds_iff.mpr
    rcases Set.not_subset.mp ((mem_fixingSubgroup_iff Gal(K/k)).not.mp h) with ⟨y, yL, ne⟩
    use σ • ((adjoin k {y}).1.fixingSubgroup : Set Gal(K/k))
    constructor
    · intro f hf
      rcases (Set.mem_smul_set.mp hf) with ⟨g, hg, eq⟩
      simp only [Set.mem_compl_iff, SetLike.mem_coe, ← eq]
      apply (mem_fixingSubgroup_iff Gal(K/k)).not.mpr
      push Not
      use y
      simp only [yL, smul_eq_mul, AlgEquiv.smul_def, AlgEquiv.mul_apply, ne_eq, true_and]
have : g y = y := (mem_fixingSubgroup_iff Gal(K/k)).mp hg y
        adjoin_simple_le_iff.mp le_rfl
      simpa only [this, ne_eq, AlgEquiv.smul_def] using! ne
    · simp only [(IntermediateField.fixingSubgroup_isOpen (adjoin k {y}).1).smul σ, true_and]
      use 1
      simp only [SetLike.mem_coe, smul_eq_mul, mul_one, and_true, Subgroup.one_mem]

中文:
引理 fixingSubgroup_isClosed
  条件: (L : 中间域 k K) [是Galois k K]
  证明: isOpen_iff_mem_nhds.mpr fun σ h => by
    apply mem_nhds_iff.mpr
    rcases Set.not_subset.mp ((mem_fixingSubgroup_iff Gal(K/k)).not.mp h) with ⟨y, yL, ne⟩
    use σ • ((adjoin k {y}).1.fixingSubgroup : Set Gal(K/k))
    constructor
    · intro f hf
      rcases (Set.mem_smul_set.mp hf) with ⟨g, hg, eq⟩
      simp only [Set.mem_compl_iff, SetLike.mem_coe, ← eq]
      apply (mem_fixingSubgroup_iff Gal(K/k)).not.mpr
      push Not
      use y
      simp only [yL, smul_eq_mul, AlgEquiv.smul_def, AlgEquiv.mul_apply, ne_eq, true_and]
have : g y = y := (mem_fixingSubgroup_iff Gal(K/k)).mp hg y
        adjoin_simple_le_iff.mp le_rfl
      simpa only [this, ne_eq, AlgEquiv.smul_def] using! ne
    · simp only [(IntermediateField.fixingSubgroup_isOpen (adjoin k {y}).1).smul σ, true_and]
      use 1
      simp only [SetLike.mem_coe, smul_eq_mul, mul_one, and_true, Subgroup.one_mem]

Depends on / 依赖: AlgEquiv, AlgEquiv.mul_apply, AlgEquiv.smul_def, Set.mem_compl_iff, Set.mem_smul_set.mp, Set.not_subset.mp, SetLike, SetLike.mem_coe, adjoin, fixingSubgroup, isOpen_iff_mem_nhds, isOpen_iff_mem_nhds.mpr, mem_coe, mem_compl_iff, mem_fixingSubgroup_iff, mem_nhds_iff, mem_nhds_iff.mpr, mem_smul_set, mul_apply, ne_eq
-/
lemma fixingSubgroup_isClosed (L : IntermediateField k K) [IsGalois k K] :
    IsClosed (L.fixingSubgroup : Set Gal(K/k)) where
  isOpen_compl := isOpen_iff_mem_nhds.mpr fun σ h => by
    apply mem_nhds_iff.mpr
    rcases Set.not_subset.mp ((mem_fixingSubgroup_iff Gal(K/k)).not.mp h) with ⟨y, yL, ne⟩
    use σ • ((adjoin k {y}).1.fixingSubgroup : Set Gal(K/k))
    constructor
    · intro f hf
      rcases (Set.mem_smul_set.mp hf) with ⟨g, hg, eq⟩
      simp only [Set.mem_compl_iff, SetLike.mem_coe, ← eq]
      apply (mem_fixingSubgroup_iff Gal(K/k)).not.mpr
      push Not
      use y
      simp only [yL, smul_eq_mul, AlgEquiv.smul_def, AlgEquiv.mul_apply, ne_eq, true_and]
have : g y = y := (mem_fixingSubgroup_iff Gal(K/k)).mp hg y
        adjoin_simple_le_iff.mp le_rfl
      simpa only [this, ne_eq, AlgEquiv.smul_def] using! ne
    · simp only [(IntermediateField.fixingSubgroup_isOpen (adjoin k {y}).1).smul σ, true_and]
      use 1
      simp only [SetLike.mem_coe, smul_eq_mul, mul_one, and_true, Subgroup.one_mem]

/--
lemma `fixedField_fixingSubgroup` / 引理 `fixedField_fixingSubgroup`

English:
lemma fixedField_fixingSubgroup
  given: (L : IntermediateField k K) [IsGalois k K]
  proof: by
  apply le_antisymm
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have mem : x in (adjoin L {x}).1 := subset_adjoin _ _ rfl
    have : IntermediateField.fixedField (⊤ : Subgroup ((adjoin L {x}) ≃ₐ[L] (adjoin L {x}))) = ⊥ :=
      (IsGalois.tfae.out 0 1).mp (by infer_instance)
    have : ⟨x, mem⟩ in (⊥ : IntermediateField L (adjoin L {x})) := by
      rw [← this]; rw [IntermediateField.mem_fixedField_iff]
      intro f _
      rcases restrictNormalHom_surjective K f with ⟨σ, hσ⟩
      apply Subtype.val_injective
      rw [← hσ]; rw [restrictNormalHom_apply (adjoin L {x}).1 σ ⟨x]; rw [mem⟩]
      have := hx ((IntermediateField.fixingSubgroupEquiv L).symm σ)
      simpa only [SetLike.coe_mem, true_implies]
    rcases IntermediateField.mem_bot.mp this with ⟨y, hy⟩
    obtain ⟨rfl⟩ : y = x := congrArg Subtype.val hy
    exact y.2
  · exact (IntermediateField.le_iff_le L.fixingSubgroup L).mpr le_rfl

中文:
引理 fixedField_fixingSubgroup
  条件: (L : 中间域 k K) [是Galois k K]
  证明: by
  apply le_antisymm
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have mem : x in (adjoin L {x}).1 := subset_adjoin _ _ rfl
    have : IntermediateField.fixedField (⊤ : Subgroup ((adjoin L {x}) ≃ₐ[L] (adjoin L {x}))) = ⊥ :=
      (IsGalois.tfae.out 0 1).mp (by infer_instance)
    have : ⟨x, mem⟩ in (⊥ : IntermediateField L (adjoin L {x})) := by
      rw [← this]; rw [IntermediateField.mem_fixedField_iff]
      intro f _
      rcases restrictNormalHom_surjective K f with ⟨σ, hσ⟩
      apply Subtype.val_injective
      rw [← hσ]; rw [restrictNormalHom_apply (adjoin L {x}).1 σ ⟨x]; rw [mem⟩]
      have := hx ((IntermediateField.fixingSubgroupEquiv L).symm σ)
      simpa only [SetLike.coe_mem, true_implies]
    rcases IntermediateField.mem_bot.mp this with ⟨y, hy⟩
    obtain ⟨rfl⟩ : y = x := congrArg Subtype.val hy
    exact y.2
  · exact (IntermediateField.le_iff_le L.fixingSubgroup L).mpr le_rfl

Depends on / 依赖: IntermediateField, IntermediateField.fixedField, IntermediateField.mem_fixedField_iff, IsGalois, IsGalois.tfae.out, Subgroup, Subtype, Subtype.val_injective, adjoin, fixedField, infer_instance, le_antisymm, mem_fixedField_iff, restrictNormalHom_surjective, subset_adjoin, val_injective
-/
lemma fixedField_fixingSubgroup (L : IntermediateField k K) [IsGalois k K] :
    IntermediateField.fixedField L.fixingSubgroup = L := by
  apply le_antisymm
  · intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have mem : x in (adjoin L {x}).1 := subset_adjoin _ _ rfl
    have : IntermediateField.fixedField (⊤ : Subgroup ((adjoin L {x}) ≃ₐ[L] (adjoin L {x}))) = ⊥ :=
      (IsGalois.tfae.out 0 1).mp (by infer_instance)
    have : ⟨x, mem⟩ in (⊥ : IntermediateField L (adjoin L {x})) := by
      rw [← this]; rw [IntermediateField.mem_fixedField_iff]
      intro f _
      rcases restrictNormalHom_surjective K f with ⟨σ, hσ⟩
      apply Subtype.val_injective
      rw [← hσ]; rw [restrictNormalHom_apply (adjoin L {x}).1 σ ⟨x]; rw [mem⟩]
      have := hx ((IntermediateField.fixingSubgroupEquiv L).symm σ)
      simpa only [SetLike.coe_mem, true_implies]
    rcases IntermediateField.mem_bot.mp this with ⟨y, hy⟩
    obtain ⟨rfl⟩ : y = x := congrArg Subtype.val hy
    exact y.2
  · exact (IntermediateField.le_iff_le L.fixingSubgroup L).mpr le_rfl

/--
lemma `fixedField_bot` / 引理 `fixedField_bot`

English:
lemma fixedField_bot
  given: [IsGalois k K]
  proof: by
  rw [← IntermediateField.fixingSubgroup_bot]; rw [fixedField_fixingSubgroup]

中文:
引理 fixedField_bot
  条件: [是Galois k K]
  证明: by
  rw [← IntermediateField.fixingSubgroup_bot]; rw [fixedField_fixingSubgroup]

Depends on / 依赖: IntermediateField, IntermediateField.fixingSubgroup_bot, fixedField_fixingSubgroup, fixingSubgroup_bot
-/
lemma fixedField_bot [IsGalois k K] :
    IntermediateField.fixedField (⊤ : Subgroup Gal(K/k)) = ⊥ := by
  rw [← IntermediateField.fixingSubgroup_bot]; rw [fixedField_fixingSubgroup]

/--
theorem `mem_bot_iff_fixed` / 定理 `mem_bot_iff_fixed`

English:
theorem mem_bot_iff_fixed
  given: [IsGalois k K] (x : K)
  proof: by
  simp [← fixedField_bot, IntermediateField.mem_fixedField_iff]

中文:
定理 mem_bot_iff_fixed
  条件: [是Galois k K] (x : K)
  证明: by
  simp [← fixedField_bot, IntermediateField.mem_fixedField_iff]

Depends on / 依赖: IntermediateField, IntermediateField.mem_fixedField_iff, fixedField_bot, mem_fixedField_iff
-/
theorem mem_bot_iff_fixed [IsGalois k K] (x : K) :
    x in (⊥ : IntermediateField k K) ↔ forall (f : Gal(K/k)), f x = x := by
  simp [← fixedField_bot, IntermediateField.mem_fixedField_iff]

/--
theorem `mem_range_algebraMap_iff_fixed` / 定理 `mem_range_algebraMap_iff_fixed`

English:
theorem mem_range_algebraMap_iff_fixed
  given: [IsGalois k K] (x : K)
  proof: mem_bot_iff_fixed x

中文:
定理 mem_range_algebraMap_iff_fixed
  条件: [是Galois k K] (x : K)
  证明: mem_bot_iff_fixed x

Depends on / 依赖: mem_bot_iff_fixed
-/
theorem mem_range_algebraMap_iff_fixed [IsGalois k K] (x : K) :
    x in Set.range (algebraMap k K) ↔ forall f : Gal(K/k), f x = x :=
  mem_bot_iff_fixed x

open IntermediateField in
/--
lemma `restrict_fixedField` / 引理 `restrict_fixedField`

English:
lemma restrict_fixedField
  given: (H : Subgroup Gal(K/k)) (L : IntermediateField k K) [Normal k L]
  proof: by
  apply SetLike.ext'
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have xL := h.out.2
    apply (mem_lift (⟨x, xL⟩ : L)).mpr
    simp only [mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro σ hσ
    apply Subtype.val_injective
    dsimp only
    nth_rw 2 [← (h.out.1 ⟨σ, hσ⟩)]
    exact AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩
  · have xL := lift_le _ h
    apply (mem_lift (⟨x, xL⟩ : L)).mp at h
    simp only [mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h
    simp only [coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_fixedField_iff, xL, and_true]
    intro σ hσ
    have : ((restrictNormalHom L σ) ⟨x, xL⟩).1 = x := by rw [h σ hσ]
    nth_rw 2 [← this]
    exact (AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩).symm

中文:
引理 restrict_fixedField
  条件: (H : 子群 Gal(K/k)) (L : 中间域 k K) [正规 k L]
  证明: by
  apply SetLike.ext'
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have xL := h.out.2
    apply (mem_lift (⟨x, xL⟩ : L)).mpr
    simp only [mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro σ hσ
    apply Subtype.val_injective
    dsimp only
    nth_rw 2 [← (h.out.1 ⟨σ, hσ⟩)]
    exact AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩
  · have xL := lift_le _ h
    apply (mem_lift (⟨x, xL⟩ : L)).mp at h
    simp only [mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h
    simp only [coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_fixedField_iff, xL, and_true]
    intro σ hσ
    have : ((restrictNormalHom L σ) ⟨x, xL⟩).1 = x := by rw [h σ hσ]
    nth_rw 2 [← this]
    exact (AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.restrictNormal_commutes, SetLike, SetLike.ext, Subgroup, Subgroup.mem_map, Subtype, Subtype.val_injective, and_imp, forall_exists_index, h.out, lift_le, mem_fixedField_iff, mem_lift, mem_map, nth_rw, restrictNormal_commutes, val_injective
-/
lemma restrict_fixedField (H : Subgroup Gal(K/k)) (L : IntermediateField k K) [Normal k L] :
    fixedField H ⊓ L = lift (fixedField (Subgroup.map (restrictNormalHom L) H)) := by
  apply SetLike.ext'
  ext x
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have xL := h.out.2
    apply (mem_lift (⟨x, xL⟩ : L)).mpr
    simp only [mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂]
    intro σ hσ
    apply Subtype.val_injective
    dsimp only
    nth_rw 2 [← (h.out.1 ⟨σ, hσ⟩)]
    exact AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩
  · have xL := lift_le _ h
    apply (mem_lift (⟨x, xL⟩ : L)).mp at h
    simp only [mem_fixedField_iff, Subgroup.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at h
    simp only [coe_inf, Set.mem_inter_iff, SetLike.mem_coe, mem_fixedField_iff, xL, and_true]
    intro σ hσ
    have : ((restrictNormalHom L σ) ⟨x, xL⟩).1 = x := by rw [h σ hσ]
    nth_rw 2 [← this]
    exact (AlgEquiv.restrictNormal_commutes σ L ⟨x, xL⟩).symm

open IntermediateField in
/--
lemma `fixingSubgroup_fixedField` / 引理 `fixingSubgroup_fixedField`

English:
lemma fixingSubgroup_fixedField
  given: (H : ClosedSubgroup Gal(K/k)) [IsGalois k K]
  proof: by
  apply le_antisymm _ ((IntermediateField.le_iff_le H.toSubgroup
    (IntermediateField.fixedField H.toSubgroup)).mp le_rfl)
  intro σ hσ
  by_contra h
  have nhds : H.carrierᶜ in nhds σ := H.isClosed'.isOpen_compl.mem_nhds h
  rw [GroupFilterBasis.nhds_eq (x₀ := σ) (galGroupBasis k K)] at nhds
  rcases nhds with ⟨b, ⟨gp, ⟨L, hL, eq'⟩, eq⟩, sub⟩
  rw [← eq'] at eq
  have := hL.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k L K with
    finiteDimensional := normalClosure.is_finiteDimensional k L K
    isGalois := IsGalois.normalClosure k L K }
  have compl : σ • L'.1.fixingSubgroup.carrier subseteq H.carrierᶜ := by
    rintro φ ⟨τ, hτ, muleq⟩
    have sub' : σ • b subseteq H.carrierᶜ := Set.smul_set_subset_iff.mpr sub
    apply sub'
    simp only [← muleq, ← eq]
    apply Set.smul_mem_smul_set
    exact (L.fixingSubgroup_le (IntermediateField.le_normalClosure L) hτ)
  have fix : forall x in IntermediateField.fixedField H.toSubgroup ⊓ ↑L', σ x = x :=
    fun x hx => ((mem_fixingSubgroup_iff Gal(K/k)).mp hσ) x hx.1
  rw [restrict_fixedField H.1 L'.1] at fix
  have : (restrictNormalHom L') σ in (Subgroup.map (restrictNormalHom L') H.1) := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.map (restrictNormalHom L') H.1)]
    apply (mem_fixingSubgroup_iff (L' ≃ₐ[k] L')).mpr
    intro y hy
    apply Subtype.val_injective
    simp only [AlgEquiv.smul_def, restrictNormalHom_apply L'.1 σ y,
      fix y.1 ((IntermediateField.mem_lift y).mpr hy)]
  rcases this with ⟨h, mem, eq⟩
  have : h in σ • L'.1.fixingSubgroup.carrier := by
    use σ⁻¹ * h
    simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
      smul_eq_mul, mul_inv_cancel_left, and_true]
    apply (mem_fixingSubgroup_iff Gal(K/k)).mpr
    intro y hy
    simp only [AlgEquiv.smul_def, AlgEquiv.mul_apply]
    have : ((restrictNormalHom L') h ⟨y,hy⟩).1 = ((restrictNormalHom L') σ ⟨y,hy⟩).1 := by rw [eq]
    rw [restrictNormalHom_apply L'.1 h ⟨y]; rw [hy⟩]; rw [restrictNormalHom_apply L'.1 σ ⟨y]; rw [hy⟩] at this
    simp only [this, ← AlgEquiv.mul_apply, inv_mul_cancel, one_apply]
  absurd compl
  apply Set.not_subset.mpr
  use h
  simpa only [this, Set.mem_compl_iff, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
    Subgroup.mem_toSubmonoid, not_not, true_and] using! mem

中文:
引理 fixingSubgroup_fixedField
  条件: (H : 闭子群 Gal(K/k)) [是Galois k K]
  证明: by
  apply le_antisymm _ ((IntermediateField.le_iff_le H.toSubgroup
    (IntermediateField.fixedField H.toSubgroup)).mp le_rfl)
  intro σ hσ
  by_contra h
  have nhds : H.carrierᶜ in nhds σ := H.isClosed'.isOpen_compl.mem_nhds h
  rw [GroupFilterBasis.nhds_eq (x₀ := σ) (galGroupBasis k K)] at nhds
  rcases nhds with ⟨b, ⟨gp, ⟨L, hL, eq'⟩, eq⟩, sub⟩
  rw [← eq'] at eq
  have := hL.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k L K with
    finiteDimensional := normalClosure.is_finiteDimensional k L K
    isGalois := IsGalois.normalClosure k L K }
  have compl : σ • L'.1.fixingSubgroup.carrier subseteq H.carrierᶜ := by
    rintro φ ⟨τ, hτ, muleq⟩
    have sub' : σ • b subseteq H.carrierᶜ := Set.smul_set_subset_iff.mpr sub
    apply sub'
    simp only [← muleq, ← eq]
    apply Set.smul_mem_smul_set
    exact (L.fixingSubgroup_le (IntermediateField.le_normalClosure L) hτ)
  have fix : forall x in IntermediateField.fixedField H.toSubgroup ⊓ ↑L', σ x = x :=
    fun x hx => ((mem_fixingSubgroup_iff Gal(K/k)).mp hσ) x hx.1
  rw [restrict_fixedField H.1 L'.1] at fix
  have : (restrictNormalHom L') σ in (Subgroup.map (restrictNormalHom L') H.1) := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.map (restrictNormalHom L') H.1)]
    apply (mem_fixingSubgroup_iff (L' ≃ₐ[k] L')).mpr
    intro y hy
    apply Subtype.val_injective
    simp only [AlgEquiv.smul_def, restrictNormalHom_apply L'.1 σ y,
      fix y.1 ((IntermediateField.mem_lift y).mpr hy)]
  rcases this with ⟨h, mem, eq⟩
  have : h in σ • L'.1.fixingSubgroup.carrier := by
    use σ⁻¹ * h
    simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
      smul_eq_mul, mul_inv_cancel_left, and_true]
    apply (mem_fixingSubgroup_iff Gal(K/k)).mpr
    intro y hy
    simp only [AlgEquiv.smul_def, AlgEquiv.mul_apply]
    have : ((restrictNormalHom L') h ⟨y,hy⟩).1 = ((restrictNormalHom L') σ ⟨y,hy⟩).1 := by rw [eq]
    rw [restrictNormalHom_apply L'.1 h ⟨y]; rw [hy⟩]; rw [restrictNormalHom_apply L'.1 σ ⟨y]; rw [hy⟩] at this
    simp only [this, ← AlgEquiv.mul_apply, inv_mul_cancel, one_apply]
  absurd compl
  apply Set.not_subset.mpr
  use h
  simpa only [this, Set.mem_compl_iff, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
    Subgroup.mem_toSubmonoid, not_not, true_and] using! mem

Depends on / 依赖: FiniteGaloisIntermediateField, GroupFilterBasis, GroupFilterBasis.nhds_eq, H.carrier, H.isClosed, H.toSubgroup, IntermediateField, IntermediateField.fixedField, IntermediateField.le_iff_le, finiteDimensional, fixedField, galGroupBasis, hL.out, isClosed, isOpen_compl, isOpen_compl.mem_nhds, is_finiteDimensional, le_antisymm, le_iff_le, le_rfl
-/
lemma fixingSubgroup_fixedField (H : ClosedSubgroup Gal(K/k)) [IsGalois k K] :
    (IntermediateField.fixedField H).fixingSubgroup = H.1 := by
  apply le_antisymm _ ((IntermediateField.le_iff_le H.toSubgroup
    (IntermediateField.fixedField H.toSubgroup)).mp le_rfl)
  intro σ hσ
  by_contra h
  have nhds : H.carrierᶜ in nhds σ := H.isClosed'.isOpen_compl.mem_nhds h
  rw [GroupFilterBasis.nhds_eq (x₀ := σ) (galGroupBasis k K)] at nhds
  rcases nhds with ⟨b, ⟨gp, ⟨L, hL, eq'⟩, eq⟩, sub⟩
  rw [← eq'] at eq
  have := hL.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k L K with
    finiteDimensional := normalClosure.is_finiteDimensional k L K
    isGalois := IsGalois.normalClosure k L K }
  have compl : σ • L'.1.fixingSubgroup.carrier subseteq H.carrierᶜ := by
    rintro φ ⟨τ, hτ, muleq⟩
    have sub' : σ • b subseteq H.carrierᶜ := Set.smul_set_subset_iff.mpr sub
    apply sub'
    simp only [← muleq, ← eq]
    apply Set.smul_mem_smul_set
    exact (L.fixingSubgroup_le (IntermediateField.le_normalClosure L) hτ)
  have fix : forall x in IntermediateField.fixedField H.toSubgroup ⊓ ↑L', σ x = x :=
    fun x hx => ((mem_fixingSubgroup_iff Gal(K/k)).mp hσ) x hx.1
  rw [restrict_fixedField H.1 L'.1] at fix
  have : (restrictNormalHom L') σ in (Subgroup.map (restrictNormalHom L') H.1) := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.map (restrictNormalHom L') H.1)]
    apply (mem_fixingSubgroup_iff (L' ≃ₐ[k] L')).mpr
    intro y hy
    apply Subtype.val_injective
    simp only [AlgEquiv.smul_def, restrictNormalHom_apply L'.1 σ y,
      fix y.1 ((IntermediateField.mem_lift y).mpr hy)]
  rcases this with ⟨h, mem, eq⟩
  have : h in σ • L'.1.fixingSubgroup.carrier := by
    use σ⁻¹ * h
    simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid,
      smul_eq_mul, mul_inv_cancel_left, and_true]
    apply (mem_fixingSubgroup_iff Gal(K/k)).mpr
    intro y hy
    simp only [AlgEquiv.smul_def, AlgEquiv.mul_apply]
    have : ((restrictNormalHom L') h ⟨y,hy⟩).1 = ((restrictNormalHom L') σ ⟨y,hy⟩).1 := by rw [eq]
    rw [restrictNormalHom_apply L'.1 h ⟨y]; rw [hy⟩]; rw [restrictNormalHom_apply L'.1 σ ⟨y]; rw [hy⟩] at this
    simp only [this, ← AlgEquiv.mul_apply, inv_mul_cancel, one_apply]
  absurd compl
  apply Set.not_subset.mpr
  use h
  simpa only [this, Set.mem_compl_iff, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
    Subgroup.mem_toSubmonoid, not_not, true_and] using! mem

/--
Definition of `IntermediateFieldEquivClosedSubgroup` / `IntermediateFieldEquivClosedSubgroup` 的定义

English:
definition IntermediateFieldEquivClosedSubgroup
  signature: [IsGalois k K]
  body: ⟨L.fixingSubgroup, fixingSubgroup_isClosed L⟩
  invFun H := IntermediateField.fixedField H.1
  left_inv L := fixedField_fixingSubgroup L
  right_inv H := by
    simp_rw [fixingSubgroup_fixedField H]
    rfl
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L]; rw [IntermediateField.le_iff_le]; rw [fixedField_fixingSubgroup L]
    rfl

中文:
定义 整数ermediateFieldEquivClosedSubgroup
  签名: [是Galois k K]
  定义体: ⟨L.fixingSubgroup, fixingSubgroup_isClosed L⟩
  invFun H := IntermediateField.fixedField H.1
  left_inv L := fixedField_fixingSubgroup L
  right_inv H := by
    simp_rw [fixingSubgroup_fixedField H]
    rfl
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L]; rw [IntermediateField.le_iff_le]; rw [fixedField_fixingSubgroup L]
    rfl

Depends on / 依赖: L.fixingSubgroup, fixingSubgroup, fixingSubgroup_isClosed
-/
def IntermediateFieldEquivClosedSubgroup [IsGalois k K] :
    IntermediateField k K ≃o (ClosedSubgroup Gal(K/k))ᵒᵈ where
  toFun L := ⟨L.fixingSubgroup, fixingSubgroup_isClosed L⟩
  invFun H := IntermediateField.fixedField H.1
  left_inv L := fixedField_fixingSubgroup L
  right_inv H := by
    simp_rw [fixingSubgroup_fixedField H]
    rfl
  map_rel_iff' {K L} := by
    rw [← fixedField_fixingSubgroup L]; rw [IntermediateField.le_iff_le]; rw [fixedField_fixingSubgroup L]
    rfl

/--
Definition of `GaloisInsertionIntermediateFieldClosedSubgroup` / `GaloisInsertionIntermediateFieldClosedSubgroup` 的定义

English:
definition GaloisInsertionIntermediateFieldClosedSubgroup
  signature: [IsGalois k K]
  body: OrderIso.toGaloisInsertion IntermediateFieldEquivClosedSubgroup

中文:
定义 GaloisInsertion整数ermediateFieldClosedSubgroup
  签名: [是Galois k K]
  定义体: OrderIso.toGaloisInsertion IntermediateFieldEquivClosedSubgroup

Depends on / 依赖: IntermediateFieldEquivClosedSubgroup, OrderIso, OrderIso.toGaloisInsertion, toGaloisInsertion
-/
def GaloisInsertionIntermediateFieldClosedSubgroup [IsGalois k K] :
    GaloisInsertion (OrderDual.toDual ∘ fun (E : IntermediateField k K) =>
      (⟨E.fixingSubgroup, fixingSubgroup_isClosed E⟩ : ClosedSubgroup Gal(K/k)))
      ((fun (H : ClosedSubgroup Gal(K/k)) => IntermediateField.fixedField H) ∘
        OrderDual.toDual) :=
  OrderIso.toGaloisInsertion IntermediateFieldEquivClosedSubgroup

/--
Definition of `GaloisCoinsertionIntermediateFieldSubgroup` / `GaloisCoinsertionIntermediateFieldSubgroup` 的定义

English:
definition GaloisCoinsertionIntermediateFieldSubgroup
  signature: [IsGalois k K]
  body: IntermediateField.fixedField H
  gc E H := (IntermediateField.le_iff_le H E).symm
  u_l_le K := le_of_eq (fixedField_fixingSubgroup K)
  choice_eq _ _ := rfl

中文:
定义 GaloisCoinsertion整数ermediateFieldSubgroup
  签名: [是Galois k K]
  定义体: IntermediateField.fixedField H
  gc E H := (IntermediateField.le_iff_le H E).symm
  u_l_le K := le_of_eq (fixedField_fixingSubgroup K)
  choice_eq _ _ := rfl

Depends on / 依赖: IntermediateField, IntermediateField.fixedField, fixedField
-/
def GaloisCoinsertionIntermediateFieldSubgroup [IsGalois k K] :
    GaloisCoinsertion (OrderDual.toDual ∘ fun (E : IntermediateField k K) => E.fixingSubgroup)
      ((fun (H : Subgroup Gal(K/k)) => IntermediateField.fixedField H) ∘ OrderDual.toDual) where
  choice H _ := IntermediateField.fixedField H
  gc E H := (IntermediateField.le_iff_le H E).symm
  u_l_le K := le_of_eq (fixedField_fixingSubgroup K)
  choice_eq _ _ := rfl

open IntermediateField in
/--
Definition of `normalAutEquivQuotient` / `normalAutEquivQuotient` 的定义

English:
definition normalAutEquivQuotient
  signature: [IsGalois k K]
  body: QuotientGroup.liftEquiv _ (restrictNormalHom_surjective K)
    ((fixingSubgroup_fixedField H).symm.trans (fixedField H.1).restrictNormalHom_ker.symm)

中文:
定义 normalAutEquivQuotient
  签名: [是Galois k K]
  定义体: QuotientGroup.liftEquiv _ (restrictNormalHom_surjective K)
    ((fixingSubgroup_fixedField H).symm.trans (fixedField H.1).restrictNormalHom_ker.symm)

Depends on / 依赖: QuotientGroup, QuotientGroup.liftEquiv, fixedField, fixingSubgroup_fixedField, liftEquiv, restrictNormalHom_ker, restrictNormalHom_ker.symm, restrictNormalHom_surjective, symm.trans
-/
noncomputable def normalAutEquivQuotient [IsGalois k K]
    (H : ClosedSubgroup Gal(K/k)) [H.Normal] :
    Gal(K/k) ⧸ H.1 ≃* Gal(fixedField H.1/k) :=
  QuotientGroup.liftEquiv _ (restrictNormalHom_surjective K)
    ((fixingSubgroup_fixedField H).symm.trans (fixedField H.1).restrictNormalHom_ker.symm)

open IntermediateField in
/--
lemma `normalAutEquivQuotient_apply` / 引理 `normalAutEquivQuotient_apply`

English:
lemma normalAutEquivQuotient_apply
  statement: [IsGalois k K]
  proof: rfl

中文:
引理 normalAutEquivQuotient_apply
  结论: [是Galois k K]
  证明: rfl
-/
lemma normalAutEquivQuotient_apply [IsGalois k K]
    (H : ClosedSubgroup Gal(K/k)) [H.Normal] (σ : Gal(K/k)) :
    normalAutEquivQuotient H σ = restrictNormalHom (fixedField H.1) σ := rfl

set_option backward.isDefEq.respectTransparency false in
open IntermediateField in
/--
theorem `isOpen_iff_finite` / 定理 `isOpen_iff_finite`

English:
theorem isOpen_iff_finite
  given: (L : IntermediateField k K) [IsGalois k K]
  proof: by
  refine ⟨fun h => ?_, fun h => IntermediateField.fixingSubgroup_isOpen L⟩
  have : (IntermediateFieldEquivClosedSubgroup.toFun L).carrier in nhds 1 :=
    IsOpen.mem_nhds h (congrFun rfl)
  rw [GroupFilterBasis.nhds_one_eq] at this
  rcases this with ⟨S, ⟨gp, ⟨M, hM, eq'⟩, eq⟩, sub⟩
  rw [← eq]; rw [← eq'] at sub
  have := hM.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k M K with
    finiteDimensional := normalClosure.is_finiteDimensional k M K
    isGalois := IsGalois.normalClosure k M K }
  have : L <= L'.1 := by
    apply le_trans _ (IntermediateField.le_normalClosure M)
    rw [← fixedField_fixingSubgroup M]; rw [IntermediateField.le_iff_le]
    exact sub
  let _ : Algebra L L'.1 := RingHom.toAlgebra (IntermediateField.inclusion this)
  exact FiniteDimensional.left k L L'.1

中文:
定理 isOpen_iff_finite
  条件: (L : 中间域 k K) [是Galois k K]
  证明: by
  refine ⟨fun h => ?_, fun h => IntermediateField.fixingSubgroup_isOpen L⟩
  have : (IntermediateFieldEquivClosedSubgroup.toFun L).carrier in nhds 1 :=
    IsOpen.mem_nhds h (congrFun rfl)
  rw [GroupFilterBasis.nhds_one_eq] at this
  rcases this with ⟨S, ⟨gp, ⟨M, hM, eq'⟩, eq⟩, sub⟩
  rw [← eq]; rw [← eq'] at sub
  have := hM.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k M K with
    finiteDimensional := normalClosure.is_finiteDimensional k M K
    isGalois := IsGalois.normalClosure k M K }
  have : L <= L'.1 := by
    apply le_trans _ (IntermediateField.le_normalClosure M)
    rw [← fixedField_fixingSubgroup M]; rw [IntermediateField.le_iff_le]
    exact sub
  let _ : Algebra L L'.1 := RingHom.toAlgebra (IntermediateField.inclusion this)
  exact FiniteDimensional.left k L L'.1

Depends on / 依赖: FiniteGaloisIntermediateField, GroupFilterBasis, GroupFilterBasis.nhds_one_eq, IntermediateField, IntermediateField.fixingSubgroup_isOpen, IntermediateFieldEquivClosedSubgroup, IntermediateFieldEquivClosedSubgroup.toFun, IsGalois, IsGalois.normalClosure, IsOpen, IsOpen.mem_nhds, carrier, finiteDimensional, fixingSubgroup_isOpen, hM.out, isGalois, is_finiteDimensional, mem_nhds, nhds_one_eq, normalClosure
-/
theorem isOpen_iff_finite (L : IntermediateField k K) [IsGalois k K] :
    IsOpen L.fixingSubgroup.carrier ↔ FiniteDimensional k L := by
  refine ⟨fun h => ?_, fun h => IntermediateField.fixingSubgroup_isOpen L⟩
  have : (IntermediateFieldEquivClosedSubgroup.toFun L).carrier in nhds 1 :=
    IsOpen.mem_nhds h (congrFun rfl)
  rw [GroupFilterBasis.nhds_one_eq] at this
  rcases this with ⟨S, ⟨gp, ⟨M, hM, eq'⟩, eq⟩, sub⟩
  rw [← eq]; rw [← eq'] at sub
  have := hM.out
  let L' : FiniteGaloisIntermediateField k K := {
    normalClosure k M K with
    finiteDimensional := normalClosure.is_finiteDimensional k M K
    isGalois := IsGalois.normalClosure k M K }
  have : L <= L'.1 := by
    apply le_trans _ (IntermediateField.le_normalClosure M)
    rw [← fixedField_fixingSubgroup M]; rw [IntermediateField.le_iff_le]
    exact sub
  let _ : Algebra L L'.1 := RingHom.toAlgebra (IntermediateField.inclusion this)
  exact FiniteDimensional.left k L L'.1

/--
theorem `normal_iff_isGalois` / 定理 `normal_iff_isGalois`

English:
theorem normal_iff_isGalois
  given: (L : IntermediateField k K) [IsGalois k K]
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · let g (x : K) := L.fixingSubgroup.map (restrictNormalHom (adjoin k {x}))
let f (x : L) : IntermediateField k K := IntermediateField.lift
IntermediateField.fixedField g x.1
    have (x : K) : (g x).Normal :=
      Subgroup.Normal.map h (restrictNormalHom (adjoin k {x})) (restrictNormalHom_surjective K)
    have (l : L) : Normal k (f l) :=
Normal.of_algEquiv IntermediateField.liftAlgEquiv IntermediateField.fixedField (g l.1)
    have n : Normal k ↥(⨆ l : L, f l) := IntermediateField.normal_iSup k K f
    have : (⨆ l : L, f l) = L := by
      apply le_antisymm
      · apply iSup_le
        intro l
        simpa only [f, g, ← restrict_fixedField L.fixingSubgroup (adjoin k {l.1}),
          fixedField_fixingSubgroup L] using inf_le_left
      · intro l hl
        apply le_iSup f ⟨l, hl⟩
        simpa only [f, g, ← restrict_fixedField L.fixingSubgroup (adjoin k {l}),
          fixedField_fixingSubgroup L, IntermediateField.mem_inf, hl, true_and]
          using adjoin_simple_le_iff.mp le_rfl
    rw [this] at n
    constructor
  · simpa only [IntermediateFieldEquivClosedSubgroup, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
      ← L.restrictNormalHom_ker] using MonoidHom.normal_ker (restrictNormalHom L)

中文:
定理 normal_iff_isGalois
  条件: (L : 中间域 k K) [是Galois k K]
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · let g (x : K) := L.fixingSubgroup.map (restrictNormalHom (adjoin k {x}))
let f (x : L) : IntermediateField k K := IntermediateField.lift
IntermediateField.fixedField g x.1
    have (x : K) : (g x).Normal :=
      Subgroup.Normal.map h (restrictNormalHom (adjoin k {x})) (restrictNormalHom_surjective K)
    have (l : L) : Normal k (f l) :=
Normal.of_algEquiv IntermediateField.liftAlgEquiv IntermediateField.fixedField (g l.1)
    have n : Normal k ↥(⨆ l : L, f l) := IntermediateField.normal_iSup k K f
    have : (⨆ l : L, f l) = L := by
      apply le_antisymm
      · apply iSup_le
        intro l
        simpa only [f, g, ← restrict_fixedField L.fixingSubgroup (adjoin k {l.1}),
          fixedField_fixingSubgroup L] using inf_le_left
      · intro l hl
        apply le_iSup f ⟨l, hl⟩
        simpa only [f, g, ← restrict_fixedField L.fixingSubgroup (adjoin k {l}),
          fixedField_fixingSubgroup L, IntermediateField.mem_inf, hl, true_and]
          using adjoin_simple_le_iff.mp le_rfl
    rw [this] at n
    constructor
  · simpa only [IntermediateFieldEquivClosedSubgroup, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
      ← L.restrictNormalHom_ker] using MonoidHom.normal_ker (restrictNormalHom L)

Depends on / 依赖: Intermediat, IntermediateField, IntermediateField.fixedField, IntermediateField.lift, IntermediateField.liftAlgEquiv, L.fixingSubgroup.map, Normal, Normal.of_algEquiv, Subgroup, Subgroup.Normal.map, adjoin, fixedField, fixingSubgroup, liftAlgEquiv, of_algEquiv, restrictNormalHom, restrictNormalHom_surjective
-/
theorem normal_iff_isGalois (L : IntermediateField k K) [IsGalois k K] :
    L.fixingSubgroup.Normal ↔ IsGalois k L := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · let g (x : K) := L.fixingSubgroup.map (restrictNormalHom (adjoin k {x}))
let f (x : L) : IntermediateField k K := IntermediateField.lift
IntermediateField.fixedField g x.1
    have (x : K) : (g x).Normal :=
      Subgroup.Normal.map h (restrictNormalHom (adjoin k {x})) (restrictNormalHom_surjective K)
    have (l : L) : Normal k (f l) :=
Normal.of_algEquiv IntermediateField.liftAlgEquiv IntermediateField.fixedField (g l.1)
    have n : Normal k ↥(⨆ l : L, f l) := IntermediateField.normal_iSup k K f
    have : (⨆ l : L, f l) = L := by
      apply le_antisymm
      · apply iSup_le
        intro l
        simpa only [f, g, ← restrict_fixedField L.fixingSubgroup (adjoin k {l.1}),
          fixedField_fixingSubgroup L] using inf_le_left
      · intro l hl
        apply le_iSup f ⟨l, hl⟩
        simpa only [f, g, ← restrict_fixedField L.fixingSubgroup (adjoin k {l}),
          fixedField_fixingSubgroup L, IntermediateField.mem_inf, hl, true_and]
          using adjoin_simple_le_iff.mp le_rfl
    rw [this] at n
    constructor
  · simpa only [IntermediateFieldEquivClosedSubgroup, RelIso.coe_fn_mk, Equiv.coe_fn_mk,
      ← L.restrictNormalHom_ker] using MonoidHom.normal_ker (restrictNormalHom L)

/--
theorem `isOpen_and_normal_iff_finite_and_isGalois` / 定理 `isOpen_and_normal_iff_finite_and_isGalois`

English:
theorem isOpen_and_normal_iff_finite_and_isGalois
  given: (L : IntermediateField k K) [IsGalois k K]
  proof: by
  rw [isOpen_iff_finite]; rw [normal_iff_isGalois]

中文:
定理 isOpen_and_normal_iff_finite_and_isGalois
  条件: (L : 中间域 k K) [是Galois k K]
  证明: by
  rw [isOpen_iff_finite]; rw [normal_iff_isGalois]

Depends on / 依赖: isOpen_iff_finite, normal_iff_isGalois
-/
theorem isOpen_and_normal_iff_finite_and_isGalois (L : IntermediateField k K) [IsGalois k K] :
    IsOpen L.fixingSubgroup.carrier ∧ L.fixingSubgroup.Normal ↔
    FiniteDimensional k L ∧ IsGalois k L := by
  rw [isOpen_iff_finite]; rw [normal_iff_isGalois]

end InfiniteGalois
