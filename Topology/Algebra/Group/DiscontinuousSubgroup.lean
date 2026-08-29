/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.GroupTheory.Commensurable
public import Mathlib.GroupTheory.Complement
public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Properly discontinuous actions of subgroups
-/

open Topology Pointwise Filter Set TopologicalSpace Subgroup

public section

variable {Γ α : Type*} [Group Γ] [TopologicalSpace α]

@[to_additive]
/--
lemma `Subgroup.properlyDiscontinuousSMul_iff` / 引理 `Subgroup.properlyDiscontinuousSMul_iff`

English:
lemma Subgroup.properlyDiscontinuousSMul_iff
  proof: by
  rw [properlyDiscontinuousSMul_iff]
  congr! with K L hK hL
.bijOn_image.finite_iff_finite convert! injOn_subtype_val (s := {m : S | (m • K inter L).Nonempty})
  ext g
  simp [Set.subtype_smul_set, and_comm]

@[to_additive]

中文:
引理 子群.properlyDiscontinuousSMul_iff
  证明: by
  rw [properlyDiscontinuousSMul_iff]
  congr! with K L hK hL
.bijOn_image.finite_iff_finite convert! injOn_subtype_val (s := {m : S | (m • K inter L).Nonempty})
  ext g
  simp [Set.subtype_smul_set, and_comm]

@[to_additive]
-/
protected lemma Subgroup.properlyDiscontinuousSMul_iff
    [SMul Γ α] (S : Subgroup Γ) : ProperlyDiscontinuousSMul S α ↔ forall {K L : Set α},
      IsCompact K -> IsCompact L -> {g : Γ | g in S ∧ (g • K inter L).Nonempty}.Finite := by
  rw [properlyDiscontinuousSMul_iff]
  congr! with K L hK hL
.bijOn_image.finite_iff_finite convert! injOn_subtype_val (s := {m : S | (m • K inter L).Nonempty})
  ext g
  simp [Set.subtype_smul_set, and_comm]

@[to_additive]
/--
lemma `Subgroup.properlyDiscontinuousSMul_of_le` / 引理 `Subgroup.properlyDiscontinuousSMul_of_le`

English:
lemma Subgroup.properlyDiscontinuousSMul_of_le
  proof: by
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hG ⊢
  intro K L hK hL
  exact (hG hK hL).subset fun _ ⟨hg, hg'⟩ => ⟨hGH hg, hg'⟩

中文:
引理 子群.properlyDiscontinuousSMul_of_le
  证明: by
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hG ⊢
  intro K L hK hL
  exact (hG hK hL).subset fun _ ⟨hg, hg'⟩ => ⟨hGH hg, hg'⟩

Depends on / 依赖: Subgroup, Subgroup.properlyDiscontinuousSMul_iff, UniformOnFun, UniformOnFun.uniformEquivUniformFun, completeSpace_iff, mem_singleton, properlyDiscontinuousSMul_iff, subset, uniformEquivUniformFun
-/
lemma Subgroup.properlyDiscontinuousSMul_of_le
    [SMul Γ α] {G H : Subgroup Γ} (hG : ProperlyDiscontinuousSMul G α) (hGH : H <= G) :
    ProperlyDiscontinuousSMul H α := by
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hG ⊢
  intro K L hK hL
  exact (hG hK hL).subset fun _ ⟨hg, hg'⟩ => ⟨hGH hg, hg'⟩

/-- If `Γ` acts properly discontinuously, so does every subgroup of `Γ`. -/
@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: Γ α] [ProperlyDiscontinuousSMul Γ α] (G
  body: by
  refine Subgroup.properlyDiscontinuousSMul_of_le ?_ le_top
  simp only [Subgroup.properlyDiscontinuousSMul_iff, Subgroup.mem_top, true_and]
  exact finite_disjoint_inter_image

中文:
实例 [标量乘法
  签名: Γ α] [ProperlyDiscontinuousSMul Γ α] (G
  定义体: by
  refine Subgroup.properlyDiscontinuousSMul_of_le ?_ le_top
  simp only [Subgroup.properlyDiscontinuousSMul_iff, Subgroup.mem_top, true_and]
  exact finite_disjoint_inter_image

Depends on / 依赖: Subgroup, Subgroup.mem_top, Subgroup.properlyDiscontinuousSMul_iff, Subgroup.properlyDiscontinuousSMul_of_le, finite_disjoint_inter_image, le_top, mem_top, properlyDiscontinuousSMul_iff, properlyDiscontinuousSMul_of_le, true_and
-/
instance [SMul Γ α] [ProperlyDiscontinuousSMul Γ α] (G : Subgroup Γ) :
    ProperlyDiscontinuousSMul G α := by
  refine Subgroup.properlyDiscontinuousSMul_of_le ?_ le_top
  simp only [Subgroup.properlyDiscontinuousSMul_iff, Subgroup.mem_top, true_and]
  exact finite_disjoint_inter_image

open Pointwise in
/-- If `G, H` are subgroups of `Γ` which acts on `α`, and `G ∩ H` has finite index in `G`,
then `G` acts properly discontinuously if `H` does. -/
@[to_additive]
/--
lemma `ProperlyDiscontinuousSMul.ofFiniteRelIndex` / 引理 `ProperlyDiscontinuousSMul.ofFiniteRelIndex`

English:
lemma ProperlyDiscontinuousSMul.ofFiniteRelIndex
  statement: [MulAction Γ α] [ContinuousConstSMul Γ α]
  proof: by
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hH ⊢
  intro K L hK hL
  have (t : Γ) : {g | g in H ∧ (g • t • K inter L).Nonempty}.Finite :=
    hH (hK.image <| continuous_const_smul t) hL
  obtain ⟨S, hS, -⟩ := (H.subgroupOf G).exists_isComplement_right 1
  have hT : (Subtype.val '' S).Finite 

中文:
引理 ProperlyDiscontinuousSMul.ofFiniteRelIndex
  结论: [乘法作用 Γ α] [连续常数标量乘法 Γ α]
  证明: by
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hH ⊢
  intro K L hK hL
  have (t : Γ) : {g | g in H ∧ (g • t • K inter L).Nonempty}.Finite :=
    hH (hK.image <| continuous_const_smul t) hL
  obtain ⟨S, hS, -⟩ := (H.subgroupOf G).exists_isComplement_right 1
  have hT : (Subtype.val '' S).Finite 

Depends on / 依赖: Finite, Fintype, H.subgroupOf, Nonempty, Subgroup, Subgroup.fintypeQuotientOfFiniteIndex, Subgroup.properlyDiscontinuousSMul_iff, Subtyp, Subtype, Subtype.val, continuous_const_smul, exists_isComplement_right, fintypeQuotientOfFiniteIndex, hK.image, hS.rightQuotientEquiv, ofEquiv, properlyDiscontinuousSMul_iff, rightQuotientEquiv, subgroupOf, toFinite
-/
lemma ProperlyDiscontinuousSMul.ofFiniteRelIndex [MulAction Γ α] [ContinuousConstSMul Γ α]
    (G H : Subgroup Γ) [hH : ProperlyDiscontinuousSMul H α] [H.IsFiniteRelIndex G] :
    ProperlyDiscontinuousSMul G α := by
  rw [Subgroup.properlyDiscontinuousSMul_iff] at hH ⊢
  intro K L hK hL
  have (t : Γ) : {g | g in H ∧ (g • t • K inter L).Nonempty}.Finite :=
    hH (hK.image <| continuous_const_smul t) hL
  obtain ⟨S, hS, -⟩ := (H.subgroupOf G).exists_isComplement_right 1
  have hT : (Subtype.val '' S).Finite := by
    have : Fintype (G ⧸ H.subgroupOf G) := Subgroup.fintypeQuotientOfFiniteIndex
    have : Fintype S := .ofEquiv _ hS.rightQuotientEquiv
    exact (toFinite S).image _
  have hS' {g : Γ} (hg : g in G) : exists t in Subtype.val '' S, g * t⁻¹ in H := by
    obtain ⟨p, hp⟩ := (hS.existsUnique ⟨g, hg⟩).exists
    aesop
  refine (hT.biUnion <| fun t ht => (this t).map fun g => g * t).subset fun g => ?_
  simp [mul_smul]
  grind

@[to_additive]
/--
lemma `Subgroup.properlyDiscontinuousSMul_iff_of_isFiniteRelIndex` / 引理 `Subgroup.properlyDiscontinuousSMul_iff_of_isFiniteRelIndex`

English:
lemma Subgroup.properlyDiscontinuousSMul_iff_of_isFiniteRelIndex
  proof: ⟨fun _ => .ofFiniteRelIndex H G, (properlyDiscontinuousSMul_of_le · hGH)⟩

@[to_additive]

中文:
引理 子群.properlyDiscontinuousSMul_iff_of_isFiniteRelIndex
  证明: ⟨fun _ => .ofFiniteRelIndex H G, (properlyDiscontinuousSMul_of_le · hGH)⟩

@[to_additive]

Depends on / 依赖: ofFiniteRelIndex, properlyDiscontinuousSMul_of_le
-/
lemma Subgroup.properlyDiscontinuousSMul_iff_of_isFiniteRelIndex
    [MulAction Γ α] [ContinuousConstSMul Γ α]
    {G H : Subgroup Γ} (hGH : G <= H) [IsFiniteRelIndex G H] :
    ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul H α :=
  ⟨fun _ => .ofFiniteRelIndex H G, (properlyDiscontinuousSMul_of_le · hGH)⟩

@[to_additive]
/--
lemma `Subgroup.Commensurable.properlyDiscontinuousSMul_iff` / 引理 `Subgroup.Commensurable.properlyDiscontinuousSMul_iff`

English:
lemma Subgroup.Commensurable.properlyDiscontinuousSMul_iff
  proof: by
  have : IsFiniteRelIndex (G ⊓ H) H := ⟨Subgroup.inf_relIndex_right G H ▸ h.1⟩
  have : IsFiniteRelIndex (G ⊓ H) G := ⟨Subgroup.inf_relIndex_left G H ▸ h.2⟩
  calc ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul ↑(G ⊓ H) α :=
    (properlyDiscontinuousSMul_iff_of_isFiniteRelIndex inf_le

中文:
引理 子群.Commensurable.properlyDiscontinuousSMul_iff
  证明: by
  have : IsFiniteRelIndex (G ⊓ H) H := ⟨Subgroup.inf_relIndex_right G H ▸ h.1⟩
  have : IsFiniteRelIndex (G ⊓ H) G := ⟨Subgroup.inf_relIndex_left G H ▸ h.2⟩
  calc ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul ↑(G ⊓ H) α :=
    (properlyDiscontinuousSMul_iff_of_isFiniteRelIndex inf_le

Depends on / 依赖: IsFiniteRelIndex, ProperlyDiscontinuousSMul, Subgroup, Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_right, inf_le_left, inf_le_right, inf_relIndex_left, inf_relIndex_right, properlyDiscontinuousSMul_iff_of_isFiniteRelIndex
-/
lemma Subgroup.Commensurable.properlyDiscontinuousSMul_iff
    [MulAction Γ α] [ContinuousConstSMul Γ α]
    {G H : Subgroup Γ} (h : G.Commensurable H) :
    ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul H α := by
  have : IsFiniteRelIndex (G ⊓ H) H := ⟨Subgroup.inf_relIndex_right G H ▸ h.1⟩
  have : IsFiniteRelIndex (G ⊓ H) G := ⟨Subgroup.inf_relIndex_left G H ▸ h.2⟩
  calc ProperlyDiscontinuousSMul G α ↔ ProperlyDiscontinuousSMul ↑(G ⊓ H) α :=
    (properlyDiscontinuousSMul_iff_of_isFiniteRelIndex inf_le_left).symm
  _ ↔ ProperlyDiscontinuousSMul H α :=
    properlyDiscontinuousSMul_iff_of_isFiniteRelIndex inf_le_right

end
