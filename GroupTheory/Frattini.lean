/-
Copyright (c) 2024 Colva Roney-Dougal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colva Roney-Dougal, Inna Capdeboscq, Susanna Fishel, Kim Morrison
-/
module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Order.Radical

/-!
# The Frattini subgroup

We give the definition of the Frattini subgroup of a group, and three elementary results:
* The Frattini subgroup is characteristic.
* If every subgroup of a group is contained in a maximal subgroup, then
  the Frattini subgroup consists of the non-generating elements of the group.
* The Frattini subgroup of a finite group is nilpotent.
-/

@[expose] public section

/--
Definition of `frattini` / `frattini` 的定义

English:
definition frattini
  signature: (G : Type*) [Group G]
  body: Order.radical (Subgroup G)

中文:
定义 frattini
  签名: (G : 类型) [群 G]
  定义体: Order.radical (Subgroup G)

Depends on / 依赖: Order.radical, Subgroup, radical
-/
def frattini (G : Type*) [Group G] : Subgroup G :=
  Order.radical (Subgroup G)

variable {G H : Type*} [Group G] [Group H] {φ : G ->* H}

/--
lemma `frattini_le_coatom` / 引理 `frattini_le_coatom`

English:
lemma frattini_le_coatom
  given: {K : Subgroup G} (h : IsCoatom K)
  statement: frattini G <= K
  proof: Order.radical_le_coatom h

中文:
引理 frattini_le_coatom
  条件: {K : 子群 G} (h : IsCoatom K)
  结论: frattini G <= K
  证明: Order.radical_le_coatom h

Depends on / 依赖: Order.radical_le_coatom, radical_le_coatom
-/
lemma frattini_le_coatom {K : Subgroup G} (h : IsCoatom K) : frattini G <= K :=
  Order.radical_le_coatom h

open Subgroup

/--
lemma `frattini_le_comap_frattini_of_surjective` / 引理 `frattini_le_comap_frattini_of_surjective`

English:
lemma frattini_le_comap_frattini_of_surjective
  given: (hφ : Function.Surjective φ)
  proof: by
  simp_rw [frattini, Order.radical, comap_iInf, le_iInf_iff]
  intro M hM
  apply biInf_le
  exact isCoatom_comap_of_surjective hφ hM

中文:
引理 frattini_le_comap_frattini_of_surjective
  条件: (hφ : 函数.满射 φ)
  证明: by
  simp_rw [frattini, Order.radical, comap_iInf, le_iInf_iff]
  intro M hM
  apply biInf_le
  exact isCoatom_comap_of_surjective hφ hM

Depends on / 依赖: Order.radical, biInf_le, comap_iInf, frattini, isCoatom_comap_of_surjective, le_iInf_iff, radical, simp_rw
-/
lemma frattini_le_comap_frattini_of_surjective (hφ : Function.Surjective φ) :
    frattini G <= (frattini H).comap φ := by
  simp_rw [frattini, Order.radical, comap_iInf, le_iInf_iff]
  intro M hM
  apply biInf_le
  exact isCoatom_comap_of_surjective hφ hM

/--
Instance `frattini_characteristic` / 实例 `frattini_characteristic`

English:
instance frattini_characteristic
  signature: : (frattini G).Characteristic
  body: by
  rw [characteristic_iff_comap_eq]
  intro φ
  apply φ.comapSubgroup.map_radical

中文:
实例 frattini_characteristic
  签名: : (frattini G).特征
  定义体: by
  rw [characteristic_iff_comap_eq]
  intro φ
  apply φ.comapSubgroup.map_radical

Depends on / 依赖: characteristic_iff_comap_eq, comapSubgroup, comapSubgroup.map_radical, map_radical
-/
instance frattini_characteristic : (frattini G).Characteristic := by
  rw [characteristic_iff_comap_eq]
  intro φ
  apply φ.comapSubgroup.map_radical

/--
theorem `frattini_nongenerating` / 定理 `frattini_nongenerating`

English:
theorem frattini_nongenerating
  statement: [IsCoatomic (Subgroup G)] {K : Subgroup G}
  proof: Order.radical_nongenerating h

中文:
定理 frattini_nongenerating
  结论: [是余原子的 (子群 G)] {K : 子群 G}
  证明: Order.radical_nongenerating h

Depends on / 依赖: Order.radical_nongenerating, radical_nongenerating
-/
theorem frattini_nongenerating [IsCoatomic (Subgroup G)] {K : Subgroup G}
    (h : K ⊔ frattini G = ⊤) : K = ⊤ :=
  Order.radical_nongenerating h

/--
theorem `frattini_nilpotent` / 定理 `frattini_nilpotent`

English:
theorem frattini_nilpotent
  given: [Finite G]
  statement: Group.IsNilpotent (frattini G)
  proof: by
  -- We use the characterisation of nilpotency in terms of all Sylow subgroups being normal.
  have q := (Group.isNilpotent_of_finite_tfae (G := frattini G)).out 0 3
  rw [q]; clear q
  -- Consider each prime `p` and Sylow `p`-subgroup `P` of `frattini G`.
  intro p p_prime P
  -- The Frattini argument shows that the normalizer of `P` in `G`
  -- together with `frattini G` generates `G`.
  have frattini_argument := Sylow.normalizer_sup_eq_top P
  -- and hence by the nongenerating property of the Frattini subgroup that
  -- the normalizer of `P` in `G` is `G`.
  have normalizer_P := frattini_nongenerating frattini_argument
  -- This means that `P` is normal as a subgroup of `G`
  have P_normal_in_G : (map (frattini G).subtype P).Normal := normalizer_eq_top_iff.mp normalizer_P
  -- and hence also as a subgroup of `frattini G`, which was the remaining goal.
  exact P_normal_in_G.of_map_subtype

中文:
定理 frattini_nilpotent
  条件: [有限 G]
  结论: 群.是幂零 (frattini G)
  证明: by
  -- We use the characterisation of nilpotency in terms of all Sylow subgroups being normal.
  have q := (Group.isNilpotent_of_finite_tfae (G := frattini G)).out 0 3
  rw [q]; clear q
  -- Consider each prime `p` and Sylow `p`-subgroup `P` of `frattini G`.
  intro p p_prime P
  -- The Frattini argument shows that the normalizer of `P` in `G`
  -- together with `frattini G` generates `G`.
  have frattini_argument := Sylow.normalizer_sup_eq_top P
  -- and hence by the nongenerating property of the Frattini subgroup that
  -- the normalizer of `P` in `G` is `G`.
  have normalizer_P := frattini_nongenerating frattini_argument
  -- This means that `P` is normal as a subgroup of `G`
  have P_normal_in_G : (map (frattini G).subtype P).Normal := normalizer_eq_top_iff.mp normalizer_P
  -- and hence also as a subgroup of `frattini G`, which was the remaining goal.
  exact P_normal_in_G.of_map_subtype
-/
theorem frattini_nilpotent [Finite G] : Group.IsNilpotent (frattini G) := by
  -- We use the characterisation of nilpotency in terms of all Sylow subgroups being normal.
  have q := (Group.isNilpotent_of_finite_tfae (G := frattini G)).out 0 3
  rw [q]; clear q
  -- Consider each prime `p` and Sylow `p`-subgroup `P` of `frattini G`.
  intro p p_prime P
  -- The Frattini argument shows that the normalizer of `P` in `G`
  -- together with `frattini G` generates `G`.
  have frattini_argument := Sylow.normalizer_sup_eq_top P
  -- and hence by the nongenerating property of the Frattini subgroup that
  -- the normalizer of `P` in `G` is `G`.
  have normalizer_P := frattini_nongenerating frattini_argument
  -- This means that `P` is normal as a subgroup of `G`
  have P_normal_in_G : (map (frattini G).subtype P).Normal := normalizer_eq_top_iff.mp normalizer_P
  -- and hence also as a subgroup of `frattini G`, which was the remaining goal.
  exact P_normal_in_G.of_map_subtype
