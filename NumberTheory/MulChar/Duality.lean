/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.GroupTheory.FiniteAbelian.Duality
public import Mathlib.NumberTheory.MulChar.Lemmas

/-!
# Duality for multiplicative characters

Let `M` be a finite commutative monoid and `R` a ring that has enough `n`th roots of unity,
where `n` is the exponent of `M`. Then the main results of this file are as follows.

## Main results

* `MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity`: multiplicative characters
  `M → R` separate elements of `Mˣ`.

* `MulChar.mulEquiv_units`: the group of multiplicative characters `M → R` is
  (noncanonically) isomorphic to `Mˣ`.

* `MulChar.mulCharEquiv`: the `MulEquiv` between the double dual `MulChar (MulChar M R) R` of `M`
  and `Mˣ`.

* `MulChar.subgroupOrderIsoSubgroupMulChar`: The order reversing bijection that sends a
  subgroup of `Mˣ` to its dual subgroup in `MulChar M R`.

-/

@[expose] public section

namespace MulChar

variable {M R : Type*} [CommMonoid M] [CommRing R]

/--
Instance `finite` / 实例 `finite`

English:
instance finite
  signature: [Finite Mˣ] [IsDomain R]
  body: .of_equiv _ equivToUnitHom.symm

中文:
实例 finite
  签名: [有限 Mˣ] [是整环 R]
  定义体: .of_equiv _ equivToUnitHom.symm

Depends on / 依赖: equivToUnitHom, equivToUnitHom.symm, of_equiv
-/
instance finite [Finite Mˣ] [IsDomain R] : Finite (MulChar M R) := .of_equiv _ equivToUnitHom.symm

/--
lemma `exists_apply_ne_one_iff_exists_monoidHom` / 引理 `exists_apply_ne_one_iff_exists_monoidHom`

English:
lemma exists_apply_ne_one_iff_exists_monoidHom
  given: (a : Mˣ)
  proof: by
  refine ⟨fun ⟨χ, hχ⟩ => ⟨χ.toUnitHom, ?_⟩, fun ⟨φ, hφ⟩ => ⟨ofUnitHom φ, ?_⟩⟩
  · contrapose hχ
    rwa [Units.ext_iff, coe_toUnitHom] at hχ
  · contrapose hφ
    simpa only [ofUnitHom_eq, equivToUnitHom_symm_coe, Units.val_eq_one] using hφ

中文:
引理 存在_apply_ne_one_iff_存在_monoidHom
  条件: (a : Mˣ)
  证明: by
  refine ⟨fun ⟨χ, hχ⟩ => ⟨χ.toUnitHom, ?_⟩, fun ⟨φ, hφ⟩ => ⟨ofUnitHom φ, ?_⟩⟩
  · contrapose hχ
    rwa [Units.ext_iff, coe_toUnitHom] at hχ
  · contrapose hφ
    simpa only [ofUnitHom_eq, equivToUnitHom_symm_coe, Units.val_eq_one] using hφ

Depends on / 依赖: Units.ext_iff, Units.val_eq_one, coe_toUnitHom, contrapose, equivToUnitHom_symm_coe, ext_iff, ofUnitHom, ofUnitHom_eq, toUnitHom, val_eq_one
-/
lemma exists_apply_ne_one_iff_exists_monoidHom (a : Mˣ) :
    (exists χ : MulChar M R, χ a != 1) ↔ exists φ : Mˣ ->* Rˣ, φ a != 1 := by
  refine ⟨fun ⟨χ, hχ⟩ => ⟨χ.toUnitHom, ?_⟩, fun ⟨φ, hφ⟩ => ⟨ofUnitHom φ, ?_⟩⟩
  · contrapose hχ
    rwa [Units.ext_iff, coe_toUnitHom] at hχ
  · contrapose hφ
    simpa only [ofUnitHom_eq, equivToUnitHom_symm_coe, Units.val_eq_one] using hφ

variable (M R)
variable [Finite M] [HasEnoughRootsOfUnity R (Monoid.exponent Mˣ)]

/--
theorem `exists_apply_ne_one_of_hasEnoughRootsOfUnity` / 定理 `exists_apply_ne_one_of_hasEnoughRootsOfUnity`

English:
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity
  given: [Nontrivial R] {a : M} (ha : a != 1)
  proof: by
  by_cases hu : IsUnit a
  · refine (exists_apply_ne_one_iff_exists_monoidHom hu.unit).mpr ?_
    refine CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Mˣ R ?_
    contrapose ha
    rw [← hu.unit_spec]; rw [ha]; rw [Units.val_eq_one]
  · exact ⟨1, by simpa only [map_nonunit _ hu] using zero_ne_one⟩

中文:
定理 存在_apply_ne_one_of_hasEnoughRootsOfUnity
  条件: [非平凡 R] {a : M} (ha : a != 1)
  证明: by
  by_cases hu : IsUnit a
  · refine (exists_apply_ne_one_iff_exists_monoidHom hu.unit).mpr ?_
    refine CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Mˣ R ?_
    contrapose ha
    rw [← hu.unit_spec]; rw [ha]; rw [Units.val_eq_one]
  · exact ⟨1, by simpa only [map_nonunit _ hu] using zero_ne_one⟩

Depends on / 依赖: CommGroup, CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity, IsUnit, Units.val_eq_one, contrapose, exists_apply_ne_one_iff_exists_monoidHom, exists_apply_ne_one_of_hasEnoughRootsOfUnity, hu.unit, hu.unit_spec, map_nonunit, unit_spec, val_eq_one, zero_ne_one
-/
theorem exists_apply_ne_one_of_hasEnoughRootsOfUnity [Nontrivial R] {a : M} (ha : a != 1) :
    exists χ : MulChar M R, χ a != 1 := by
  by_cases hu : IsUnit a
  · refine (exists_apply_ne_one_iff_exists_monoidHom hu.unit).mpr ?_
    refine CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Mˣ R ?_
    contrapose ha
    rw [← hu.unit_spec]; rw [ha]; rw [Units.val_eq_one]
  · exact ⟨1, by simpa only [map_nonunit _ hu] using zero_ne_one⟩

/--
lemma `mulEquiv_units` / 引理 `mulEquiv_units`

English:
lemma mulEquiv_units
  statement: Nonempty (MulChar M R ≃* Mˣ)
  proof: ⟨mulEquivToUnitHom.trans
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Mˣ R).some⟩

中文:
引理 mulEquiv_units
  结论: 非空 (乘法特征 M R ≃* Mˣ)
  证明: ⟨mulEquivToUnitHom.trans
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Mˣ R).some⟩

Depends on / 依赖: CommGroup, CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity, monoidHom_mulEquiv_of_hasEnoughRootsOfUnity, mulEquivToUnitHom, mulEquivToUnitHom.trans
-/
lemma mulEquiv_units : Nonempty (MulChar M R ≃* Mˣ) :=
  ⟨mulEquivToUnitHom.trans
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity Mˣ R).some⟩

/--
lemma `card_eq_card_units_of_hasEnoughRootsOfUnity` / 引理 `card_eq_card_units_of_hasEnoughRootsOfUnity`

English:
lemma card_eq_card_units_of_hasEnoughRootsOfUnity
  statement: Nat.card (MulChar M R) = Nat.card Mˣ
  proof: Nat.card_congr (mulEquiv_units M R).some.toEquiv

中文:
引理 card_eq_card_units_of_hasEnoughRootsOfUnity
  结论: 自然数.card (乘法特征 M R) = 自然数.card Mˣ
  证明: Nat.card_congr (mulEquiv_units M R).some.toEquiv

Depends on / 依赖: Nat.card_congr, card_congr, mulEquiv_units, some.toEquiv, toEquiv
-/
lemma card_eq_card_units_of_hasEnoughRootsOfUnity : Nat.card (MulChar M R) = Nat.card Mˣ :=
  Nat.card_congr (mulEquiv_units M R).some.toEquiv


/--
theorem `domRestrictHom_surjective` / 定理 `domRestrictHom_surjective`

English:
theorem domRestrictHom_surjective
  given: (N : Submonoid M)
  proof: by
  intro χ
  obtain ⟨ψ, hψ⟩ := (χ.toUnitHom.comp N.unitsEquivUnitsType).domRestrict_surjective R N.units
  refine ⟨MulChar.ofUnitHom ψ, ext fun _ => ?_⟩
  rw [MonoidHom.domRestrictHom_apply] at hψ
  rw [domRestrictHom_apply]; rw [domRestrict_ofUnitHom]
  simp [hψ]

@[deprecated (since := "2026-07-19")] alias restrictHom_surjective := domRestrictHom_surjective

中文:
定理 domRestrictHom_surjective
  条件: (N : 子幺半群 M)
  证明: by
  intro χ
  obtain ⟨ψ, hψ⟩ := (χ.toUnitHom.comp N.unitsEquivUnitsType).domRestrict_surjective R N.units
  refine ⟨MulChar.ofUnitHom ψ, ext fun _ => ?_⟩
  rw [MonoidHom.domRestrictHom_apply] at hψ
  rw [domRestrictHom_apply]; rw [domRestrict_ofUnitHom]
  simp [hψ]

@[deprecated (since := "2026-07-19")] alias restrictHom_surjective := domRestrictHom_surjective

Depends on / 依赖: MonoidHom, MonoidHom.domRestrictHom_apply, MulChar, MulChar.ofUnitHom, N.units, N.unitsEquivUnitsType, domRestrictHom_apply, domRestrict_ofUnitHom, domRestrict_surjective, ofUnitHom, toUnitHom, toUnitHom.comp, unitsEquivUnitsType
-/
theorem domRestrictHom_surjective (N : Submonoid M) :
    Function.Surjective (MulChar.domRestrictHom N R) := by
  intro χ
  obtain ⟨ψ, hψ⟩ := (χ.toUnitHom.comp N.unitsEquivUnitsType).domRestrict_surjective R N.units
  refine ⟨MulChar.ofUnitHom ψ, ext fun _ => ?_⟩
  rw [MonoidHom.domRestrictHom_apply] at hψ
  rw [domRestrictHom_apply]; rw [domRestrict_ofUnitHom]
  simp [hψ]

@[deprecated (since := "2026-07-19")] alias restrictHom_surjective := domRestrictHom_surjective

/--
Definition of `mulCharEquiv` / `mulCharEquiv` 的定义

English:
definition mulCharEquiv
  signature: : MulChar (MulChar M R) R ≃* Mˣ
  body: mulEquivToUnitHom.trans toUnits.monoidHomCongrLeft.symm.trans
mulEquivToUnitHom.monoidHomCongrLeft.trans CommGroup.monoidHomMonoidHomEquiv Mˣ R

中文:
定义 mulCharEquiv
  签名: : 乘法特征 (乘法特征 M R) R ≃* Mˣ
  定义体: mulEquivToUnitHom.trans toUnits.monoidHomCongrLeft.symm.trans
mulEquivToUnitHom.monoidHomCongrLeft.trans CommGroup.monoidHomMonoidHomEquiv Mˣ R

Depends on / 依赖: CommGroup, CommGroup.monoidHomMonoidHomEquiv, monoidHomCongrLeft, monoidHomMonoidHomEquiv, mulEquivToUnitHom, mulEquivToUnitHom.monoidHomCongrLeft.trans, mulEquivToUnitHom.trans, toUnits, toUnits.monoidHomCongrLeft.symm.trans
-/
noncomputable def mulCharEquiv : MulChar (MulChar M R) R ≃* Mˣ :=
mulEquivToUnitHom.trans toUnits.monoidHomCongrLeft.symm.trans
mulEquivToUnitHom.monoidHomCongrLeft.trans CommGroup.monoidHomMonoidHomEquiv Mˣ R

variable {M R}

@[simp]
/--
theorem `mulCharEquiv_symm_apply_apply` / 定理 `mulCharEquiv_symm_apply_apply`

English:
theorem mulCharEquiv_symm_apply_apply
  given: (m : Mˣ) (χ : MulChar M R)
  proof: by
  classical
  rw [show ((mulCharEquiv M R).symm m) χ =
    if IsUnit χ then ↑(mulEquivToUnitHom χ m) else (0 : R) by rfl]; rw [if_pos (Group.isUnit χ)]; rw [mulEquivToUnitHom_apply]; rw [coe_equivToUnitHom]

@[simp]

中文:
定理 mulCharEquiv_symm_apply_apply
  条件: (m : Mˣ) (χ : 乘法特征 M R)
  证明: by
  classical
  rw [show ((mulCharEquiv M R).symm m) χ =
    if IsUnit χ then ↑(mulEquivToUnitHom χ m) else (0 : R) by rfl]; rw [if_pos (Group.isUnit χ)]; rw [mulEquivToUnitHom_apply]; rw [coe_equivToUnitHom]

@[simp]

Depends on / 依赖: Group.isUnit, IsUnit, classical, coe_equivToUnitHom, if_pos, isUnit, mulCharEquiv, mulEquivToUnitHom, mulEquivToUnitHom_apply
-/
theorem mulCharEquiv_symm_apply_apply (m : Mˣ) (χ : MulChar M R) :
    (mulCharEquiv M R).symm m χ = χ m := by
  classical
  rw [show ((mulCharEquiv M R).symm m) χ =
    if IsUnit χ then ↑(mulEquivToUnitHom χ m) else (0 : R) by rfl]; rw [if_pos (Group.isUnit χ)]; rw [mulEquivToUnitHom_apply]; rw [coe_equivToUnitHom]

@[simp]
/--
theorem `apply_mulCharEquiv` / 定理 `apply_mulCharEquiv`

English:
theorem apply_mulCharEquiv
  given: (χ : MulChar M R) (η : MulChar (MulChar M R) R)
  proof: by
  rw [← mulCharEquiv_symm_apply_apply (mulCharEquiv M R η) χ]; rw [MulEquiv.symm_apply_apply]

中文:
定理 apply_mulCharEquiv
  条件: (χ : 乘法特征 M R) (η : 乘法特征 (乘法特征 M R) R)
  证明: by
  rw [← mulCharEquiv_symm_apply_apply (mulCharEquiv M R η) χ]; rw [MulEquiv.symm_apply_apply]

Depends on / 依赖: MulEquiv, MulEquiv.symm_apply_apply, mulCharEquiv, mulCharEquiv_symm_apply_apply, symm_apply_apply
-/
theorem apply_mulCharEquiv (χ : MulChar M R) (η : MulChar (MulChar M R) R) :
    χ (mulCharEquiv M R η) = η χ := by
  rw [← mulCharEquiv_symm_apply_apply (mulCharEquiv M R η) χ]; rw [MulEquiv.symm_apply_apply]

variable (M R) in
/--
Definition of `subgroupOrderIsoSubgroupMulChar` / `subgroupOrderIsoSubgroupMulChar` 的定义

English:
definition subgroupOrderIsoSubgroupMulChar
  signature: : Subgroup Mˣ ≃o (Subgroup (MulChar M R))ᵒᵈ
  body: (CommGroup.subgroupOrderIsoSubgroupMonoidHom Mˣ R).trans mulEquivToUnitHom.symm.mapSubgroup.dual

@[simp]

中文:
定义 subgroupOrderIsoSubgroupMulChar
  签名: : 子群 Mˣ ≃o (子群 (乘法特征 M R))ᵒᵈ
  定义体: (CommGroup.subgroupOrderIsoSubgroupMonoidHom Mˣ R).trans mulEquivToUnitHom.symm.mapSubgroup.dual

@[simp]

Depends on / 依赖: CommGroup, CommGroup.subgroupOrderIsoSubgroupMonoidHom, mapSubgroup, mulEquivToUnitHom, mulEquivToUnitHom.symm.mapSubgroup.dual, subgroupOrderIsoSubgroupMonoidHom
-/
noncomputable def subgroupOrderIsoSubgroupMulChar : Subgroup Mˣ ≃o (Subgroup (MulChar M R))ᵒᵈ :=
  (CommGroup.subgroupOrderIsoSubgroupMonoidHom Mˣ R).trans mulEquivToUnitHom.symm.mapSubgroup.dual

@[simp]
/--
theorem `mem_subgroupOrderIsoSubgroupMulChar_iff` / 定理 `mem_subgroupOrderIsoSubgroupMulChar_iff`

English:
theorem mem_subgroupOrderIsoSubgroupMulChar_iff
  given: {H : Subgroup Mˣ} {χ : MulChar M R}
  proof: by
  rw [subgroupOrderIsoSubgroupMulChar]; rw [OrderIso.trans_apply]; rw [OrderIso.dual_apply]; rw [MulEquiv.coe_mapSubgroup]; rw [OrderDual.ofDual_toDual]; rw [Subgroup.mem_map_equiv]
  simp [← Units.val_eq_one]

@[simp]

中文:
定理 mem_subgroupOrderIsoSubgroupMulChar_iff
  条件: {H : 子群 Mˣ} {χ : 乘法特征 M R}
  证明: by
  rw [subgroupOrderIsoSubgroupMulChar]; rw [OrderIso.trans_apply]; rw [OrderIso.dual_apply]; rw [MulEquiv.coe_mapSubgroup]; rw [OrderDual.ofDual_toDual]; rw [Subgroup.mem_map_equiv]
  simp [← Units.val_eq_one]

@[simp]

Depends on / 依赖: MulEquiv, MulEquiv.coe_mapSubgroup, OrderDual, OrderDual.ofDual_toDual, OrderIso, OrderIso.dual_apply, OrderIso.trans_apply, Subgroup, Subgroup.mem_map_equiv, Units.val_eq_one, coe_mapSubgroup, dual_apply, mem_map_equiv, ofDual_toDual, subgroupOrderIsoSubgroupMulChar, trans_apply, val_eq_one
-/
theorem mem_subgroupOrderIsoSubgroupMulChar_iff {H : Subgroup Mˣ} {χ : MulChar M R} :
    χ in (subgroupOrderIsoSubgroupMulChar M R H).ofDual ↔ forall m in H, χ m = 1 := by
  rw [subgroupOrderIsoSubgroupMulChar]; rw [OrderIso.trans_apply]; rw [OrderIso.dual_apply]; rw [MulEquiv.coe_mapSubgroup]; rw [OrderDual.ofDual_toDual]; rw [Subgroup.mem_map_equiv]
  simp [← Units.val_eq_one]

@[simp]
/--
theorem `mem_subgroupOrderIsoSubgroupMulChar_symm_iff` / 定理 `mem_subgroupOrderIsoSubgroupMulChar_symm_iff`

English:
theorem mem_subgroupOrderIsoSubgroupMulChar_symm_iff
  given: {X : Subgroup (MulChar M R)} {m : Mˣ}
  proof: by
  simp [subgroupOrderIsoSubgroupMulChar, ← Units.val_eq_one]

中文:
定理 mem_subgroupOrderIsoSubgroupMulChar_symm_iff
  条件: {X : 子群 (乘法特征 M R)} {m : Mˣ}
  证明: by
  simp [subgroupOrderIsoSubgroupMulChar, ← Units.val_eq_one]

Depends on / 依赖: Units.val_eq_one, subgroupOrderIsoSubgroupMulChar, val_eq_one
-/
theorem mem_subgroupOrderIsoSubgroupMulChar_symm_iff {X : Subgroup (MulChar M R)} {m : Mˣ} :
    m in (subgroupOrderIsoSubgroupMulChar M R).symm (OrderDual.toDual X) ↔ forall χ in X, χ m = 1 := by
  simp [subgroupOrderIsoSubgroupMulChar, ← Units.val_eq_one]

/--
theorem `card_subgroupOrderIsoSubgroupMulChar` / 定理 `card_subgroupOrderIsoSubgroupMulChar`

English:
theorem card_subgroupOrderIsoSubgroupMulChar
  given: {H : Subgroup Mˣ}
  proof: by
  rw [subgroupOrderIsoSubgroupMulChar]; rw [OrderIso.trans_apply]; rw [OrderIso.dual_apply]; rw [OrderDual.ofDual_toDual]; rw [Subgroup.card_mapSubgroup]; rw [CommGroup.card_subgroupOrderIsoSubgroupMonoidHom]

中文:
定理 card_subgroupOrderIsoSubgroupMulChar
  条件: {H : 子群 Mˣ}
  证明: by
  rw [subgroupOrderIsoSubgroupMulChar]; rw [OrderIso.trans_apply]; rw [OrderIso.dual_apply]; rw [OrderDual.ofDual_toDual]; rw [Subgroup.card_mapSubgroup]; rw [CommGroup.card_subgroupOrderIsoSubgroupMonoidHom]

Depends on / 依赖: CommGroup, CommGroup.card_subgroupOrderIsoSubgroupMonoidHom, OrderDual, OrderDual.ofDual_toDual, OrderIso, OrderIso.dual_apply, OrderIso.trans_apply, Subgroup, Subgroup.card_mapSubgroup, card_mapSubgroup, card_subgroupOrderIsoSubgroupMonoidHom, dual_apply, ofDual_toDual, subgroupOrderIsoSubgroupMulChar, trans_apply
-/
theorem card_subgroupOrderIsoSubgroupMulChar {H : Subgroup Mˣ} :
    Nat.card (subgroupOrderIsoSubgroupMulChar M R H).ofDual = Nat.card (Mˣ ⧸ H) := by
  rw [subgroupOrderIsoSubgroupMulChar]; rw [OrderIso.trans_apply]; rw [OrderIso.dual_apply]; rw [OrderDual.ofDual_toDual]; rw [Subgroup.card_mapSubgroup]; rw [CommGroup.card_subgroupOrderIsoSubgroupMonoidHom]

end MulChar
