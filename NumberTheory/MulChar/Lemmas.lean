/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Further Results on multiplicative characters
-/

@[expose] public section

namespace MulChar

section CommMonoid

variable {R : Type*} [CommMonoid R] {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S)
  {R' : Type*} [CommMonoidWithZero R']

/--
lemma `eq_iff` / 引理 `eq_iff`

English:
lemma eq_iff
  given: {g : Rˣ} (hg : forall x, x in Subgroup.zpowers g) (χ₁ χ₂ : MulChar R R')
  proof: by
  rw [← Equiv.apply_eq_iff_eq equivToUnitHom]; rw [MonoidHom.eq_iff_eq_on_generator hg]; rw [← coe_equivToUnitHom]; rw [← coe_equivToUnitHom]; rw [Units.ext_iff]

中文:
引理 eq_iff
  条件: {g : Rˣ} (hg : 对任意 x, x in 子群.zpowers g) (χ₁ χ₂ : 乘法特征 R R')
  证明: by
  rw [← Equiv.apply_eq_iff_eq equivToUnitHom]; rw [MonoidHom.eq_iff_eq_on_generator hg]; rw [← coe_equivToUnitHom]; rw [← coe_equivToUnitHom]; rw [Units.ext_iff]

Depends on / 依赖: Equiv.apply_eq_iff_eq, MonoidHom, MonoidHom.eq_iff_eq_on_generator, Units.ext_iff, apply_eq_iff_eq, coe_equivToUnitHom, eq_iff_eq_on_generator, equivToUnitHom, ext_iff
-/
lemma eq_iff {g : Rˣ} (hg : forall x, x in Subgroup.zpowers g) (χ₁ χ₂ : MulChar R R') :
    χ₁ = χ₂ ↔ χ₁ g.val = χ₂ g.val := by
  rw [← Equiv.apply_eq_iff_eq equivToUnitHom]; rw [MonoidHom.eq_iff_eq_on_generator hg]; rw [← coe_equivToUnitHom]; rw [← coe_equivToUnitHom]; rw [Units.ext_iff]

/--
theorem `domRestrict_ofUnitHom` / 定理 `domRestrict_ofUnitHom`

English:
theorem domRestrict_ofUnitHom
  given: (f : Rˣ ->* R'ˣ) (S : Submonoid R)
  statement: domRestrict S (ofUnitHom f) =
  proof: by
  ext x
  simp only [ofUnitHom_eq, domRestrict_apply, Units.isUnit, reduceIte, equivToUnitHom_symm_coe,
    MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, MonoidHom.domRestrict_apply]
  rw [← Submonoid.val_unitsEquivUnitsType_symm_apply_coe S x]; rw [equivToUnitHom_symm_coe]

@[deprecated (since := "2026-07-19")] alias restrict_ofUnitHom := domRestrict_ofUnitHom

中文:
定理 domRestrict_ofUnitHom
  条件: (f : Rˣ ->* R'ˣ) (S : 子幺半群 R)
  结论: domRestrict S (ofUnitHom f) =
  证明: by
  ext x
  simp only [ofUnitHom_eq, domRestrict_apply, Units.isUnit, reduceIte, equivToUnitHom_symm_coe,
    MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, MonoidHom.domRestrict_apply]
  rw [← Submonoid.val_unitsEquivUnitsType_symm_apply_coe S x]; rw [equivToUnitHom_symm_coe]

@[deprecated (since := "2026-07-19")] alias restrict_ofUnitHom := domRestrict_ofUnitHom

Depends on / 依赖: Function, Function.comp_apply, MonoidHom, MonoidHom.coe_coe, MonoidHom.coe_comp, MonoidHom.domRestrict_apply, Submonoid, Submonoid.val_unitsEquivUnitsType_symm_apply_coe, Units.isUnit, coe_coe, coe_comp, comp_apply, domRestrict_apply, equivToUnitHom_symm_coe, isUnit, ofUnitHom_eq, reduceIte, val_unitsEquivUnitsType_symm_apply_coe
-/
theorem domRestrict_ofUnitHom (f : Rˣ ->* R'ˣ) (S : Submonoid R) : domRestrict S (ofUnitHom f) =
      ofUnitHom ((f.domRestrict S.units).comp S.unitsEquivUnitsType.symm) := by
  ext x
  simp only [ofUnitHom_eq, domRestrict_apply, Units.isUnit, reduceIte, equivToUnitHom_symm_coe,
    MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply, MonoidHom.domRestrict_apply]
  rw [← Submonoid.val_unitsEquivUnitsType_symm_apply_coe S x]; rw [equivToUnitHom_symm_coe]

@[deprecated (since := "2026-07-19")] alias restrict_ofUnitHom := domRestrict_ofUnitHom

end CommMonoid

section Ring

variable {R R' : Type*} [CommRing R] [CommRing R']

/-- Define the conjugation (`star`) of a multiplicative character by conjugating pointwise. -/
@[simps!]
/--
Definition of `starComp` / `starComp` 的定义

English:
definition starComp
  signature: [StarRing R'] (χ : MulChar R R')
  body: χ.ringHomComp (starRingEnd R')

中文:
定义 starComp
  签名: [对合环 R'] (χ : 乘法特征 R R')
  定义体: χ.ringHomComp (starRingEnd R')

Depends on / 依赖: ringHomComp, starRingEnd
-/
def starComp [StarRing R'] (χ : MulChar R R') : MulChar R R' :=
  χ.ringHomComp (starRingEnd R')

/--
Instance `instStarMul` / 实例 `instStarMul`

English:
instance instStarMul
  signature: [StarRing R']
  body: starComp
  star_involutive χ := by
    ext1
    simp [starComp_apply]
  star_mul χ χ' := by
    ext1
    simp [starComp_apply, mul_comm]

@[simp]

中文:
实例 instStarMul
  签名: [对合环 R']
  定义体: starComp
  star_involutive χ := by
    ext1
    simp [starComp_apply]
  star_mul χ χ' := by
    ext1
    simp [starComp_apply, mul_comm]

@[simp]

Depends on / 依赖: starComp
-/
instance instStarMul [StarRing R'] : StarMul (MulChar R R') where
  star := starComp
  star_involutive χ := by
    ext1
    simp [starComp_apply]
  star_mul χ χ' := by
    ext1
    simp [starComp_apply, mul_comm]

@[simp]
/--
lemma `star_apply` / 引理 `star_apply`

English:
lemma star_apply
  given: [StarRing R'] (χ : MulChar R R') (a : R)
  statement: (star χ) a = star (χ a)
  proof: rfl

中文:
引理 star_apply
  条件: [对合环 R'] (χ : 乘法特征 R R') (a : R)
  结论: (star χ) a = star (χ a)
  证明: rfl
-/
lemma star_apply [StarRing R'] (χ : MulChar R R') (a : R) : (star χ) a = star (χ a) :=
  rfl

/--
lemma `apply_mem_rootsOfUnity` / 引理 `apply_mem_rootsOfUnity`

English:
lemma apply_mem_rootsOfUnity
  given: [Fintype Rˣ] (a : Rˣ) {χ : MulChar R R'}
  proof: by
  rw [mem_rootsOfUnity]; rw [← map_pow]; rw [← (equivToUnitHom χ).map_one]; rw [pow_card_eq_one]

中文:
引理 apply_mem_rootsOfUnity
  条件: [有限类型 Rˣ] (a : Rˣ) {χ : 乘法特征 R R'}
  证明: by
  rw [mem_rootsOfUnity]; rw [← map_pow]; rw [← (equivToUnitHom χ).map_one]; rw [pow_card_eq_one]

Depends on / 依赖: equivToUnitHom, map_one, map_pow, mem_rootsOfUnity, pow_card_eq_one
-/
lemma apply_mem_rootsOfUnity [Fintype Rˣ] (a : Rˣ) {χ : MulChar R R'} :
    equivToUnitHom χ a in rootsOfUnity (Fintype.card Rˣ) R' := by
  rw [mem_rootsOfUnity]; rw [← map_pow]; rw [← (equivToUnitHom χ).map_one]; rw [pow_card_eq_one]

variable [Finite Rˣ]

open Complex in
/--
lemma `star_eq_inv` / 引理 `star_eq_inv`

English:
lemma star_eq_inv
  given: (χ : MulChar R Complex)
  statement: star χ = χ⁻¹
  proof: by
  cases nonempty_fintype Rˣ
  ext1 a
  simp only [inv_apply_eq_inv']
  exact (inv_eq_conj <| norm_eq_one_of_mem_rootsOfUnity <| χ.apply_mem_rootsOfUnity a).symm

中文:
引理 star_eq_inv
  条件: (χ : 乘法特征 R 复形)
  结论: star χ = χ⁻¹
  证明: by
  cases nonempty_fintype Rˣ
  ext1 a
  simp only [inv_apply_eq_inv']
  exact (inv_eq_conj <| norm_eq_one_of_mem_rootsOfUnity <| χ.apply_mem_rootsOfUnity a).symm

Depends on / 依赖: apply_mem_rootsOfUnity, inv_apply_eq_inv, inv_eq_conj, nonempty_fintype, norm_eq_one_of_mem_rootsOfUnity
-/
lemma star_eq_inv (χ : MulChar R Complex) : star χ = χ⁻¹ := by
  cases nonempty_fintype Rˣ
  ext1 a
  simp only [inv_apply_eq_inv']
  exact (inv_eq_conj <| norm_eq_one_of_mem_rootsOfUnity <| χ.apply_mem_rootsOfUnity a).symm

/--
lemma `star_apply'` / 引理 `star_apply'`

English:
lemma star_apply'
  given: (χ : MulChar R Complex) (a : R)
  statement: star (χ a) = χ⁻¹ a
  proof: by
  simp only [RCLike.star_def, ← star_eq_inv, star_apply]

中文:
引理 star_apply'
  条件: (χ : 乘法特征 R 复形) (a : R)
  结论: star (χ a) = χ⁻¹ a
  证明: by
  simp only [RCLike.star_def, ← star_eq_inv, star_apply]

Depends on / 依赖: RCLike, RCLike.star_def, star_apply, star_def, star_eq_inv
-/
lemma star_apply' (χ : MulChar R Complex) (a : R) : star (χ a) = χ⁻¹ a := by
  simp only [RCLike.star_def, ← star_eq_inv, star_apply]

end Ring

section IsCyclic

/-!
### Multiplicative characters on finite monoids with cyclic unit group
-/

variable {M : Type*} [CommMonoid M] [Fintype M] [DecidableEq M]
variable {R : Type*} [CommMonoidWithZero R]

/--
Definition of `ofRootOfUnity` / `ofRootOfUnity` 的定义

English:
definition ofRootOfUnity
  signature: {ζ : Rˣ} (hζ : ζ in rootsOfUnity (Fintype.card Mˣ) R)
  body: by
  have : orderOf ζ ∣ Fintype.card Mˣ :=
orderOf_dvd_iff_pow_eq_one.mpr (mem_rootsOfUnity _ ζ).mp hζ
refine ofUnitHom monoidHomOfForallMemZpowers hg this.trans dvd_of_eq ?_
  rw [orderOf_eq_card_of_forall_mem_zpowers hg]; rw [Nat.card_eq_fintype_card]

中文:
定义 ofRootOfUnity
  签名: {ζ : Rˣ} (hζ : ζ in rootsOfUnity (有限类型.card Mˣ) R)
  定义体: by
  have : orderOf ζ ∣ Fintype.card Mˣ :=
orderOf_dvd_iff_pow_eq_one.mpr (mem_rootsOfUnity _ ζ).mp hζ
refine ofUnitHom monoidHomOfForallMemZpowers hg this.trans dvd_of_eq ?_
  rw [orderOf_eq_card_of_forall_mem_zpowers hg]; rw [Nat.card_eq_fintype_card]

Depends on / 依赖: Fintype, Fintype.card, Nat.card_eq_fintype_card, card_eq_fintype_card, dvd_of_eq, mem_rootsOfUnity, monoidHomOfForallMemZpowers, ofUnitHom, orderOf, orderOf_dvd_iff_pow_eq_one, orderOf_dvd_iff_pow_eq_one.mpr, orderOf_eq_card_of_forall_mem_zpowers, this.trans
-/
noncomputable def ofRootOfUnity {ζ : Rˣ} (hζ : ζ in rootsOfUnity (Fintype.card Mˣ) R)
    {g : Mˣ} (hg : forall x, x in Subgroup.zpowers g) :
    MulChar M R := by
  have : orderOf ζ ∣ Fintype.card Mˣ :=
orderOf_dvd_iff_pow_eq_one.mpr (mem_rootsOfUnity _ ζ).mp hζ
refine ofUnitHom monoidHomOfForallMemZpowers hg this.trans dvd_of_eq ?_
  rw [orderOf_eq_card_of_forall_mem_zpowers hg]; rw [Nat.card_eq_fintype_card]

/--
lemma `ofRootOfUnity_spec` / 引理 `ofRootOfUnity_spec`

English:
lemma ofRootOfUnity_spec
  statement: {ζ : Rˣ} (hζ : ζ in rootsOfUnity (Fintype.card Mˣ) R)
  proof: by
  simp only [ofRootOfUnity, ofUnitHom_eq, equivToUnitHom_symm_coe,
    monoidHomOfForallMemZpowers_apply_gen]

中文:
引理 ofRootOfUnity_spec
  结论: {ζ : Rˣ} (hζ : ζ in rootsOfUnity (有限类型.card Mˣ) R)
  证明: by
  simp only [ofRootOfUnity, ofUnitHom_eq, equivToUnitHom_symm_coe,
    monoidHomOfForallMemZpowers_apply_gen]

Depends on / 依赖: equivToUnitHom_symm_coe, monoidHomOfForallMemZpowers_apply_gen, ofRootOfUnity, ofUnitHom_eq
-/
lemma ofRootOfUnity_spec {ζ : Rˣ} (hζ : ζ in rootsOfUnity (Fintype.card Mˣ) R)
    {g : Mˣ} (hg : forall x, x in Subgroup.zpowers g) :
    ofRootOfUnity hζ hg g = ζ := by
  simp only [ofRootOfUnity, ofUnitHom_eq, equivToUnitHom_symm_coe,
    monoidHomOfForallMemZpowers_apply_gen]

variable (M R) in
/--
Definition of `equiv_rootsOfUnity` / `equiv_rootsOfUnity` 的定义

English:
definition equiv_rootsOfUnity
  signature: [inst_cyc : IsCyclic Mˣ]
  body: ⟨χ.toUnitHom Classical.choose inst_cyc.exists_generator, by
      simp only [toUnitHom_eq, mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one]⟩
invFun ζ := ofRootOfUnity ζ.prop Classical.choose_spec inst_cyc.exists_generator
  left_inv χ := by
    simp only [toUnitHom_eq, eq_iff <| Classical.choose_spec inst_cyc.exists_generator,
      ofRootOfUnity_spec, coe_equivToUnitHom]
  right_inv ζ := by
    ext
    simp only [toUnitHom_eq, coe_equivToUnitHom, ofRootOfUnity_spec]
  map_mul' x y := by
    simp only [toUnitHom_eq, equivToUnitHom_mul_apply, MulMemClass.mk_mul_mk]

中文:
定义 equiv_rootsOfUnity
  签名: [inst_cyc : 是循环 Mˣ]
  定义体: ⟨χ.toUnitHom Classical.choose inst_cyc.exists_generator, by
      simp only [toUnitHom_eq, mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one]⟩
invFun ζ := ofRootOfUnity ζ.prop Classical.choose_spec inst_cyc.exists_generator
  left_inv χ := by
    simp only [toUnitHom_eq, eq_iff <| Classical.choose_spec inst_cyc.exists_generator,
      ofRootOfUnity_spec, coe_equivToUnitHom]
  right_inv ζ := by
    ext
    simp only [toUnitHom_eq, coe_equivToUnitHom, ofRootOfUnity_spec]
  map_mul' x y := by
    simp only [toUnitHom_eq, equivToUnitHom_mul_apply, MulMemClass.mk_mul_mk]

Depends on / 依赖: Classical, Classical.choose, Classical.choose_spec, choose_spec, coe_equivToUnitHom, eq_iff, equivT, exists_generator, inst_cyc, inst_cyc.exists_generator, invFun, left_inv, map_mul, map_one, map_pow, mem_rootsOfUnity, ofRootOfUnity, ofRootOfUnity_spec, pow_card_eq_one, right_inv
-/
noncomputable def equiv_rootsOfUnity [inst_cyc : IsCyclic Mˣ] :
    MulChar M R ≃* rootsOfUnity (Fintype.card Mˣ) R where
  toFun χ :=
⟨χ.toUnitHom Classical.choose inst_cyc.exists_generator, by
      simp only [toUnitHom_eq, mem_rootsOfUnity, ← map_pow, pow_card_eq_one, map_one]⟩
invFun ζ := ofRootOfUnity ζ.prop Classical.choose_spec inst_cyc.exists_generator
  left_inv χ := by
    simp only [toUnitHom_eq, eq_iff <| Classical.choose_spec inst_cyc.exists_generator,
      ofRootOfUnity_spec, coe_equivToUnitHom]
  right_inv ζ := by
    ext
    simp only [toUnitHom_eq, coe_equivToUnitHom, ofRootOfUnity_spec]
  map_mul' x y := by
    simp only [toUnitHom_eq, equivToUnitHom_mul_apply, MulMemClass.mk_mul_mk]

end IsCyclic

section FiniteField

/-!
### Multiplicative characters on finite fields
-/

section Fintype

variable (F : Type*) [Field F] [Fintype F]
variable {R : Type*} [CommRing R]

/--
lemma `exists_mulChar_orderOf` / 引理 `exists_mulChar_orderOf`

English:
lemma exists_mulChar_orderOf
  statement: {n : Nat} (h : n ∣ Fintype.card F - 1) {ζ : R}
  proof: by
  classical
  have hn₀ : 0 < n := by
    refine Nat.pos_of_ne_zero fun hn => ?_
    simp only [hn, zero_dvd_iff, Nat.sub_eq_zero_iff_le] at h
    exact (Fintype.one_lt_card.trans_le h).false
  let e := MulChar.equiv_rootsOfUnity F R
  let ζ' : Rˣ := (hζ.isUnit hn₀.ne').unit
  have h' : ζ' ^ (Fintype.card Fˣ : Nat) = 1 :=
Units.ext_iff.mpr (hζ.pow_eq_one_iff_dvd _).mpr Fintype.card_units (α := F) ▸ h
  use e.symm ⟨ζ', (mem_rootsOfUnity (Fintype.card Fˣ) ζ').mpr h'⟩
  rw [e.symm.orderOf_eq]; rw [orderOf_eq_iff hn₀]
  refine ⟨?_, fun m hm hm₀ h => ?_⟩
  · ext
    push_cast
    exact hζ.pow_eq_one
  · rw [Subtype.ext_iff, Units.ext_iff] at h
    push_cast at h
    exact ((Nat.le_of_dvd hm₀ <| hζ.dvd_of_pow_eq_one _ h).trans_lt hm).false

中文:
引理 存在_mulChar_orderOf
  结论: {n : 自然数} (h : n ∣ 有限类型.card F - 1) {ζ : R}
  证明: by
  classical
  have hn₀ : 0 < n := by
    refine Nat.pos_of_ne_zero fun hn => ?_
    simp only [hn, zero_dvd_iff, Nat.sub_eq_zero_iff_le] at h
    exact (Fintype.one_lt_card.trans_le h).false
  let e := MulChar.equiv_rootsOfUnity F R
  let ζ' : Rˣ := (hζ.isUnit hn₀.ne').unit
  have h' : ζ' ^ (Fintype.card Fˣ : Nat) = 1 :=
Units.ext_iff.mpr (hζ.pow_eq_one_iff_dvd _).mpr Fintype.card_units (α := F) ▸ h
  use e.symm ⟨ζ', (mem_rootsOfUnity (Fintype.card Fˣ) ζ').mpr h'⟩
  rw [e.symm.orderOf_eq]; rw [orderOf_eq_iff hn₀]
  refine ⟨?_, fun m hm hm₀ h => ?_⟩
  · ext
    push_cast
    exact hζ.pow_eq_one
  · rw [Subtype.ext_iff, Units.ext_iff] at h
    push_cast at h
    exact ((Nat.le_of_dvd hm₀ <| hζ.dvd_of_pow_eq_one _ h).trans_lt hm).false

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_units, Fintype.one_lt_card.trans_le, MulChar, MulChar.equiv_rootsOfUnity, Nat.pos_of_ne_zero, Nat.sub_eq_zero_iff_le, Units.ext_iff.mpr, card_units, classical, e.symm, e.symm.orderOf_eq, equiv_rootsOfUnity, ext_iff, isUnit, mem_rootsOfUnity, one_lt_card, orderOf_eq, orderOf_eq_iff
-/
lemma exists_mulChar_orderOf {n : Nat} (h : n ∣ Fintype.card F - 1) {ζ : R}
    (hζ : IsPrimitiveRoot ζ n) :
    exists χ : MulChar F R, orderOf χ = n := by
  classical
  have hn₀ : 0 < n := by
    refine Nat.pos_of_ne_zero fun hn => ?_
    simp only [hn, zero_dvd_iff, Nat.sub_eq_zero_iff_le] at h
    exact (Fintype.one_lt_card.trans_le h).false
  let e := MulChar.equiv_rootsOfUnity F R
  let ζ' : Rˣ := (hζ.isUnit hn₀.ne').unit
  have h' : ζ' ^ (Fintype.card Fˣ : Nat) = 1 :=
Units.ext_iff.mpr (hζ.pow_eq_one_iff_dvd _).mpr Fintype.card_units (α := F) ▸ h
  use e.symm ⟨ζ', (mem_rootsOfUnity (Fintype.card Fˣ) ζ').mpr h'⟩
  rw [e.symm.orderOf_eq]; rw [orderOf_eq_iff hn₀]
  refine ⟨?_, fun m hm hm₀ h => ?_⟩
  · ext
    push_cast
    exact hζ.pow_eq_one
  · rw [Subtype.ext_iff, Units.ext_iff] at h
    push_cast at h
    exact ((Nat.le_of_dvd hm₀ <| hζ.dvd_of_pow_eq_one _ h).trans_lt hm).false

/--
lemma `orderOf_dvd_card_sub_one` / 引理 `orderOf_dvd_card_sub_one`

English:
lemma orderOf_dvd_card_sub_one
  given: (χ : MulChar F R)
  statement: orderOf χ ∣ Fintype.card F - 1
  proof: by
  classical
  rw [← Fintype.card_units]
  exact orderOf_dvd_of_pow_eq_one χ.pow_card_eq_one

中文:
引理 orderOf_dvd_card_sub_one
  条件: (χ : 乘法特征 F R)
  结论: orderOf χ ∣ 有限类型.card F - 1
  证明: by
  classical
  rw [← Fintype.card_units]
  exact orderOf_dvd_of_pow_eq_one χ.pow_card_eq_one

Depends on / 依赖: Fintype, Fintype.card_units, card_units, classical, orderOf_dvd_of_pow_eq_one, pow_card_eq_one
-/
lemma orderOf_dvd_card_sub_one (χ : MulChar F R) : orderOf χ ∣ Fintype.card F - 1 := by
  classical
  rw [← Fintype.card_units]
  exact orderOf_dvd_of_pow_eq_one χ.pow_card_eq_one

/--
lemma `exists_mulChar_orderOf_eq_card_units` / 引理 `exists_mulChar_orderOf_eq_card_units`

English:
lemma exists_mulChar_orderOf_eq_card_units
  statement: [DecidableEq F]
  proof: exists_mulChar_orderOf F (by rw [Fintype.card_units]) hζ

中文:
引理 存在_mulChar_orderOf_eq_card_units
  结论: [DecidableEq F]
  证明: exists_mulChar_orderOf F (by rw [Fintype.card_units]) hζ

Depends on / 依赖: Fintype, Fintype.card_units, card_units, exists_mulChar_orderOf
-/
lemma exists_mulChar_orderOf_eq_card_units [DecidableEq F]
    {ζ : R} (hζ : IsPrimitiveRoot ζ (Fintype.card Fˣ)) :
    exists χ : MulChar F R, orderOf χ = Fintype.card Fˣ :=
  exists_mulChar_orderOf F (by rw [Fintype.card_units]) hζ

end Fintype

variable {F : Type*} [Field F] [Finite F]
variable {R : Type*} [CommRing R]

/--
lemma `apply_mem_rootsOfUnity_orderOf` / 引理 `apply_mem_rootsOfUnity_orderOf`

English:
lemma apply_mem_rootsOfUnity_orderOf
  given: (χ : MulChar F R) {a : F} (ha : a != 0)
  proof: by
  have hu : IsUnit (χ a) := ha.isUnit.map χ
  refine ⟨hu.unit, ?_, hu.unit_spec⟩
  rw [mem_rootsOfUnity]; rw [Units.ext_iff]; rw [Units.val_pow_eq_pow_val]; rw [Units.val_one]; rw [IsUnit.unit_spec]; rw [← χ.pow_apply' χ.orderOf_pos.ne']; rw [pow_orderOf_eq_one]; rw [show a = (isUnit_iff_ne_zero.mpr ha).unit by simp only [IsUnit.unit_spec],
    MulChar.one_apply_coe]

中文:
引理 apply_mem_rootsOfUnity_orderOf
  条件: (χ : 乘法特征 F R) {a : F} (ha : a != 0)
  证明: by
  have hu : IsUnit (χ a) := ha.isUnit.map χ
  refine ⟨hu.unit, ?_, hu.unit_spec⟩
  rw [mem_rootsOfUnity]; rw [Units.ext_iff]; rw [Units.val_pow_eq_pow_val]; rw [Units.val_one]; rw [IsUnit.unit_spec]; rw [← χ.pow_apply' χ.orderOf_pos.ne']; rw [pow_orderOf_eq_one]; rw [show a = (isUnit_iff_ne_zero.mpr ha).unit by simp only [IsUnit.unit_spec],
    MulChar.one_apply_coe]

Depends on / 依赖: IsUnit, IsUnit.unit_spec, MulChar, MulChar.one_apply_coe, Units.ext_iff, Units.val_one, Units.val_pow_eq_pow_val, ext_iff, ha.isUnit.map, hu.unit, hu.unit_spec, isUnit, isUnit_iff_ne_zero, isUnit_iff_ne_zero.mpr, mem_rootsOfUnity, one_apply_coe, orderOf_pos, orderOf_pos.ne, pow_apply, pow_orderOf_eq_one
-/
lemma apply_mem_rootsOfUnity_orderOf (χ : MulChar F R) {a : F} (ha : a != 0) :
    exists ζ in rootsOfUnity (orderOf χ) R, ζ = χ a := by
  have hu : IsUnit (χ a) := ha.isUnit.map χ
  refine ⟨hu.unit, ?_, hu.unit_spec⟩
  rw [mem_rootsOfUnity]; rw [Units.ext_iff]; rw [Units.val_pow_eq_pow_val]; rw [Units.val_one]; rw [IsUnit.unit_spec]; rw [← χ.pow_apply' χ.orderOf_pos.ne']; rw [pow_orderOf_eq_one]; rw [show a = (isUnit_iff_ne_zero.mpr ha).unit by simp only [IsUnit.unit_spec],
    MulChar.one_apply_coe]

/--
lemma `apply_mem_rootsOfUnity_of_pow_eq_one` / 引理 `apply_mem_rootsOfUnity_of_pow_eq_one`

English:
lemma apply_mem_rootsOfUnity_of_pow_eq_one
  statement: {χ : MulChar F R} {n : Nat} (hχ : χ ^ n = 1)
  proof: by
  obtain ⟨μ, hμ₁, hμ₂⟩ := χ.apply_mem_rootsOfUnity_orderOf ha
  exact ⟨μ, rootsOfUnity_le_of_dvd (orderOf_dvd_of_pow_eq_one hχ) hμ₁, hμ₂⟩

中文:
引理 apply_mem_rootsOfUnity_of_pow_eq_one
  结论: {χ : 乘法特征 F R} {n : 自然数} (hχ : χ ^ n = 1)
  证明: by
  obtain ⟨μ, hμ₁, hμ₂⟩ := χ.apply_mem_rootsOfUnity_orderOf ha
  exact ⟨μ, rootsOfUnity_le_of_dvd (orderOf_dvd_of_pow_eq_one hχ) hμ₁, hμ₂⟩

Depends on / 依赖: apply_mem_rootsOfUnity_orderOf, orderOf_dvd_of_pow_eq_one, rootsOfUnity_le_of_dvd
-/
lemma apply_mem_rootsOfUnity_of_pow_eq_one {χ : MulChar F R} {n : Nat} (hχ : χ ^ n = 1)
    {a : F} (ha : a != 0) :
    exists ζ in rootsOfUnity n R, ζ = χ a := by
  obtain ⟨μ, hμ₁, hμ₂⟩ := χ.apply_mem_rootsOfUnity_orderOf ha
  exact ⟨μ, rootsOfUnity_le_of_dvd (orderOf_dvd_of_pow_eq_one hχ) hμ₁, hμ₂⟩

-- Results involving primitive roots of unity require `R` to be an integral domain.
variable [IsDomain R]

/--
lemma `exists_apply_eq_pow` / 引理 `exists_apply_eq_pow`

English:
lemma exists_apply_eq_pow
  statement: {χ : MulChar F R} {n : Nat} [NeZero n] (hχ : χ ^ n = 1) {μ : R}
  proof: by
  obtain ⟨ζ, hζ₁, hζ₂⟩ := apply_mem_rootsOfUnity_of_pow_eq_one hχ ha
  have hζ' : ζ.val ^ n = 1 := (mem_rootsOfUnity' n ↑ζ).mp hζ₁
  obtain ⟨k, hk₁, hk₂⟩ := hμ.eq_pow_of_pow_eq_one hζ'
  exact ⟨k, hk₁, (hζ₂ ▸ hk₂).symm⟩

中文:
引理 存在_apply_eq_pow
  结论: {χ : 乘法特征 F R} {n : 自然数} [NeZero n] (hχ : χ ^ n = 1) {μ : R}
  证明: by
  obtain ⟨ζ, hζ₁, hζ₂⟩ := apply_mem_rootsOfUnity_of_pow_eq_one hχ ha
  have hζ' : ζ.val ^ n = 1 := (mem_rootsOfUnity' n ↑ζ).mp hζ₁
  obtain ⟨k, hk₁, hk₂⟩ := hμ.eq_pow_of_pow_eq_one hζ'
  exact ⟨k, hk₁, (hζ₂ ▸ hk₂).symm⟩

Depends on / 依赖: apply_mem_rootsOfUnity_of_pow_eq_one, eq_pow_of_pow_eq_one, mem_rootsOfUnity
-/
lemma exists_apply_eq_pow {χ : MulChar F R} {n : Nat} [NeZero n] (hχ : χ ^ n = 1) {μ : R}
    (hμ : IsPrimitiveRoot μ n) {a : F} (ha : a != 0) :
    exists k < n, χ a = μ ^ k := by
  obtain ⟨ζ, hζ₁, hζ₂⟩ := apply_mem_rootsOfUnity_of_pow_eq_one hχ ha
  have hζ' : ζ.val ^ n = 1 := (mem_rootsOfUnity' n ↑ζ).mp hζ₁
  obtain ⟨k, hk₁, hk₂⟩ := hμ.eq_pow_of_pow_eq_one hζ'
  exact ⟨k, hk₁, (hζ₂ ▸ hk₂).symm⟩

/--
lemma `apply_mem_algebraAdjoin_of_pow_eq_one` / 引理 `apply_mem_algebraAdjoin_of_pow_eq_one`

English:
lemma apply_mem_algebraAdjoin_of_pow_eq_one
  statement: {χ : MulChar F R} {n : Nat} [NeZero n] (hχ : χ ^ n = 1)
  proof: by
  rcases eq_or_ne a 0 with rfl | h
  · exact χ.map_zero ▸ Subalgebra.zero_mem _
  · obtain ⟨ζ, hζ₁, hζ₂⟩ := apply_mem_rootsOfUnity_of_pow_eq_one hχ h
    rw [mem_rootsOfUnity]; rw [Units.ext_iff]; rw [Units.val_pow_eq_pow_val] at hζ₁
    obtain ⟨k, _, hk⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hμ hζ₁
    exact hζ₂ ▸ hk ▸ Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton Int μ) k

中文:
引理 apply_mem_algebraAdjoin_of_pow_eq_one
  结论: {χ : 乘法特征 F R} {n : 自然数} [NeZero n] (hχ : χ ^ n = 1)
  证明: by
  rcases eq_or_ne a 0 with rfl | h
  · exact χ.map_zero ▸ Subalgebra.zero_mem _
  · obtain ⟨ζ, hζ₁, hζ₂⟩ := apply_mem_rootsOfUnity_of_pow_eq_one hχ h
    rw [mem_rootsOfUnity]; rw [Units.ext_iff]; rw [Units.val_pow_eq_pow_val] at hζ₁
    obtain ⟨k, _, hk⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hμ hζ₁
    exact hζ₂ ▸ hk ▸ Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton Int μ) k

Depends on / 依赖: Algebra, Algebra.self_mem_adjoin_singleton, IsPrimitiveRoot, IsPrimitiveRoot.eq_pow_of_pow_eq_one, Subalgebra, Subalgebra.pow_mem, Subalgebra.zero_mem, Units.ext_iff, Units.val_pow_eq_pow_val, apply_mem_rootsOfUnity_of_pow_eq_one, eq_or_ne, eq_pow_of_pow_eq_one, ext_iff, map_zero, mem_rootsOfUnity, pow_mem, self_mem_adjoin_singleton, val_pow_eq_pow_val, zero_mem
-/
lemma apply_mem_algebraAdjoin_of_pow_eq_one {χ : MulChar F R} {n : Nat} [NeZero n] (hχ : χ ^ n = 1)
    {μ : R} (hμ : IsPrimitiveRoot μ n) (a : F) :
    χ a in Algebra.adjoin Int {μ} := by
  rcases eq_or_ne a 0 with rfl | h
  · exact χ.map_zero ▸ Subalgebra.zero_mem _
  · obtain ⟨ζ, hζ₁, hζ₂⟩ := apply_mem_rootsOfUnity_of_pow_eq_one hχ h
    rw [mem_rootsOfUnity]; rw [Units.ext_iff]; rw [Units.val_pow_eq_pow_val] at hζ₁
    obtain ⟨k, _, hk⟩ := IsPrimitiveRoot.eq_pow_of_pow_eq_one hμ hζ₁
    exact hζ₂ ▸ hk ▸ Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton Int μ) k

/--
lemma `apply_mem_algebraAdjoin` / 引理 `apply_mem_algebraAdjoin`

English:
lemma apply_mem_algebraAdjoin
  statement: {χ : MulChar F R} {μ : R} (hμ : IsPrimitiveRoot μ (orderOf χ))
  proof: have : NeZero (orderOf χ) := ⟨χ.orderOf_pos.ne'⟩
  apply_mem_algebraAdjoin_of_pow_eq_one (pow_orderOf_eq_one χ) hμ a

中文:
引理 apply_mem_algebraAdjoin
  结论: {χ : 乘法特征 F R} {μ : R} (hμ : 是PrimitiveRoot μ (orderOf χ))
  证明: have : NeZero (orderOf χ) := ⟨χ.orderOf_pos.ne'⟩
  apply_mem_algebraAdjoin_of_pow_eq_one (pow_orderOf_eq_one χ) hμ a

Depends on / 依赖: NeZero, apply_mem_algebraAdjoin_of_pow_eq_one, orderOf, orderOf_pos, orderOf_pos.ne, pow_orderOf_eq_one
-/
lemma apply_mem_algebraAdjoin {χ : MulChar F R} {μ : R} (hμ : IsPrimitiveRoot μ (orderOf χ))
    (a : F) :
    χ a in Algebra.adjoin Int {μ} :=
  have : NeZero (orderOf χ) := ⟨χ.orderOf_pos.ne'⟩
  apply_mem_algebraAdjoin_of_pow_eq_one (pow_orderOf_eq_one χ) hμ a

end FiniteField

end MulChar
