/-
Copyright (c) 2023 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, Moritz Firsching, Michael Stoll
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Data.ZMod.Units
public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Dirichlet Characters

Let `R` be a commutative monoid with zero. A Dirichlet character `χ` of level `n` over `R` is a
multiplicative character from `ZMod n` to `R` sending non-units to 0. We then obtain some properties
of `toUnitHom χ`, the restriction of `χ` to a group homomorphism `(ZMod n)ˣ →* Rˣ`.

Main definitions:

- `DirichletCharacter`: The type representing a Dirichlet character.
- `changeLevel`: Extend the Dirichlet character χ of level `n` to level `m`, where `n` divides `m`.
- `conductor`: The conductor of a Dirichlet character.
- `IsPrimitive`: If the level is equal to the conductor.

## Tags

dirichlet character, multiplicative character
-/

@[expose] public section

/-!
### Definitions
-/

/-- The type of Dirichlet characters of level `n`. -/
@[wikidata Q1063579]
/--
Definition of `DirichletCharacter` / `DirichletCharacter` 的定义

English:
abbreviation DirichletCharacter
  signature: (R : Type*) [CommMonoidWithZero R] (n : Nat)
  body: MulChar (ZMod n) R

中文:
缩写 DirichletCharacter
  签名: (R : 类型) [带零交换幺半群 R] (n : 自然数)
  定义体: MulChar (ZMod n) R

Depends on / 依赖: MulChar
-/
abbrev DirichletCharacter (R : Type*) [CommMonoidWithZero R] (n : Nat) := MulChar (ZMod n) R

open MulChar

variable {R : Type*} [CommMonoidWithZero R] {n : Nat} (χ : DirichletCharacter R n)

namespace DirichletCharacter

/--
lemma `toUnitHom_eq_char'` / 引理 `toUnitHom_eq_char'`

English:
lemma toUnitHom_eq_char'
  given: {a : ZMod n} (ha : IsUnit a)
  statement: χ a = χ.toUnitHom ha.unit
  proof: by simp

中文:
引理 toUnitHom_eq_char'
  条件: {a : ZMod n} (ha : 是单位 a)
  结论: χ a = χ.toUnitHom ha.unit
  证明: by simp
-/
lemma toUnitHom_eq_char' {a : ZMod n} (ha : IsUnit a) : χ a = χ.toUnitHom ha.unit := by simp

/--
lemma `toUnitHom_inj` / 引理 `toUnitHom_inj`

English:
lemma toUnitHom_inj
  given: (ψ : DirichletCharacter R n)
  statement: toUnitHom χ = toUnitHom ψ ↔ χ = ψ
  proof: by simp

中文:
引理 toUnitHom_inj
  条件: (ψ : DirichletCharacter R n)
  结论: toUnitHom χ = toUnitHom ψ ↔ χ = ψ
  证明: by simp
-/
lemma toUnitHom_inj (ψ : DirichletCharacter R n) : toUnitHom χ = toUnitHom ψ ↔ χ = ψ := by simp

/--
lemma `eval_modulus_sub` / 引理 `eval_modulus_sub`

English:
lemma eval_modulus_sub
  given: (x : ZMod n)
  statement: χ (n - x) = χ (-x)
  proof: by simp

中文:
引理 eval_modulus_sub
  条件: (x : ZMod n)
  结论: χ (n - x) = χ (-x)
  证明: by simp
-/
lemma eval_modulus_sub (x : ZMod n) : χ (n - x) = χ (-x) := by simp

/--
lemma `apply_ne_zero_iff` / 引理 `apply_ne_zero_iff`

English:
lemma apply_ne_zero_iff
  given: [Nontrivial R] (a : Int)
  statement: χ a != 0 ↔ IsCoprime a n
  proof: by
  rw [MulChar.apply_ne_zero_iff]; rw [ZMod.coe_int_isUnit_iff_isCoprime]; rw [isCoprime_comm]

中文:
引理 apply_ne_zero_iff
  条件: [非平凡 R] (a : 整数)
  结论: χ a != 0 ↔ IsCoprime a n
  证明: by
  rw [MulChar.apply_ne_zero_iff]; rw [ZMod.coe_int_isUnit_iff_isCoprime]; rw [isCoprime_comm]

Depends on / 依赖: MulChar, MulChar.apply_ne_zero_iff, ZMod.coe_int_isUnit_iff_isCoprime, apply_ne_zero_iff, coe_int_isUnit_iff_isCoprime, isCoprime_comm
-/
lemma apply_ne_zero_iff [Nontrivial R] (a : Int) : χ a != 0 ↔ IsCoprime a n := by
  rw [MulChar.apply_ne_zero_iff]; rw [ZMod.coe_int_isUnit_iff_isCoprime]; rw [isCoprime_comm]

/--
lemma `apply_eq_zero_iff` / 引理 `apply_eq_zero_iff`

English:
lemma apply_eq_zero_iff
  given: [Nontrivial R] (a : Int)
  statement: χ a = 0 ↔ ¬ IsCoprime a n
  proof: by
  rw [← (apply_ne_zero_iff χ a).not]; rw [ne_eq]; rw [not_not]

中文:
引理 apply_eq_zero_iff
  条件: [非平凡 R] (a : 整数)
  结论: χ a = 0 ↔ ¬ IsCoprime a n
  证明: by
  rw [← (apply_ne_zero_iff χ a).not]; rw [ne_eq]; rw [not_not]

Depends on / 依赖: apply_ne_zero_iff, ne_eq, not_not
-/
lemma apply_eq_zero_iff [Nontrivial R] (a : Int) : χ a = 0 ↔ ¬ IsCoprime a n := by
  rw [← (apply_ne_zero_iff χ a).not]; rw [ne_eq]; rw [not_not]

/-!
### Changing levels
-/

/--
Definition of `changeLevel` / `changeLevel` 的定义

English:
definition changeLevel
  signature: {n m : Nat} (hm : n ∣ m)
  body: MulChar.ofUnitHom (ψ.toUnitHom.comp (ZMod.unitsMap hm))
  map_one' := by ext; simp
  map_mul' ψ₁ ψ₂ := by ext; simp

中文:
定义 changeLevel
  签名: {n m : 自然数} (hm : n ∣ m)
  定义体: MulChar.ofUnitHom (ψ.toUnitHom.comp (ZMod.unitsMap hm))
  map_one' := by ext; simp
  map_mul' ψ₁ ψ₂ := by ext; simp

Depends on / 依赖: MulChar, MulChar.ofUnitHom, ZMod.unitsMap, ofUnitHom, toUnitHom, toUnitHom.comp, unitsMap
-/
noncomputable def changeLevel {n m : Nat} (hm : n ∣ m) :
    DirichletCharacter R n ->* DirichletCharacter R m where
  toFun ψ := MulChar.ofUnitHom (ψ.toUnitHom.comp (ZMod.unitsMap hm))
  map_one' := by ext; simp
  map_mul' ψ₁ ψ₂ := by ext; simp

/--
lemma `changeLevel_def` / 引理 `changeLevel_def`

English:
lemma changeLevel_def
  given: {m : Nat} (hm : n ∣ m)
  proof: rfl

中文:
引理 changeLevel_def
  条件: {m : 自然数} (hm : n ∣ m)
  证明: rfl
-/
lemma changeLevel_def {m : Nat} (hm : n ∣ m) :
    changeLevel hm χ = MulChar.ofUnitHom (χ.toUnitHom.comp (ZMod.unitsMap hm)) := rfl

/--
lemma `changeLevel_toUnitHom` / 引理 `changeLevel_toUnitHom`

English:
lemma changeLevel_toUnitHom
  given: {m : Nat} (hm : n ∣ m)
  proof: by
  simp [changeLevel]

中文:
引理 changeLevel_toUnitHom
  条件: {m : 自然数} (hm : n ∣ m)
  证明: by
  simp [changeLevel]

Depends on / 依赖: changeLevel
-/
lemma changeLevel_toUnitHom {m : Nat} (hm : n ∣ m) :
    (changeLevel hm χ).toUnitHom = χ.toUnitHom.comp (ZMod.unitsMap hm) := by
  simp [changeLevel]

/--
lemma `changeLevel_injective` / 引理 `changeLevel_injective`

English:
lemma changeLevel_injective
  given: {m : Nat} [NeZero m] (hm : n ∣ m)
  proof: by
  intro _ _ h
  ext1 y
  obtain ⟨z, rfl⟩ := ZMod.unitsMap_surjective hm y
  rw [MulChar.ext_iff] at h
  simpa [changeLevel_def] using h z

@[simp]

中文:
引理 changeLevel_injective
  条件: {m : 自然数} [NeZero m] (hm : n ∣ m)
  证明: by
  intro _ _ h
  ext1 y
  obtain ⟨z, rfl⟩ := ZMod.unitsMap_surjective hm y
  rw [MulChar.ext_iff] at h
  simpa [changeLevel_def] using h z

@[simp]

Depends on / 依赖: MulChar, MulChar.ext_iff, ZMod.unitsMap_surjective, changeLevel_def, ext_iff, unitsMap_surjective
-/
lemma changeLevel_injective {m : Nat} [NeZero m] (hm : n ∣ m) :
    Function.Injective (changeLevel (R := R) hm) := by
  intro _ _ h
  ext1 y
  obtain ⟨z, rfl⟩ := ZMod.unitsMap_surjective hm y
  rw [MulChar.ext_iff] at h
  simpa [changeLevel_def] using h z

@[simp]
/--
lemma `changeLevel_eq_one_iff` / 引理 `changeLevel_eq_one_iff`

English:
lemma changeLevel_eq_one_iff
  given: {m : Nat} [NeZero m] {χ : DirichletCharacter R n} (hm : n ∣ m)
  proof: map_eq_one_iff _ (changeLevel_injective hm)

@[simp]

中文:
引理 changeLevel_eq_one_iff
  条件: {m : 自然数} [NeZero m] {χ : DirichletCharacter R n} (hm : n ∣ m)
  证明: map_eq_one_iff _ (changeLevel_injective hm)

@[simp]

Depends on / 依赖: changeLevel_injective, map_eq_one_iff
-/
lemma changeLevel_eq_one_iff {m : Nat} [NeZero m] {χ : DirichletCharacter R n} (hm : n ∣ m) :
    changeLevel hm χ = 1 ↔ χ = 1 :=
  map_eq_one_iff _ (changeLevel_injective hm)

@[simp]
/--
lemma `changeLevel_self` / 引理 `changeLevel_self`

English:
lemma changeLevel_self
  statement: changeLevel (dvd_refl n) χ = χ
  proof: by
  simp [changeLevel, ZMod.unitsMap]

中文:
引理 changeLevel_self
  结论: changeLevel (dvd_refl n) χ = χ
  证明: by
  simp [changeLevel, ZMod.unitsMap]

Depends on / 依赖: ZMod.unitsMap, changeLevel, unitsMap
-/
lemma changeLevel_self : changeLevel (dvd_refl n) χ = χ := by
  simp [changeLevel, ZMod.unitsMap]

/--
lemma `changeLevel_self_toUnitHom` / 引理 `changeLevel_self_toUnitHom`

English:
lemma changeLevel_self_toUnitHom
  statement: (changeLevel (dvd_refl n) χ).toUnitHom = χ.toUnitHom
  proof: by
  rw [changeLevel_self]

中文:
引理 changeLevel_self_toUnitHom
  结论: (changeLevel (dvd_refl n) χ).toUnitHom = χ.toUnitHom
  证明: by
  rw [changeLevel_self]

Depends on / 依赖: changeLevel_self
-/
lemma changeLevel_self_toUnitHom : (changeLevel (dvd_refl n) χ).toUnitHom = χ.toUnitHom := by
  rw [changeLevel_self]

/--
lemma `changeLevel_trans` / 引理 `changeLevel_trans`

English:
lemma changeLevel_trans
  given: {m d : Nat} (hm : n ∣ m) (hd : m ∣ d)
  proof: by
  simp [changeLevel_def, MonoidHom.comp_assoc, ZMod.unitsMap_comp]

中文:
引理 changeLevel_trans
  条件: {m d : 自然数} (hm : n ∣ m) (hd : m ∣ d)
  证明: by
  simp [changeLevel_def, MonoidHom.comp_assoc, ZMod.unitsMap_comp]

Depends on / 依赖: MonoidHom, MonoidHom.comp_assoc, ZMod.unitsMap_comp, changeLevel_def, comp_assoc, unitsMap_comp
-/
lemma changeLevel_trans {m d : Nat} (hm : n ∣ m) (hd : m ∣ d) :
    changeLevel (dvd_trans hm hd) χ = changeLevel hd (changeLevel hm χ) := by
  simp [changeLevel_def, MonoidHom.comp_assoc, ZMod.unitsMap_comp]

/--
lemma `changeLevel_eq_cast_of_dvd` / 引理 `changeLevel_eq_cast_of_dvd`

English:
lemma changeLevel_eq_cast_of_dvd
  given: {m : Nat} (hm : n ∣ m) (a : Units (ZMod m))
  proof: by
  simp [changeLevel_def, ZMod.unitsMap_val]

中文:
引理 changeLevel_eq_cast_of_dvd
  条件: {m : 自然数} (hm : n ∣ m) (a : 单位群 (ZMod m))
  证明: by
  simp [changeLevel_def, ZMod.unitsMap_val]

Depends on / 依赖: ZMod.unitsMap_val, changeLevel_def, unitsMap_val
-/
lemma changeLevel_eq_cast_of_dvd {m : Nat} (hm : n ∣ m) (a : Units (ZMod m)) :
    (changeLevel hm χ) a = χ (ZMod.cast (a : ZMod m)) := by
  simp [changeLevel_def, ZMod.unitsMap_val]

/--
lemma `changeLevel_eq_cast_of_dvd'` / 引理 `changeLevel_eq_cast_of_dvd'`

English:
lemma changeLevel_eq_cast_of_dvd'
  given: {m : Nat} (hm : n ∣ m) {a : Int} (ha : IsCoprime a m)
  proof: by
  rw [← ZMod.coe_unitOfIsCoprime _ ha]; rw [changeLevel_eq_cast_of_dvd _ hm]; rw [ZMod.coe_unitOfIsCoprime]; rw [ZMod.cast_intCast hm]

中文:
引理 changeLevel_eq_cast_of_dvd'
  条件: {m : 自然数} (hm : n ∣ m) {a : 整数} (ha : IsCoprime a m)
  证明: by
  rw [← ZMod.coe_unitOfIsCoprime _ ha]; rw [changeLevel_eq_cast_of_dvd _ hm]; rw [ZMod.coe_unitOfIsCoprime]; rw [ZMod.cast_intCast hm]

Depends on / 依赖: ZMod.cast_intCast, ZMod.coe_unitOfIsCoprime, cast_intCast, changeLevel_eq_cast_of_dvd, coe_unitOfIsCoprime
-/
lemma changeLevel_eq_cast_of_dvd' {m : Nat} (hm : n ∣ m) {a : Int} (ha : IsCoprime a m) :
    changeLevel hm χ a = χ a := by
  rw [← ZMod.coe_unitOfIsCoprime _ ha]; rw [changeLevel_eq_cast_of_dvd _ hm]; rw [ZMod.coe_unitOfIsCoprime]; rw [ZMod.cast_intCast hm]

/--
Definition of `FactorsThrough` / `FactorsThrough` 的定义

English:
definition FactorsThrough
  signature: (d : Nat)
  body: exists (h : d ∣ n) (χ₀ : DirichletCharacter R d), χ = changeLevel h χ₀

中文:
定义 FactorsThrough
  签名: (d : 自然数)
  定义体: exists (h : d ∣ n) (χ₀ : DirichletCharacter R d), χ = changeLevel h χ₀

Depends on / 依赖: DirichletCharacter, changeLevel
-/
def FactorsThrough (d : Nat) : Prop :=
  exists (h : d ∣ n) (χ₀ : DirichletCharacter R d), χ = changeLevel h χ₀

/--
lemma `changeLevel_factorsThrough` / 引理 `changeLevel_factorsThrough`

English:
lemma changeLevel_factorsThrough
  given: {m : Nat} (hm : n ∣ m)
  statement: FactorsThrough (changeLevel hm χ) n
  proof: ⟨hm, χ, rfl⟩

中文:
引理 changeLevel_factorsThrough
  条件: {m : 自然数} (hm : n ∣ m)
  结论: FactorsThrough (changeLevel hm χ) n
  证明: ⟨hm, χ, rfl⟩
-/
lemma changeLevel_factorsThrough {m : Nat} (hm : n ∣ m) : FactorsThrough (changeLevel hm χ) n :=
  ⟨hm, χ, rfl⟩

namespace FactorsThrough

variable {χ}

/--
lemma `dvd` / 引理 `dvd`

English:
lemma dvd
  given: {d : Nat} (h : FactorsThrough χ d)
  statement: d ∣ n
  proof: h.1

中文:
引理 dvd
  条件: {d : 自然数} (h : FactorsThrough χ d)
  结论: d ∣ n
  证明: h.1
-/
lemma dvd {d : Nat} (h : FactorsThrough χ d) : d ∣ n := h.1

/-- The Dirichlet character at level `d` through which `χ` factors -/
noncomputable
/--
Definition of `χ₀` / `χ₀` 的定义

English:
definition χ₀
  signature: {d : Nat} (h : FactorsThrough χ d)
  body: Classical.choose h.2

中文:
定义 χ₀
  签名: {d : 自然数} (h : FactorsThrough χ d)
  定义体: Classical.choose h.2

Depends on / 依赖: Classical, Classical.choose
-/
def χ₀ {d : Nat} (h : FactorsThrough χ d) : DirichletCharacter R d := Classical.choose h.2

/--
lemma `eq_changeLevel` / 引理 `eq_changeLevel`

English:
lemma eq_changeLevel
  given: {d : Nat} (h : FactorsThrough χ d)
  statement: χ = changeLevel h.dvd h.χ₀
  proof: Classical.choose_spec h.2

中文:
引理 eq_changeLevel
  条件: {d : 自然数} (h : FactorsThrough χ d)
  结论: χ = changeLevel h.dvd h.χ₀
  证明: Classical.choose_spec h.2

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec
-/
lemma eq_changeLevel {d : Nat} (h : FactorsThrough χ d) : χ = changeLevel h.dvd h.χ₀ :=
  Classical.choose_spec h.2

/--
lemma `existsUnique` / 引理 `existsUnique`

English:
lemma existsUnique
  given: {d : Nat} [NeZero n] (h : FactorsThrough χ d)
  proof: by
  rcases h with ⟨hd, χ₂, rfl⟩
  exact ⟨χ₂, rfl, fun χ₃ hχ₃ => (changeLevel_injective hd hχ₃).symm⟩

中文:
引理 存在Unique
  条件: {d : 自然数} [NeZero n] (h : FactorsThrough χ d)
  证明: by
  rcases h with ⟨hd, χ₂, rfl⟩
  exact ⟨χ₂, rfl, fun χ₃ hχ₃ => (changeLevel_injective hd hχ₃).symm⟩

Depends on / 依赖: changeLevel_injective
-/
lemma existsUnique {d : Nat} [NeZero n] (h : FactorsThrough χ d) :
    exists! χ' : DirichletCharacter R d, χ = changeLevel h.dvd χ' := by
  rcases h with ⟨hd, χ₂, rfl⟩
  exact ⟨χ₂, rfl, fun χ₃ hχ₃ => (changeLevel_injective hd hχ₃).symm⟩

variable (χ) in
/--
lemma `same_level` / 引理 `same_level`

English:
lemma same_level
  statement: FactorsThrough χ n
  proof: ⟨dvd_refl n, χ, (changeLevel_self χ).symm⟩

中文:
引理 same_level
  结论: FactorsThrough χ n
  证明: ⟨dvd_refl n, χ, (changeLevel_self χ).symm⟩

Depends on / 依赖: changeLevel_self, dvd_refl
-/
lemma same_level : FactorsThrough χ n := ⟨dvd_refl n, χ, (changeLevel_self χ).symm⟩

end FactorsThrough

variable {χ} in
/--
lemma `factorsThrough_iff_ker_unitsMap` / 引理 `factorsThrough_iff_ker_unitsMap`

English:
lemma factorsThrough_iff_ker_unitsMap
  given: {d : Nat} [NeZero n] (hd : d ∣ n)
  proof: by
  refine ⟨fun ⟨_, ⟨χ₀, hχ₀⟩⟩ x hx => ?_, fun h => ?_⟩
  · rw [MonoidHom.mem_ker, hχ₀, changeLevel_toUnitHom, MonoidHom.comp_apply, hx, map_one]
  · let E := MonoidHom.liftOfSurjective _ (ZMod.unitsMap_surjective hd) ⟨_, h⟩
    have hE : E.comp (ZMod.unitsMap hd) = χ.toUnitHom := MonoidHom.liftOfR

中文:
引理 factorsThrough_iff_ker_unitsMap
  条件: {d : 自然数} [NeZero n] (hd : d ∣ n)
  证明: by
  refine ⟨fun ⟨_, ⟨χ₀, hχ₀⟩⟩ x hx => ?_, fun h => ?_⟩
  · rw [MonoidHom.mem_ker, hχ₀, changeLevel_toUnitHom, MonoidHom.comp_apply, hx, map_one]
  · let E := MonoidHom.liftOfSurjective _ (ZMod.unitsMap_surjective hd) ⟨_, h⟩
    have hE : E.comp (ZMod.unitsMap hd) = χ.toUnitHom := MonoidHom.liftOfR

Depends on / 依赖: E.comp, Equiv.apply_symm_apply, MonoidHom, MonoidHom.comp_apply, MonoidHom.liftOfRightInverse_comp, MonoidHom.liftOfSurjective, MonoidHom.mem_ker, MulChar, MulChar.ofUnitHom, ZMod.unitsMap, ZMod.unitsMap_surjective, apply_symm_apply, changeLevel_toUnitHom, comp_apply, equivToUnitHom, equivToUnitHom.injective, injective, liftOfRightInverse_comp, liftOfSurjective, map_one
-/
lemma factorsThrough_iff_ker_unitsMap {d : Nat} [NeZero n] (hd : d ∣ n) :
    FactorsThrough χ d ↔ (ZMod.unitsMap hd).ker <= χ.toUnitHom.ker := by
  refine ⟨fun ⟨_, ⟨χ₀, hχ₀⟩⟩ x hx => ?_, fun h => ?_⟩
  · rw [MonoidHom.mem_ker, hχ₀, changeLevel_toUnitHom, MonoidHom.comp_apply, hx, map_one]
  · let E := MonoidHom.liftOfSurjective _ (ZMod.unitsMap_surjective hd) ⟨_, h⟩
    have hE : E.comp (ZMod.unitsMap hd) = χ.toUnitHom := MonoidHom.liftOfRightInverse_comp ..
    refine ⟨hd, MulChar.ofUnitHom E, equivToUnitHom.injective (?_ : toUnitHom _ = toUnitHom _)⟩
    simp_rw [changeLevel_toUnitHom, toUnitHom_eq, ofUnitHom_eq, Equiv.apply_symm_apply, hE,
      toUnitHom_eq]

/--
theorem `FactorsThrough.mono` / 定理 `FactorsThrough.mono`

English:
theorem FactorsThrough.mono
  statement: {d m : Nat} [NeZero n] (hχ : FactorsThrough χ d) (hd : d ∣ m)
  proof: by
  refine (factorsThrough_iff_ker_unitsMap hm).mpr fun x hx => ?_
  apply (factorsThrough_iff_ker_unitsMap hχ.dvd).mp hχ
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [← ZMod.unitsMap_comp hd hm]; rw [MonoidHom.comp_apply]; rw [hx]; rw [map_one]

中文:
定理 FactorsThrough.mono
  结论: {d m : 自然数} [NeZero n] (hχ : FactorsThrough χ d) (hd : d ∣ m)
  证明: by
  refine (factorsThrough_iff_ker_unitsMap hm).mpr fun x hx => ?_
  apply (factorsThrough_iff_ker_unitsMap hχ.dvd).mp hχ
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [← ZMod.unitsMap_comp hd hm]; rw [MonoidHom.comp_apply]; rw [hx]; rw [map_one]

Depends on / 依赖: MonoidHom, MonoidHom.comp_apply, MonoidHom.mem_ker, ZMod.unitsMap_comp, comp_apply, factorsThrough_iff_ker_unitsMap, map_one, mem_ker, unitsMap_comp
-/
theorem FactorsThrough.mono {d m : Nat} [NeZero n] (hχ : FactorsThrough χ d) (hd : d ∣ m)
    (hm : m ∣ n) :
    FactorsThrough χ m := by
  refine (factorsThrough_iff_ker_unitsMap hm).mpr fun x hx => ?_
  apply (factorsThrough_iff_ker_unitsMap hχ.dvd).mp hχ
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [← ZMod.unitsMap_comp hd hm]; rw [MonoidHom.comp_apply]; rw [hx]; rw [map_one]

/--
theorem `factorsThrough_gcd` / 定理 `factorsThrough_gcd`

English:
theorem factorsThrough_gcd
  statement: {m : Nat} [NeZero n] (ψ : DirichletCharacter R m)
  proof: by
  refine (factorsThrough_iff_ker_unitsMap (n.gcd_dvd_left m)).mpr fun x hx =>
    MonoidHom.mem_ker.mpr ?_
  rw [Units.ext_iff]; rw [MulChar.coe_toUnitHom]; rw [Units.val_one]
  obtain ⟨z, hz₁, hz₂⟩ : exists z : Nat, z = x.val ∧ (z : ZMod m) = 1 := by
    suffices x.val.val ≡ 1 [MOD n.gcd m] by
 

中文:
定理 factorsThrough_gcd
  结论: {m : 自然数} [NeZero n] (ψ : DirichletCharacter R m)
  证明: by
  refine (factorsThrough_iff_ker_unitsMap (n.gcd_dvd_left m)).mpr fun x hx =>
    MonoidHom.mem_ker.mpr ?_
  rw [Units.ext_iff]; rw [MulChar.coe_toUnitHom]; rw [Units.val_one]
  obtain ⟨z, hz₁, hz₂⟩ : exists z : Nat, z = x.val ∧ (z : ZMod m) = 1 := by
    suffices x.val.val ≡ 1 [MOD n.gcd m] by
 

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, MonoidHom.mem_ker.mpr, MulChar, MulChar.coe_toUnitHom, Nat.cast_one, Nat.chineseRemainder, Units.ext_if, Units.ext_iff, Units.val_one, ZMod.natCast_eq_natCast_iff, cast_one, chineseRemainder, coe_toUnitHom, ext_if, ext_iff, factorsThrough_iff_ker_unitsMap, gcd_dvd_left, mem_ker, n.gcd
-/
theorem factorsThrough_gcd {m : Nat} [NeZero n] (ψ : DirichletCharacter R m)
    (h : χ.changeLevel (n.dvd_mul_right m) = ψ.changeLevel (m.dvd_mul_left n)) :
    χ.FactorsThrough (n.gcd m) := by
  refine (factorsThrough_iff_ker_unitsMap (n.gcd_dvd_left m)).mpr fun x hx =>
    MonoidHom.mem_ker.mpr ?_
  rw [Units.ext_iff]; rw [MulChar.coe_toUnitHom]; rw [Units.val_one]
  obtain ⟨z, hz₁, hz₂⟩ : exists z : Nat, z = x.val ∧ (z : ZMod m) = 1 := by
    suffices x.val.val ≡ 1 [MOD n.gcd m] by
      obtain ⟨z, hz₁, hz₂⟩ := Nat.chineseRemainder' this
      refine ⟨z, ?_, ?_⟩
      · simpa [← ZMod.natCast_eq_natCast_iff] using hz₁
      · rwa [← ZMod.natCast_eq_natCast_iff, Nat.cast_one] at hz₂
    rwa [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
      Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at hx
  have hz₀ : z.gcd (n * m) = 1 := by
    refine Nat.Coprime.mul_right ?_ ?_
· exact (ZMod.isUnit_iff_coprime _ _).mp hz₁ ▸ x.isUnit
· exact (ZMod.isUnit_iff_coprime _ _).mp hz₂ ▸ isUnit_one
  have := changeLevel_eq_cast_of_dvd χ (n.dvd_mul_right m) (ZMod.unitOfCoprime z hz₀)
  simp only [ZMod.coe_unitOfCoprime, dvd_mul_right, ZMod.cast_natCast] at this
  rw [← hz₁]; rw [← this]; rw [h]
  have := changeLevel_eq_cast_of_dvd ψ (m.dvd_mul_left n) (ZMod.unitOfCoprime z hz₀)
  simp only [ZMod.coe_unitOfCoprime, dvd_mul_left, ZMod.cast_natCast] at this
  rw [this]; rw [hz₂]; rw [map_one]


/--
lemma `level_one` / 引理 `level_one`

English:
lemma level_one
  given: (χ : DirichletCharacter R 1)
  statement: χ = 1
  proof: by
  ext
  simp [Units.eq_one]

中文:
引理 level_one
  条件: (χ : DirichletCharacter R 1)
  结论: χ = 1
  证明: by
  ext
  simp [Units.eq_one]

Depends on / 依赖: Units.eq_one, eq_one
-/
lemma level_one (χ : DirichletCharacter R 1) : χ = 1 := by
  ext
  simp [Units.eq_one]

/--
lemma `level_one'` / 引理 `level_one'`

English:
lemma level_one'
  given: (hn : n = 1)
  statement: χ = 1
  proof: by
  subst hn
  exact level_one _

中文:
引理 level_one'
  条件: (hn : n = 1)
  结论: χ = 1
  证明: by
  subst hn
  exact level_one _

Depends on / 依赖: level_one
-/
lemma level_one' (hn : n = 1) : χ = 1 := by
  subst hn
  exact level_one _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (DirichletCharacter R 1)
  body: by
  refine subsingleton_iff.mpr (fun χ χ' => ?_)
  simp [level_one]

中文:
实例 :
  签名: 子单例 (DirichletCharacter R 1)
  定义体: by
  refine subsingleton_iff.mpr (fun χ χ' => ?_)
  simp [level_one]

Depends on / 依赖: level_one, subsingleton_iff, subsingleton_iff.mpr
-/
instance : Subsingleton (DirichletCharacter R 1) := by
  refine subsingleton_iff.mpr (fun χ χ' => ?_)
  simp [level_one]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (DirichletCharacter R 1)
  body: Unique.mk' (DirichletCharacter R 1)

中文:
实例 :
  签名: 唯一 (DirichletCharacter R 1)
  定义体: Unique.mk' (DirichletCharacter R 1)

Depends on / 依赖: DirichletCharacter, Unique, Unique.mk
-/
noncomputable instance : Unique (DirichletCharacter R 1) := Unique.mk' (DirichletCharacter R 1)

/--
lemma `map_zero'` / 引理 `map_zero'`

English:
lemma map_zero'
  given: (hn : n != 1)
  statement: χ 0 = 0
  proof: have := ZMod.nontrivial_iff.mpr hn; χ.map_zero

中文:
引理 map_zero'
  条件: (hn : n != 1)
  结论: χ 0 = 0
  证明: have := ZMod.nontrivial_iff.mpr hn; χ.map_zero

Depends on / 依赖: ZMod.nontrivial_iff.mpr, map_zero, nontrivial_iff
-/
lemma map_zero' (hn : n != 1) : χ 0 = 0 :=
  have := ZMod.nontrivial_iff.mpr hn; χ.map_zero

/--
lemma `changeLevel_one` / 引理 `changeLevel_one`

English:
lemma changeLevel_one
  given: {d : Nat} (h : d ∣ n)
  proof: by
  simp

中文:
引理 changeLevel_one
  条件: {d : 自然数} (h : d ∣ n)
  证明: by
  simp
-/
lemma changeLevel_one {d : Nat} (h : d ∣ n) :
    changeLevel h (1 : DirichletCharacter R d) = 1 := by
  simp

/--
lemma `factorsThrough_one_iff` / 引理 `factorsThrough_one_iff`

English:
lemma factorsThrough_one_iff
  statement: FactorsThrough χ 1 ↔ χ = 1
  proof: by
  refine ⟨fun ⟨_, χ₀, hχ₀⟩ => ?_,
          fun h => ⟨one_dvd n, 1, by rw [h, changeLevel_one]⟩⟩
  rwa [level_one χ₀, changeLevel_one] at hχ₀

中文:
引理 factorsThrough_one_iff
  结论: FactorsThrough χ 1 ↔ χ = 1
  证明: by
  refine ⟨fun ⟨_, χ₀, hχ₀⟩ => ?_,
          fun h => ⟨one_dvd n, 1, by rw [h, changeLevel_one]⟩⟩
  rwa [level_one χ₀, changeLevel_one] at hχ₀

Depends on / 依赖: changeLevel_one, level_one, one_dvd
-/
lemma factorsThrough_one_iff : FactorsThrough χ 1 ↔ χ = 1 := by
  refine ⟨fun ⟨_, χ₀, hχ₀⟩ => ?_,
          fun h => ⟨one_dvd n, 1, by rw [h, changeLevel_one]⟩⟩
  rwa [level_one χ₀, changeLevel_one] at hχ₀

/-!
### The conductor
-/

/--
Definition of `conductorSet` / `conductorSet` 的定义

English:
definition conductorSet
  signature: : Set Nat
  body: {d : Nat | FactorsThrough χ d}

中文:
定义 conductorSet
  签名: : 集合 自然数
  定义体: {d : Nat | FactorsThrough χ d}

Depends on / 依赖: FactorsThrough
-/
def conductorSet : Set Nat := {d : Nat | FactorsThrough χ d}

/--
lemma `mem_conductorSet_iff` / 引理 `mem_conductorSet_iff`

English:
lemma mem_conductorSet_iff
  given: {x : Nat}
  statement: x in conductorSet χ ↔ FactorsThrough χ x
  proof: Iff.refl _

中文:
引理 mem_conductorSet_iff
  条件: {x : 自然数}
  结论: x in conductorSet χ ↔ FactorsThrough χ x
  证明: Iff.refl _

Depends on / 依赖: Iff.refl
-/
lemma mem_conductorSet_iff {x : Nat} : x in conductorSet χ ↔ FactorsThrough χ x := Iff.refl _

/--
lemma `level_mem_conductorSet` / 引理 `level_mem_conductorSet`

English:
lemma level_mem_conductorSet
  statement: n in conductorSet χ
  proof: FactorsThrough.same_level χ

中文:
引理 level_mem_conductorSet
  结论: n in conductorSet χ
  证明: FactorsThrough.same_level χ

Depends on / 依赖: FactorsThrough, FactorsThrough.same_level, same_level
-/
lemma level_mem_conductorSet : n in conductorSet χ := FactorsThrough.same_level χ

/--
lemma `mem_conductorSet_dvd` / 引理 `mem_conductorSet_dvd`

English:
lemma mem_conductorSet_dvd
  given: {x : Nat} (hx : x in conductorSet χ)
  statement: x ∣ n
  proof: hx.dvd

中文:
引理 mem_conductorSet_dvd
  条件: {x : 自然数} (hx : x in conductorSet χ)
  结论: x ∣ n
  证明: hx.dvd

Depends on / 依赖: hx.dvd
-/
lemma mem_conductorSet_dvd {x : Nat} (hx : x in conductorSet χ) : x ∣ n := hx.dvd

/--
theorem `zero_ne_mem_conductorSet` / 定理 `zero_ne_mem_conductorSet`

English:
theorem zero_ne_mem_conductorSet
  given: [NeZero n]
  statement: 0 ∉ χ.conductorSet
  proof: fun h => NeZero.ne n Nat.eq_zero_of_zero_dvd FactorsThrough.dvd h

中文:
定理 zero_ne_mem_conductorSet
  条件: [NeZero n]
  结论: 0 ∉ χ.conductorSet
  证明: fun h => NeZero.ne n Nat.eq_zero_of_zero_dvd FactorsThrough.dvd h

Depends on / 依赖: FactorsThrough, FactorsThrough.dvd, Nat.eq_zero_of_zero_dvd, NeZero, NeZero.ne, eq_zero_of_zero_dvd
-/
theorem zero_ne_mem_conductorSet [NeZero n] : 0 ∉ χ.conductorSet :=
fun h => NeZero.ne n Nat.eq_zero_of_zero_dvd FactorsThrough.dvd h

/--
Definition of `conductor` / `conductor` 的定义

English:
definition conductor
  signature: : Nat
  body: sInf (conductorSet χ)

中文:
定义 conductor
  签名: : 自然数
  定义体: sInf (conductorSet χ)

Depends on / 依赖: conductorSet
-/
noncomputable def conductor : Nat := sInf (conductorSet χ)

/--
lemma `conductor_mem_conductorSet` / 引理 `conductor_mem_conductorSet`

English:
lemma conductor_mem_conductorSet
  statement: conductor χ in conductorSet χ
  proof: Nat.sInf_mem (Set.nonempty_of_mem (level_mem_conductorSet χ))

中文:
引理 conductor_mem_conductorSet
  结论: conductor χ in conductorSet χ
  证明: Nat.sInf_mem (Set.nonempty_of_mem (level_mem_conductorSet χ))

Depends on / 依赖: Nat.sInf_mem, Set.nonempty_of_mem, level_mem_conductorSet, nonempty_of_mem, sInf_mem
-/
lemma conductor_mem_conductorSet : conductor χ in conductorSet χ :=
  Nat.sInf_mem (Set.nonempty_of_mem (level_mem_conductorSet χ))

/--
lemma `conductor_dvd_level` / 引理 `conductor_dvd_level`

English:
lemma conductor_dvd_level
  statement: conductor χ ∣ n
  proof: (conductor_mem_conductorSet χ).dvd

中文:
引理 conductor_dvd_level
  结论: conductor χ ∣ n
  证明: (conductor_mem_conductorSet χ).dvd

Depends on / 依赖: conductor_mem_conductorSet
-/
lemma conductor_dvd_level : conductor χ ∣ n := (conductor_mem_conductorSet χ).dvd

/--
lemma `factorsThrough_conductor` / 引理 `factorsThrough_conductor`

English:
lemma factorsThrough_conductor
  statement: FactorsThrough χ (conductor χ)
  proof: conductor_mem_conductorSet χ

中文:
引理 factorsThrough_conductor
  结论: FactorsThrough χ (conductor χ)
  证明: conductor_mem_conductorSet χ

Depends on / 依赖: conductor_mem_conductorSet
-/
lemma factorsThrough_conductor : FactorsThrough χ (conductor χ) := conductor_mem_conductorSet χ

/--
lemma `conductor_ne_zero` / 引理 `conductor_ne_zero`

English:
lemma conductor_ne_zero
  given: [NeZero n]
  statement: conductor χ != 0
  proof: fun h => NeZero.ne n Nat.eq_zero_of_zero_dvd h ▸ conductor_dvd_level _

中文:
引理 conductor_ne_zero
  条件: [NeZero n]
  结论: conductor χ != 0
  证明: fun h => NeZero.ne n Nat.eq_zero_of_zero_dvd h ▸ conductor_dvd_level _

Depends on / 依赖: Nat.eq_zero_of_zero_dvd, NeZero, NeZero.ne, conductor_dvd_level, eq_zero_of_zero_dvd
-/
lemma conductor_ne_zero [NeZero n] : conductor χ != 0 :=
fun h => NeZero.ne n Nat.eq_zero_of_zero_dvd h ▸ conductor_dvd_level _

/--
lemma `conductor_one` / 引理 `conductor_one`

English:
lemma conductor_one
  given: [NeZero n]
  statement: conductor (1 : DirichletCharacter R n) = 1
  proof: by
  suffices FactorsThrough (1 : DirichletCharacter R n) 1 by
    have h : conductor (1 : DirichletCharacter R n) <= 1 :=
Nat.sInf_le (mem_conductorSet_iff _).mpr this
    exact Nat.le_antisymm h (Nat.pos_of_ne_zero <| conductor_ne_zero _)
  exact (factorsThrough_one_iff _).mpr rfl

中文:
引理 conductor_one
  条件: [NeZero n]
  结论: conductor (1 : DirichletCharacter R n) = 1
  证明: by
  suffices FactorsThrough (1 : DirichletCharacter R n) 1 by
    have h : conductor (1 : DirichletCharacter R n) <= 1 :=
Nat.sInf_le (mem_conductorSet_iff _).mpr this
    exact Nat.le_antisymm h (Nat.pos_of_ne_zero <| conductor_ne_zero _)
  exact (factorsThrough_one_iff _).mpr rfl

Depends on / 依赖: DirichletCharacter, FactorsThrough, Nat.le_antisymm, Nat.pos_of_ne_zero, Nat.sInf_le, conductor, conductor_ne_zero, factorsThrough_one_iff, le_antisymm, mem_conductorSet_iff, pos_of_ne_zero, sInf_le
-/
lemma conductor_one [NeZero n] : conductor (1 : DirichletCharacter R n) = 1 := by
  suffices FactorsThrough (1 : DirichletCharacter R n) 1 by
    have h : conductor (1 : DirichletCharacter R n) <= 1 :=
Nat.sInf_le (mem_conductorSet_iff _).mpr this
    exact Nat.le_antisymm h (Nat.pos_of_ne_zero <| conductor_ne_zero _)
  exact (factorsThrough_one_iff _).mpr rfl

variable {χ}

/--
lemma `eq_one_iff_conductor_eq_one` / 引理 `eq_one_iff_conductor_eq_one`

English:
lemma eq_one_iff_conductor_eq_one
  given: [NeZero n]
  statement: χ = 1 ↔ conductor χ = 1
  proof: by
  refine ⟨fun h => h ▸ conductor_one, fun hχ => ?_⟩
  obtain ⟨h', χ₀, h⟩ := factorsThrough_conductor χ
exact (level_one' χ₀ hχ ▸ h).trans changeLevel_one h'

中文:
引理 eq_one_iff_conductor_eq_one
  条件: [NeZero n]
  结论: χ = 1 ↔ conductor χ = 1
  证明: by
  refine ⟨fun h => h ▸ conductor_one, fun hχ => ?_⟩
  obtain ⟨h', χ₀, h⟩ := factorsThrough_conductor χ
exact (level_one' χ₀ hχ ▸ h).trans changeLevel_one h'

Depends on / 依赖: changeLevel_one, conductor_one, factorsThrough_conductor, level_one
-/
lemma eq_one_iff_conductor_eq_one [NeZero n] : χ = 1 ↔ conductor χ = 1 := by
  refine ⟨fun h => h ▸ conductor_one, fun hχ => ?_⟩
  obtain ⟨h', χ₀, h⟩ := factorsThrough_conductor χ
exact (level_one' χ₀ hχ ▸ h).trans changeLevel_one h'

/--
lemma `conductor_eq_zero_iff_level_eq_zero` / 引理 `conductor_eq_zero_iff_level_eq_zero`

English:
lemma conductor_eq_zero_iff_level_eq_zero
  statement: conductor χ = 0 ↔ n = 0
  proof: by
  refine ⟨?_, ?_⟩
  · contrapose!
    exact fun h => @conductor_ne_zero _ _ _ χ ⟨h⟩
  · rintro rfl
exact Nat.sInf_eq_zero.mpr Or.inl level_mem_conductorSet χ

中文:
引理 conductor_eq_zero_iff_level_eq_zero
  结论: conductor χ = 0 ↔ n = 0
  证明: by
  refine ⟨?_, ?_⟩
  · contrapose!
    exact fun h => @conductor_ne_zero _ _ _ χ ⟨h⟩
  · rintro rfl
exact Nat.sInf_eq_zero.mpr Or.inl level_mem_conductorSet χ

Depends on / 依赖: Nat.sInf_eq_zero.mpr, Or.inl, conductor_ne_zero, contrapose, level_mem_conductorSet, sInf_eq_zero
-/
lemma conductor_eq_zero_iff_level_eq_zero : conductor χ = 0 ↔ n = 0 := by
  refine ⟨?_, ?_⟩
  · contrapose!
    exact fun h => @conductor_ne_zero _ _ _ χ ⟨h⟩
  · rintro rfl
exact Nat.sInf_eq_zero.mpr Or.inl level_mem_conductorSet χ

/--
lemma `conductor_le_conductor_mem_conductorSet` / 引理 `conductor_le_conductor_mem_conductorSet`

English:
lemma conductor_le_conductor_mem_conductorSet
  given: {d : Nat} (hd : d in conductorSet χ)
  proof: by
refine Nat.sInf_le (mem_conductorSet_iff χ).mpr
    ⟨dvd_trans (conductor_dvd_level _) hd.1,
     (factorsThrough_conductor (Classical.choose hd.2)).2.choose, ?_⟩
  rw [changeLevel_trans _ (conductor_dvd_level _) hd.dvd]; rw [← (factorsThrough_conductor (Classical.choose hd.2)).2.choose_spec]
  e

中文:
引理 conductor_le_conductor_mem_conductorSet
  条件: {d : 自然数} (hd : d in conductorSet χ)
  证明: by
refine Nat.sInf_le (mem_conductorSet_iff χ).mpr
    ⟨dvd_trans (conductor_dvd_level _) hd.1,
     (factorsThrough_conductor (Classical.choose hd.2)).2.choose, ?_⟩
  rw [changeLevel_trans _ (conductor_dvd_level _) hd.dvd]; rw [← (factorsThrough_conductor (Classical.choose hd.2)).2.choose_spec]
  e

Depends on / 依赖: Classical, Classical.choose, Nat.sInf_le, changeLevel_trans, choose_spec, conductor_dvd_level, dvd_trans, eq_changeLevel, factorsThrough_conductor, hd.dvd, hd.eq_changeLevel, mem_conductorSet_iff, sInf_le
-/
lemma conductor_le_conductor_mem_conductorSet {d : Nat} (hd : d in conductorSet χ) :
    χ.conductor <= (Classical.choose hd.2).conductor := by
refine Nat.sInf_le (mem_conductorSet_iff χ).mpr
    ⟨dvd_trans (conductor_dvd_level _) hd.1,
     (factorsThrough_conductor (Classical.choose hd.2)).2.choose, ?_⟩
  rw [changeLevel_trans _ (conductor_dvd_level _) hd.dvd]; rw [← (factorsThrough_conductor (Classical.choose hd.2)).2.choose_spec]
  exact hd.eq_changeLevel

variable (χ)

/--
Definition of `IsPrimitive` / `IsPrimitive` 的定义

English:
definition IsPrimitive
  signature: : Prop
  body: conductor χ = n

中文:
定义 是Primitive
  签名: : 命题
  定义体: conductor χ = n

Depends on / 依赖: conductor
-/
def IsPrimitive : Prop := conductor χ = n

/--
lemma `isPrimitive_def` / 引理 `isPrimitive_def`

English:
lemma isPrimitive_def
  statement: IsPrimitive χ ↔ conductor χ = n
  proof: Iff.rfl

中文:
引理 isPrimitive_def
  结论: 是Primitive χ ↔ conductor χ = n
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isPrimitive_def : IsPrimitive χ ↔ conductor χ = n := Iff.rfl

/--
lemma `isPrimitive_one_level_one` / 引理 `isPrimitive_one_level_one`

English:
lemma isPrimitive_one_level_one
  statement: IsPrimitive (1 : DirichletCharacter R 1)
  proof: Nat.dvd_one.mp (conductor_dvd_level _)

中文:
引理 isPrimitive_one_level_one
  结论: 是Primitive (1 : DirichletCharacter R 1)
  证明: Nat.dvd_one.mp (conductor_dvd_level _)

Depends on / 依赖: Nat.dvd_one.mp, conductor_dvd_level, dvd_one
-/
lemma isPrimitive_one_level_one : IsPrimitive (1 : DirichletCharacter R 1) :=
  Nat.dvd_one.mp (conductor_dvd_level _)

/--
lemma `isPrimitive_one_level_zero` / 引理 `isPrimitive_one_level_zero`

English:
lemma isPrimitive_one_level_zero
  statement: IsPrimitive (1 : DirichletCharacter R 0)
  proof: conductor_eq_zero_iff_level_eq_zero.mpr rfl

中文:
引理 isPrimitive_one_level_zero
  结论: 是Primitive (1 : DirichletCharacter R 0)
  证明: conductor_eq_zero_iff_level_eq_zero.mpr rfl

Depends on / 依赖: conductor_eq_zero_iff_level_eq_zero, conductor_eq_zero_iff_level_eq_zero.mpr
-/
lemma isPrimitive_one_level_zero : IsPrimitive (1 : DirichletCharacter R 0) :=
  conductor_eq_zero_iff_level_eq_zero.mpr rfl

/--
lemma `conductor_one_dvd` / 引理 `conductor_one_dvd`

English:
lemma conductor_one_dvd
  given: (n : Nat)
  statement: conductor (1 : DirichletCharacter R 1) ∣ n
  proof: by
  rw [(isPrimitive_def _).mp isPrimitive_one_level_one]
  apply one_dvd _

中文:
引理 conductor_one_dvd
  条件: (n : 自然数)
  结论: conductor (1 : DirichletCharacter R 1) ∣ n
  证明: by
  rw [(isPrimitive_def _).mp isPrimitive_one_level_one]
  apply one_dvd _

Depends on / 依赖: isPrimitive_def, isPrimitive_one_level_one, one_dvd
-/
lemma conductor_one_dvd (n : Nat) : conductor (1 : DirichletCharacter R 1) ∣ n := by
  rw [(isPrimitive_def _).mp isPrimitive_one_level_one]
  apply one_dvd _

/--
Definition of `primitiveCharacter` / `primitiveCharacter` 的定义

English:
definition primitiveCharacter
  signature: : DirichletCharacter R χ.conductor
  body: Classical.choose (factorsThrough_conductor χ).choose_spec

中文:
定义 primitiveCharacter
  签名: : DirichletCharacter R χ.conductor
  定义体: Classical.choose (factorsThrough_conductor χ).choose_spec

Depends on / 依赖: Classical, Classical.choose, choose_spec, factorsThrough_conductor
-/
noncomputable def primitiveCharacter : DirichletCharacter R χ.conductor :=
  Classical.choose (factorsThrough_conductor χ).choose_spec

/--
theorem `changeLevel_primitiveCharacter` / 定理 `changeLevel_primitiveCharacter`

English:
theorem changeLevel_primitiveCharacter
  proof: (factorsThrough_conductor χ).choose_spec.choose_spec.symm

中文:
定理 changeLevel_primitiveCharacter
  证明: (factorsThrough_conductor χ).choose_spec.choose_spec.symm

Depends on / 依赖: choose_spec, choose_spec.choose_spec.symm, factorsThrough_conductor
-/
theorem changeLevel_primitiveCharacter :
    (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ :=
  (factorsThrough_conductor χ).choose_spec.choose_spec.symm

/--
lemma `primitiveCharacter_isPrimitive` / 引理 `primitiveCharacter_isPrimitive`

English:
lemma primitiveCharacter_isPrimitive
  statement: IsPrimitive (χ.primitiveCharacter)
  proof: by
  by_cases h : χ.conductor = 0
  · rw [isPrimitive_def]
    convert! conductor_eq_zero_iff_level_eq_zero.mpr h
· exact le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (conductor_dvd_level _))
conductor_le_conductor_mem_conductorSet conductor_mem_conductorSet χ

中文:
引理 primitiveCharacter_isPrimitive
  结论: 是Primitive (χ.primitiveCharacter)
  证明: by
  by_cases h : χ.conductor = 0
  · rw [isPrimitive_def]
    convert! conductor_eq_zero_iff_level_eq_zero.mpr h
· exact le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (conductor_dvd_level _))
conductor_le_conductor_mem_conductorSet conductor_mem_conductorSet χ

Depends on / 依赖: Nat.le_of_dvd, Nat.pos_of_ne_zero, conductor, conductor_dvd_level, conductor_eq_zero_iff_level_eq_zero, conductor_eq_zero_iff_level_eq_zero.mpr, conductor_le_conductor_mem_conductorSet, conductor_mem_conductorSet, convert, isPrimitive_def, le_antisymm, le_of_dvd, pos_of_ne_zero
-/
lemma primitiveCharacter_isPrimitive : IsPrimitive (χ.primitiveCharacter) := by
  by_cases h : χ.conductor = 0
  · rw [isPrimitive_def]
    convert! conductor_eq_zero_iff_level_eq_zero.mpr h
· exact le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (conductor_dvd_level _))
conductor_le_conductor_mem_conductorSet conductor_mem_conductorSet χ

/--
lemma `primitiveCharacter_one` / 引理 `primitiveCharacter_one`

English:
lemma primitiveCharacter_one
  given: [NeZero n]
  statement: (1 : DirichletCharacter R n).primitiveCharacter = 1
  proof: by
  have : NeZero (conductor (1 : DirichletCharacter R n)) :=
    ⟨@conductor_one R _ n _ ▸ Nat.one_ne_zero⟩
  rw [eq_one_iff_conductor_eq_one]; rw [(isPrimitive_def _).1 (1 : DirichletCharacter R n).primitiveCharacter_isPrimitive]; rw [conductor_one]

中文:
引理 primitiveCharacter_one
  条件: [NeZero n]
  结论: (1 : DirichletCharacter R n).primitiveCharacter = 1
  证明: by
  have : NeZero (conductor (1 : DirichletCharacter R n)) :=
    ⟨@conductor_one R _ n _ ▸ Nat.one_ne_zero⟩
  rw [eq_one_iff_conductor_eq_one]; rw [(isPrimitive_def _).1 (1 : DirichletCharacter R n).primitiveCharacter_isPrimitive]; rw [conductor_one]

Depends on / 依赖: DirichletCharacter, Nat.one_ne_zero, NeZero, conductor, conductor_one, eq_one_iff_conductor_eq_one, isPrimitive_def, one_ne_zero, primitiveCharacter_isPrimitive
-/
lemma primitiveCharacter_one [NeZero n] : (1 : DirichletCharacter R n).primitiveCharacter = 1 := by
  have : NeZero (conductor (1 : DirichletCharacter R n)) :=
    ⟨@conductor_one R _ n _ ▸ Nat.one_ne_zero⟩
  rw [eq_one_iff_conductor_eq_one]; rw [(isPrimitive_def _).1 (1 : DirichletCharacter R n).primitiveCharacter_isPrimitive]; rw [conductor_one]

/--
theorem `primitiveCharacter_apply_of_isCoprime` / 定理 `primitiveCharacter_apply_of_isCoprime`

English:
theorem primitiveCharacter_apply_of_isCoprime
  given: {a : Int} (ha : IsCoprime a n)
  proof: by
  rw [← changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level ha]; rw [changeLevel_primitiveCharacter]

中文:
定理 primitiveCharacter_apply_of_isCoprime
  条件: {a : 整数} (ha : IsCoprime a n)
  证明: by
  rw [← changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level ha]; rw [changeLevel_primitiveCharacter]

Depends on / 依赖: changeLevel_eq_cast_of_dvd, changeLevel_primitiveCharacter, conductor_dvd_level, primitiveCharacter
-/
theorem primitiveCharacter_apply_of_isCoprime {a : Int} (ha : IsCoprime a n) :
    χ.primitiveCharacter a = χ a := by
  rw [← changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level ha]; rw [changeLevel_primitiveCharacter]

/--
theorem `conductor_dvd_of_mem_conductorSet` / 定理 `conductor_dvd_of_mem_conductorSet`

English:
theorem conductor_dvd_of_mem_conductorSet
  given: {d : Nat} [NeZero n] (hd : d in χ.conductorSet)
  proof: by
  have : NeZero d := ⟨by
    contrapose hd
    exact hd ▸ zero_ne_mem_conductorSet χ⟩
  suffices d.gcd χ.conductor in χ.conductorSet by
    have : χ.conductor <= d.gcd χ.conductor := Nat.sInf_le this
    contrapose! this
    refine Nat.lt_of_le_of_ne ?_ (Nat.gcd_eq_right_iff_dvd.not.mpr this)
exa

中文:
定理 conductor_dvd_of_mem_conductorSet
  条件: {d : 自然数} [NeZero n] (hd : d in χ.conductorSet)
  证明: by
  have : NeZero d := ⟨by
    contrapose hd
    exact hd ▸ zero_ne_mem_conductorSet χ⟩
  suffices d.gcd χ.conductor in χ.conductorSet by
    have : χ.conductor <= d.gcd χ.conductor := Nat.sInf_le this
    contrapose! this
    refine Nat.lt_of_le_of_ne ?_ (Nat.gcd_eq_right_iff_dvd.not.mpr this)
exa

Depends on / 依赖: Nat.gcd_eq_right_iff_dvd.not.mpr, Nat.gcd_le_right, Nat.lt_of_le_of_ne, Nat.pos_of_ne_zero, Nat.sInf_le, NeZero, changeLevel, conductor, conductor.dvd_mul_left, conductorSet, conductor_ne_zero, contrapose, d.dvd_mul_right, d.gcd, dvd_mul_left, dvd_mul_right, gcd_eq_right_iff_dvd, gcd_le_right, lt_of_le_of_ne, pos_of_ne_zero
-/
theorem conductor_dvd_of_mem_conductorSet {d : Nat} [NeZero n] (hd : d in χ.conductorSet) :
    χ.conductor ∣ d := by
  have : NeZero d := ⟨by
    contrapose hd
    exact hd ▸ zero_ne_mem_conductorSet χ⟩
  suffices d.gcd χ.conductor in χ.conductorSet by
    have : χ.conductor <= d.gcd χ.conductor := Nat.sInf_le this
    contrapose! this
    refine Nat.lt_of_le_of_ne ?_ (Nat.gcd_eq_right_iff_dvd.not.mpr this)
exact Nat.gcd_le_right _ Nat.pos_of_ne_zero conductor_ne_zero χ
  obtain ⟨hd, χ₀, hχ₀⟩ := hd
  suffices (changeLevel (d.dvd_mul_right χ.conductor)) χ₀ =
      (changeLevel (χ.conductor.dvd_mul_left d)) χ.primitiveCharacter by
    obtain ⟨_, χ₁, hχ₁⟩ := factorsThrough_gcd χ₀ χ.primitiveCharacter this
    refine ⟨Nat.dvd_trans (d.gcd_dvd_left χ.conductor) hd, χ₁, ?_⟩
    rw [changeLevel_trans _ (d.gcd_dvd_left χ.conductor)]; rw [← hχ₁]; rw [hχ₀]
  have : NeZero (d * χ.conductor * n) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne d) χ.conductor_ne_zero) (NeZero.ne n)⟩
apply changeLevel_injective Nat.dvd_mul_right (d * χ.conductor) n
  rw [← changeLevel_trans]; rw [← changeLevel_trans]; rw [changeLevel_trans _ hd (n.dvd_mul_left (d * χ.conductor))]; rw [← hχ₀]; rw [changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level]; rw [changeLevel_primitiveCharacter]

/--
theorem `mem_conductorSet_iff_conductor_dvd` / 定理 `mem_conductorSet_iff_conductor_dvd`

English:
theorem mem_conductorSet_iff_conductor_dvd
  given: {d : Nat} [NeZero n] (hd : d ∣ n)
  proof: ⟨conductor_dvd_of_mem_conductorSet χ, fun h => χ.factorsThrough_conductor.mono χ h hd⟩

中文:
定理 mem_conductorSet_iff_conductor_dvd
  条件: {d : 自然数} [NeZero n] (hd : d ∣ n)
  证明: ⟨conductor_dvd_of_mem_conductorSet χ, fun h => χ.factorsThrough_conductor.mono χ h hd⟩

Depends on / 依赖: conductor_dvd_of_mem_conductorSet, factorsThrough_conductor, factorsThrough_conductor.mono
-/
theorem mem_conductorSet_iff_conductor_dvd {d : Nat} [NeZero n] (hd : d ∣ n) :
    d in χ.conductorSet ↔ χ.conductor ∣ d :=
  ⟨conductor_dvd_of_mem_conductorSet χ, fun h => χ.factorsThrough_conductor.mono χ h hd⟩

/--
theorem `conductor_changeLevel` / 定理 `conductor_changeLevel`

English:
theorem conductor_changeLevel
  given: {m : Nat} [NeZero m] (hm : n ∣ m)
  proof: by
  have : NeZero n := ⟨by aesop⟩
  have h : (changeLevel hm χ).conductor ∣ χ.conductor := by
    refine conductor_dvd_of_mem_conductorSet _
      ⟨χ.conductor_dvd_level.trans hm, χ.primitiveCharacter, ?_⟩
    rw [changeLevel_trans _ χ.conductor_dvd_level]; rw [changeLevel_primitiveCharacter]
refin

中文:
定理 conductor_changeLevel
  条件: {m : 自然数} [NeZero m] (hm : n ∣ m)
  证明: by
  have : NeZero n := ⟨by aesop⟩
  have h : (changeLevel hm χ).conductor ∣ χ.conductor := by
    refine conductor_dvd_of_mem_conductorSet _
      ⟨χ.conductor_dvd_level.trans hm, χ.primitiveCharacter, ?_⟩
    rw [changeLevel_trans _ χ.conductor_dvd_level]; rw [changeLevel_primitiveCharacter]
refin

Depends on / 依赖: NeZero, antisymm, changeLevel, changeLevel_injective, changeLevel_primitiveCharacter, changeLevel_trans, conductor, conductor_dvd_level, conductor_dvd_level.trans, conductor_dvd_of_mem_conductorSet, h.antisymm, h.trans, primitiveCharacter
-/
theorem conductor_changeLevel {m : Nat} [NeZero m] (hm : n ∣ m) :
    (changeLevel hm χ).conductor = χ.conductor := by
  have : NeZero n := ⟨by aesop⟩
  have h : (changeLevel hm χ).conductor ∣ χ.conductor := by
    refine conductor_dvd_of_mem_conductorSet _
      ⟨χ.conductor_dvd_level.trans hm, χ.primitiveCharacter, ?_⟩
    rw [changeLevel_trans _ χ.conductor_dvd_level]; rw [changeLevel_primitiveCharacter]
refine h.antisymm conductor_dvd_of_mem_conductorSet _
    ⟨h.trans χ.conductor_dvd_level, (changeLevel hm χ).primitiveCharacter, ?_⟩
  apply changeLevel_injective hm
  rw [← changeLevel_trans]; rw [changeLevel_primitiveCharacter]

/--
theorem `primitiveCharacter_changeLevel_apply` / 定理 `primitiveCharacter_changeLevel_apply`

English:
theorem primitiveCharacter_changeLevel_apply
  statement: [Nontrivial R] {m : Nat} [NeZero m] (hm : n ∣ m)
  proof: by
  by_cases ha : IsCoprime a χ.conductor
  · suffices changeLevel (dvd_of_eq <| conductor_changeLevel ..)
        (changeLevel hm χ).primitiveCharacter = χ.primitiveCharacter by
      have := DFunLike.congr_fun this (a : ZMod _)
      rwa [changeLevel_eq_cast_of_dvd' _ _ ha] at this
    apply chan

中文:
定理 primitiveCharacter_changeLevel_apply
  结论: [非平凡 R] {m : 自然数} [NeZero m] (hm : n ∣ m)
  证明: by
  by_cases ha : IsCoprime a χ.conductor
  · suffices changeLevel (dvd_of_eq <| conductor_changeLevel ..)
        (changeLevel hm χ).primitiveCharacter = χ.primitiveCharacter by
      have := DFunLike.congr_fun this (a : ZMod _)
      rwa [changeLevel_eq_cast_of_dvd' _ _ ha] at this
    apply chan

Depends on / 依赖: DFunLike, DFunLike.congr_fun, IsCoprime, changeLevel, changeLevel_eq_cast_of_dvd, changeLevel_injective, changeLevel_primitiveCharacter, changeLevel_trans, conductor, conductor_changeLevel, conductor_dvd_level, conductor_dvd_level.trans, congr_fun, dvd_of_eq, primitiveCharacter, primitiveCharacter.changeLevel_trans
-/
theorem primitiveCharacter_changeLevel_apply [Nontrivial R] {m : Nat} [NeZero m] (hm : n ∣ m)
    (χ : DirichletCharacter R n) (a : Int) :
    (changeLevel hm χ).primitiveCharacter a = χ.primitiveCharacter a := by
  by_cases ha : IsCoprime a χ.conductor
  · suffices changeLevel (dvd_of_eq <| conductor_changeLevel ..)
        (changeLevel hm χ).primitiveCharacter = χ.primitiveCharacter by
      have := DFunLike.congr_fun this (a : ZMod _)
      rwa [changeLevel_eq_cast_of_dvd' _ _ ha] at this
    apply changeLevel_injective (χ.conductor_dvd_level.trans hm)
    rw [← changeLevel_trans]; rw [changeLevel_primitiveCharacter]; rw [χ.primitiveCharacter.changeLevel_trans χ.conductor_dvd_level]; rw [changeLevel_primitiveCharacter]
  · rw [(apply_eq_zero_iff ..).mpr ha, (apply_eq_zero_iff ..).mpr (by rwa [conductor_changeLevel])]

/--
lemma `conductor_zpow_dvd` / 引理 `conductor_zpow_dvd`

English:
lemma conductor_zpow_dvd
  given: (χ : DirichletCharacter R n) (m : Int)
  proof: by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr]
  rw [← mem_conductorSet_iff_conductor_dvd _ χ.conductor_dvd_level]; rw [mem_conductorSet_iff]
  refine ⟨χ.conductor_dvd_level, χ.primitiveCharacter ^ m, ?_⟩
  rw [MonoidHom.map_zpow]; rw [changeLevel_prim

中文:
引理 conductor_zpow_dvd
  条件: (χ : DirichletCharacter R n) (m : 整数)
  证明: by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr]
  rw [← mem_conductorSet_iff_conductor_dvd _ χ.conductor_dvd_level]; rw [mem_conductorSet_iff]
  refine ⟨χ.conductor_dvd_level, χ.primitiveCharacter ^ m, ?_⟩
  rw [MonoidHom.map_zpow]; rw [changeLevel_prim

Depends on / 依赖: MonoidHom, MonoidHom.map_zpow, changeLevel_primitiveCharacter, conductor_dvd_level, conductor_eq_zero_iff_level_eq_zero, conductor_eq_zero_iff_level_eq_zero.mpr, eq_zero_or_neZero, map_zpow, mem_conductorSet_iff, mem_conductorSet_iff_conductor_dvd, primitiveCharacter
-/
lemma conductor_zpow_dvd (χ : DirichletCharacter R n) (m : Int) :
    conductor (χ ^ m) ∣ conductor χ := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr]
  rw [← mem_conductorSet_iff_conductor_dvd _ χ.conductor_dvd_level]; rw [mem_conductorSet_iff]
  refine ⟨χ.conductor_dvd_level, χ.primitiveCharacter ^ m, ?_⟩
  rw [MonoidHom.map_zpow]; rw [changeLevel_primitiveCharacter]

/--
lemma `conductor_pow_dvd` / 引理 `conductor_pow_dvd`

English:
lemma conductor_pow_dvd
  given: (χ : DirichletCharacter R n) (m : Nat)
  proof: zpow_natCast χ m ▸ conductor_zpow_dvd ..

中文:
引理 conductor_pow_dvd
  条件: (χ : DirichletCharacter R n) (m : 自然数)
  证明: zpow_natCast χ m ▸ conductor_zpow_dvd ..

Depends on / 依赖: conductor_zpow_dvd, zpow_natCast
-/
lemma conductor_pow_dvd (χ : DirichletCharacter R n) (m : Nat) :
    conductor (χ ^ m) ∣ conductor χ :=
  zpow_natCast χ m ▸ conductor_zpow_dvd ..

/--
theorem `conductor_inv` / 定理 `conductor_inv`

English:
theorem conductor_inv
  given: (χ : DirichletCharacter R n)
  proof: by
  rw [← zpow_neg_one]
  refine dvd_antisymm (conductor_zpow_dvd ..) ?_
  nth_rewrite 1 [← inv_inv χ, ← zpow_neg_one, ← zpow_neg_one]
  exact conductor_zpow_dvd ..

中文:
定理 conductor_inv
  条件: (χ : DirichletCharacter R n)
  证明: by
  rw [← zpow_neg_one]
  refine dvd_antisymm (conductor_zpow_dvd ..) ?_
  nth_rewrite 1 [← inv_inv χ, ← zpow_neg_one, ← zpow_neg_one]
  exact conductor_zpow_dvd ..

Depends on / 依赖: conductor_zpow_dvd, dvd_antisymm, inv_inv, nth_rewrite, zpow_neg_one
-/
theorem conductor_inv (χ : DirichletCharacter R n) :
    χ⁻¹.conductor = χ.conductor := by
  rw [← zpow_neg_one]
  refine dvd_antisymm (conductor_zpow_dvd ..) ?_
  nth_rewrite 1 [← inv_inv χ, ← zpow_neg_one, ← zpow_neg_one]
  exact conductor_zpow_dvd ..

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: {m : Nat} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m)
  body: changeLevel (Nat.dvd_lcm_left n m) χ₁ * changeLevel (Nat.dvd_lcm_right n m) χ₂

中文:
定义 mul
  签名: {m : 自然数} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m)
  定义体: changeLevel (Nat.dvd_lcm_left n m) χ₁ * changeLevel (Nat.dvd_lcm_right n m) χ₂

Depends on / 依赖: Nat.dvd_lcm_left, Nat.dvd_lcm_right, changeLevel, dvd_lcm_left, dvd_lcm_right
-/
noncomputable def mul {m : Nat} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m) :
    DirichletCharacter R (Nat.lcm n m) :=
  changeLevel (Nat.dvd_lcm_left n m) χ₁ * changeLevel (Nat.dvd_lcm_right n m) χ₂

/--
Definition of `primitive_mul` / `primitive_mul` 的定义

English:
definition primitive_mul
  signature: {m : Nat} (χ₁ : DirichletCharacter R n)
  body: primitiveCharacter (mul χ₁ χ₂)

中文:
定义 primitive_mul
  签名: {m : 自然数} (χ₁ : DirichletCharacter R n)
  定义体: primitiveCharacter (mul χ₁ χ₂)

Depends on / 依赖: primitiveCharacter
-/
noncomputable def primitive_mul {m : Nat} (χ₁ : DirichletCharacter R n)
    (χ₂ : DirichletCharacter R m) : DirichletCharacter R (mul χ₁ χ₂).conductor :=
  primitiveCharacter (mul χ₁ χ₂)

/--
lemma `mul_def` / 引理 `mul_def`

English:
lemma mul_def
  given: {n m : Nat} {χ : DirichletCharacter R n} {ψ : DirichletCharacter R m}
  proof: rfl

中文:
引理 mul_def
  条件: {n m : 自然数} {χ : DirichletCharacter R n} {ψ : DirichletCharacter R m}
  证明: rfl
-/
lemma mul_def {n m : Nat} {χ : DirichletCharacter R n} {ψ : DirichletCharacter R m} :
    χ.primitive_mul ψ = primitiveCharacter (mul χ ψ) :=
  rfl

/--
lemma `primitive_mul_isPrimitive` / 引理 `primitive_mul_isPrimitive`

English:
lemma primitive_mul_isPrimitive
  given: {m : Nat} (ψ : DirichletCharacter R m)
  proof: primitiveCharacter_isPrimitive _

中文:
引理 primitive_mul_isPrimitive
  条件: {m : 自然数} (ψ : DirichletCharacter R m)
  证明: primitiveCharacter_isPrimitive _

Depends on / 依赖: primitiveCharacter_isPrimitive
-/
lemma primitive_mul_isPrimitive {m : Nat} (ψ : DirichletCharacter R m) :
    IsPrimitive (primitive_mul χ ψ) :=
  primitiveCharacter_isPrimitive _

/--
theorem `conductor_mul_dvd_lcm_conductor` / 定理 `conductor_mul_dvd_lcm_conductor`

English:
theorem conductor_mul_dvd_lcm_conductor
  given: (χ ψ : DirichletCharacter R n)
  proof: by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr]
  have h := Nat.lcm_dvd χ.conductor_dvd_level ψ.conductor_dvd_level
  rw [← mem_conductorSet_iff_conductor_dvd _ h]; rw [mem_conductorSet_iff]
  refine ⟨h, χ.primitiveCharacter.mul ψ.primitiveCharacter, ?_

中文:
定理 conductor_mul_dvd_lcm_conductor
  条件: (χ ψ : DirichletCharacter R n)
  证明: by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr]
  have h := Nat.lcm_dvd χ.conductor_dvd_level ψ.conductor_dvd_level
  rw [← mem_conductorSet_iff_conductor_dvd _ h]; rw [mem_conductorSet_iff]
  refine ⟨h, χ.primitiveCharacter.mul ψ.primitiveCharacter, ?_

Depends on / 依赖: MonoidHom, MonoidHom.map_mul, Nat.lcm_dvd, changeLevel_primitiveCharacter, changeLevel_trans, conductor_dvd_level, conductor_eq_zero_iff_level_eq_zero, conductor_eq_zero_iff_level_eq_zero.mpr, eq_zero_or_neZero, lcm_dvd, map_mul, mem_conductorSet_iff, mem_conductorSet_iff_conductor_dvd, primitiveCharacter, primitiveCharacter.mul
-/
theorem conductor_mul_dvd_lcm_conductor (χ ψ : DirichletCharacter R n) :
    (χ * ψ).conductor ∣ χ.conductor.lcm ψ.conductor := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr]
  have h := Nat.lcm_dvd χ.conductor_dvd_level ψ.conductor_dvd_level
  rw [← mem_conductorSet_iff_conductor_dvd _ h]; rw [mem_conductorSet_iff]
  refine ⟨h, χ.primitiveCharacter.mul ψ.primitiveCharacter, ?_⟩
  rw [mul]; rw [MonoidHom.map_mul]; rw [← changeLevel_trans]; rw [← changeLevel_trans]; rw [changeLevel_primitiveCharacter]; rw [changeLevel_primitiveCharacter]

/-!
### Specific subgroups
-/

/--
Definition of `subgroupOfCoprimeConductor` / `subgroupOfCoprimeConductor` 的定义

English:
definition subgroupOfCoprimeConductor
  signature: [NeZero n] (d : Nat)
  body: {χ | d.Coprime χ.conductor}
  mul_mem' hχ hψ := by
    apply Nat.Coprime.of_dvd_right (conductor_mul_dvd_lcm_conductor _ _)
exact (Nat.Coprime.mul_right hχ hψ).coprime_div_right Nat.gcd_dvd_mul _ _
  one_mem' := by simp [conductor_one]
  inv_mem' hχ := by rwa [Set.mem_ofPred, conductor_inv]

@[simp]

中文:
定义 subgroupOfCoprimeConductor
  签名: [NeZero n] (d : 自然数)
  定义体: {χ | d.Coprime χ.conductor}
  mul_mem' hχ hψ := by
    apply Nat.Coprime.of_dvd_right (conductor_mul_dvd_lcm_conductor _ _)
exact (Nat.Coprime.mul_right hχ hψ).coprime_div_right Nat.gcd_dvd_mul _ _
  one_mem' := by simp [conductor_one]
  inv_mem' hχ := by rwa [Set.mem_ofPred, conductor_inv]

@[simp]

Depends on / 依赖: Coprime, conductor, d.Coprime
-/
def subgroupOfCoprimeConductor [NeZero n] (d : Nat) :
    Subgroup (DirichletCharacter R n) where
  carrier := {χ | d.Coprime χ.conductor}
  mul_mem' hχ hψ := by
    apply Nat.Coprime.of_dvd_right (conductor_mul_dvd_lcm_conductor _ _)
exact (Nat.Coprime.mul_right hχ hψ).coprime_div_right Nat.gcd_dvd_mul _ _
  one_mem' := by simp [conductor_one]
  inv_mem' hχ := by rwa [Set.mem_ofPred, conductor_inv]

@[simp]
/--
lemma `mem_subgroupOfCoprimeConductor` / 引理 `mem_subgroupOfCoprimeConductor`

English:
lemma mem_subgroupOfCoprimeConductor
  given: [NeZero n] {d : Nat} {χ : DirichletCharacter R n}
  proof: Iff.rfl

中文:
引理 mem_subgroupOfCoprimeConductor
  条件: [NeZero n] {d : 自然数} {χ : DirichletCharacter R n}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_subgroupOfCoprimeConductor [NeZero n] {d : Nat} {χ : DirichletCharacter R n} :
    χ in subgroupOfCoprimeConductor d ↔ d.Coprime χ.conductor := Iff.rfl

variable (R) in
/--
Definition of `annihilator` / `annihilator` 的定义

English:
definition annihilator
  signature: (H : Set (ZMod n)ˣ)
  body: (MulChar.domRestrictHom ((Submonoid.closure H).map (Units.coeHom (ZMod n))) _).ker

中文:
定义 annihilator
  签名: (H : 集合 (ZMod n)ˣ)
  定义体: (MulChar.domRestrictHom ((Submonoid.closure H).map (Units.coeHom (ZMod n))) _).ker

Depends on / 依赖: MulChar, MulChar.domRestrictHom, Submonoid, Submonoid.closure, Units.coeHom, closure, coeHom, domRestrictHom
-/
noncomputable def annihilator (H : Set (ZMod n)ˣ) :
    Subgroup (DirichletCharacter R n) :=
  (MulChar.domRestrictHom ((Submonoid.closure H).map (Units.coeHom (ZMod n))) _).ker

/--
theorem `mem_annihilator_iff_mem_closure` / 定理 `mem_annihilator_iff_mem_closure`

English:
theorem mem_annihilator_iff_mem_closure
  given: {H : Set (ZMod n)ˣ} {χ : DirichletCharacter R n}
  proof: by
  simp only [annihilator, MonoidHom.mem_ker, MulChar.domRestrictHom_apply,
    MulChar.domRestrict_eq_one_iff]
  refine ⟨fun hχ x hx => ?_, fun h u => ?_⟩
· exact hχ (Submonoid.unitsEquivUnitsType _)
      ⟨x, Submonoid.mem_units_of_val_mem_inv_val_mem _ ⟨x, hx, rfl⟩
        ⟨x⁻¹, by simpa [← Sub

中文:
定理 mem_annihilator_iff_mem_closure
  条件: {H : 集合 (ZMod n)ˣ} {χ : DirichletCharacter R n}
  证明: by
  simp only [annihilator, MonoidHom.mem_ker, MulChar.domRestrictHom_apply,
    MulChar.domRestrict_eq_one_iff]
  refine ⟨fun hχ x hx => ?_, fun h u => ?_⟩
· exact hχ (Submonoid.unitsEquivUnitsType _)
      ⟨x, Submonoid.mem_units_of_val_mem_inv_val_mem _ ⟨x, hx, rfl⟩
        ⟨x⁻¹, by simpa [← Sub

Depends on / 依赖: MonoidHom, MonoidHom.mem_ker, MulChar, MulChar.domRestrictHom_apply, MulChar.domRestrict_eq_one_iff, Subgroup, Subgroup.closure_toSubmonoid_of_finite, Submonoid, Submonoid.mem_map.mp, Submonoid.mem_units_of_val_mem_inv_val_mem, Submonoid.unitsEquivUnitsType, annihilator, closure_toSubmonoid_of_finite, domRestrictHom_apply, domRestrict_eq_one_iff, mem_ker, mem_map, mem_units_of_val_mem_inv_val_mem, u.val.prop, unitsEquivUnitsType
-/
theorem mem_annihilator_iff_mem_closure {H : Set (ZMod n)ˣ} {χ : DirichletCharacter R n} :
    χ in annihilator R H ↔ forall x in Submonoid.closure H, χ x = 1 := by
  simp only [annihilator, MonoidHom.mem_ker, MulChar.domRestrictHom_apply,
    MulChar.domRestrict_eq_one_iff]
  refine ⟨fun hχ x hx => ?_, fun h u => ?_⟩
· exact hχ (Submonoid.unitsEquivUnitsType _)
      ⟨x, Submonoid.mem_units_of_val_mem_inv_val_mem _ ⟨x, hx, rfl⟩
        ⟨x⁻¹, by simpa [← Subgroup.closure_toSubmonoid_of_finite] using hx, rfl⟩⟩
  · obtain ⟨y, hy, hyu⟩ := Submonoid.mem_map.mp u.val.prop
    exact hyu ▸ h _ hy

@[simp]
/--
theorem `mem_annihilator_iff` / 定理 `mem_annihilator_iff`

English:
theorem mem_annihilator_iff
  given: {H : Set (ZMod n)ˣ} {χ : DirichletCharacter R n}
  proof: by
  rw [mem_annihilator_iff_mem_closure]
  refine ⟨fun h a ha => h a (Submonoid.subset_closure ha), fun h x hx => ?_⟩
  refine Submonoid.closure_induction h (by simp) (fun a b _ _ ha hb => ?_) hx
  simp [map_mul, ha, hb]

中文:
定理 mem_annihilator_iff
  条件: {H : 集合 (ZMod n)ˣ} {χ : DirichletCharacter R n}
  证明: by
  rw [mem_annihilator_iff_mem_closure]
  refine ⟨fun h a ha => h a (Submonoid.subset_closure ha), fun h x hx => ?_⟩
  refine Submonoid.closure_induction h (by simp) (fun a b _ _ ha hb => ?_) hx
  simp [map_mul, ha, hb]

Depends on / 依赖: Submonoid, Submonoid.closure_induction, Submonoid.subset_closure, closure_induction, map_mul, mem_annihilator_iff_mem_closure, subset_closure
-/
theorem mem_annihilator_iff {H : Set (ZMod n)ˣ} {χ : DirichletCharacter R n} :
    χ in annihilator R H ↔ forall a in H, χ a = 1 := by
  rw [mem_annihilator_iff_mem_closure]
  refine ⟨fun h a ha => h a (Submonoid.subset_closure ha), fun h x hx => ?_⟩
  refine Submonoid.closure_induction h (by simp) (fun a b _ _ ha hb => ?_) hx
  simp [map_mul, ha, hb]

variable (R n) in
/--
Definition of `subgroupOfPrimitiveMapToOne` / `subgroupOfPrimitiveMapToOne` 的定义

English:
definition subgroupOfPrimitiveMapToOne
  signature: [NeZero n] (p : Nat) [hp : Fact p.Prime]
  body: (annihilator R (n := n / p ^ n.factorization p)
    {ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp.out (NeZero.ne n))}).map
      (changeLevel (Nat.ordCompl_dvd n p))

@[simp]

中文:
定义 subgroupOfPrimitiveMapToOne
  签名: [NeZero n] (p : 自然数) [hp : Fact p.素]
  定义体: (annihilator R (n := n / p ^ n.factorization p)
    {ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp.out (NeZero.ne n))}).map
      (changeLevel (Nat.ordCompl_dvd n p))

@[simp]

Depends on / 依赖: Nat.coprime_ordCompl, Nat.ordCompl_dvd, NeZero, NeZero.ne, ZMod.unitOfCoprime, annihilator, changeLevel, coprime_ordCompl, factorization, hp.out, n.factorization, ordCompl_dvd, unitOfCoprime
-/
noncomputable def subgroupOfPrimitiveMapToOne [NeZero n] (p : Nat) [hp : Fact p.Prime] :
    Subgroup (DirichletCharacter R n) :=
  (annihilator R (n := n / p ^ n.factorization p)
    {ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp.out (NeZero.ne n))}).map
      (changeLevel (Nat.ordCompl_dvd n p))

@[simp]
/--
theorem `mem_subgroupOfPrimitiveMapToOne_iff` / 定理 `mem_subgroupOfPrimitiveMapToOne_iff`

English:
theorem mem_subgroupOfPrimitiveMapToOne_iff
  given: [NeZero n] [Nontrivial R] (p : Nat) [hp : Fact p.Prime]
  proof: by
  have : NeZero (n / p ^ n.factorization p) := ⟨(Nat.ordCompl_pos p (NeZero.ne n)).ne'⟩
  have hcop := Nat.coprime_ordCompl hp.out (NeZero.ne n)
  simp only [subgroupOfPrimitiveMapToOne, Subgroup.mem_map, mem_annihilator_iff,
    Set.mem_singleton_iff, forall_eq, ZMod.coe_unitOfCoprime]
  refine 

中文:
定理 mem_subgroupOfPrimitiveMapToOne_iff
  条件: [NeZero n] [非平凡 R] (p : 自然数) [hp : Fact p.素]
  证明: by
  have : NeZero (n / p ^ n.factorization p) := ⟨(Nat.ordCompl_pos p (NeZero.ne n)).ne'⟩
  have hcop := Nat.coprime_ordCompl hp.out (NeZero.ne n)
  simp only [subgroupOfPrimitiveMapToOne, Subgroup.mem_map, mem_annihilator_iff,
    Set.mem_singleton_iff, forall_eq, ZMod.coe_unitOfCoprime]
  refine 

Depends on / 依赖: Int.cast_natCast, Nat.coprime_ordCompl, Nat.isCoprime_iff_coprime.mpr, Nat.ordCompl_pos, NeZero, NeZero.ne, Set.mem_singleton_iff, Subgroup, Subgroup.mem_map, ZMod.coe_unitOfCoprime, cast_natCast, coe_unitOfCoprime, coprime_ordCompl, factorization, forall_eq, hp.out, isCoprime_iff_coprime, mem_annihilator_iff, mem_map, mem_singleton_iff
-/
theorem mem_subgroupOfPrimitiveMapToOne_iff [NeZero n] [Nontrivial R] (p : Nat) [hp : Fact p.Prime] :
    χ in subgroupOfPrimitiveMapToOne R n p ↔ χ.primitiveCharacter p = 1 := by
  have : NeZero (n / p ^ n.factorization p) := ⟨(Nat.ordCompl_pos p (NeZero.ne n)).ne'⟩
  have hcop := Nat.coprime_ordCompl hp.out (NeZero.ne n)
  simp only [subgroupOfPrimitiveMapToOne, Subgroup.mem_map, mem_annihilator_iff,
    Set.mem_singleton_iff, forall_eq, ZMod.coe_unitOfCoprime]
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨ψ, hψ, rfl⟩
    rw [← Int.cast_natCast] at hψ ⊢
    rw [primitiveCharacter_changeLevel_apply]; rw [primitiveCharacter_apply_of_isCoprime]; rw [hψ]
    exact Nat.isCoprime_iff_coprime.mpr hcop
  · have hdvd : χ.conductor ∣ n / p ^ n.factorization p := by
      apply Nat.dvd_ordCompl_of_dvd_not_dvd χ.conductor_dvd_level
      simp [← hp.out.coprime_iff_not_dvd, ← Nat.isCoprime_iff_coprime,
        ← apply_ne_zero_iff (χ := χ.primitiveCharacter), h]
    refine ⟨changeLevel hdvd χ.primitiveCharacter, ?_, ?_⟩
    · rw [show (p : ZMod (n / p ^ n.factorization p))
          = ((p : Int) : ZMod (n / p ^ n.factorization p)) from (Int.cast_natCast p).symm,
        changeLevel_eq_cast_of_dvd' χ.primitiveCharacter hdvd (Nat.isCoprime_iff_coprime.mpr hcop),
        Int.cast_natCast]
      exact h
    · rw [← changeLevel_trans, changeLevel_primitiveCharacter]

/-
### Even and odd characters
-/

section CommRing

variable {S : Type*} [CommRing S] {m : Nat} (ψ : DirichletCharacter S m)

/--
Definition of `Odd` / `Odd` 的定义

English:
definition Odd
  signature: : Prop
  body: ψ (-1) = -1

中文:
定义 Odd
  签名: : 命题
  定义体: ψ (-1) = -1
-/
def Odd : Prop := ψ (-1) = -1

/--
Definition of `Even` / `Even` 的定义

English:
definition Even
  signature: : Prop
  body: ψ (-1) = 1

中文:
定义 Even
  签名: : 命题
  定义体: ψ (-1) = 1
-/
def Even : Prop := ψ (-1) = 1

/--
lemma `even_or_odd` / 引理 `even_or_odd`

English:
lemma even_or_odd
  given: [NoZeroDivisors S]
  statement: ψ.Even ∨ ψ.Odd
  proof: by
  suffices ψ (-1) ^ 2 = 1 by convert! sq_eq_one_iff.mp this
  rw [← map_pow _]; rw [neg_one_sq]; rw [map_one]

中文:
引理 even_or_odd
  条件: [无零因子 S]
  结论: ψ.Even ∨ ψ.Odd
  证明: by
  suffices ψ (-1) ^ 2 = 1 by convert! sq_eq_one_iff.mp this
  rw [← map_pow _]; rw [neg_one_sq]; rw [map_one]

Depends on / 依赖: convert, map_one, map_pow, neg_one_sq, sq_eq_one_iff, sq_eq_one_iff.mp
-/
lemma even_or_odd [NoZeroDivisors S] : ψ.Even ∨ ψ.Odd := by
  suffices ψ (-1) ^ 2 = 1 by convert! sq_eq_one_iff.mp this
  rw [← map_pow _]; rw [neg_one_sq]; rw [map_one]

/--
lemma `not_even_and_odd` / 引理 `not_even_and_odd`

English:
lemma not_even_and_odd
  given: [NeZero (2 : S)]
  statement: ¬(ψ.Even ∧ ψ.Odd)
  proof: by
  rintro ⟨(h : _ = 1), (h' : _ = -1)⟩
  simp only [h', neg_eq_iff_add_eq_zero, one_add_one_eq_two, two_ne_zero] at h

中文:
引理 not_even_and_odd
  条件: [NeZero (2 : S)]
  结论: ¬(ψ.Even ∧ ψ.Odd)
  证明: by
  rintro ⟨(h : _ = 1), (h' : _ = -1)⟩
  simp only [h', neg_eq_iff_add_eq_zero, one_add_one_eq_two, two_ne_zero] at h

Depends on / 依赖: neg_eq_iff_add_eq_zero, one_add_one_eq_two, two_ne_zero
-/
lemma not_even_and_odd [NeZero (2 : S)] : ¬(ψ.Even ∧ ψ.Odd) := by
  rintro ⟨(h : _ = 1), (h' : _ = -1)⟩
  simp only [h', neg_eq_iff_add_eq_zero, one_add_one_eq_two, two_ne_zero] at h

/--
lemma `Even.not_odd` / 引理 `Even.not_odd`

English:
lemma Even.not_odd
  given: [NeZero (2 : S)] (hψ : Even ψ)
  statement: ¬Odd ψ
  proof: not_and.mp ψ.not_even_and_odd hψ

中文:
引理 Even.not_odd
  条件: [NeZero (2 : S)] (hψ : Even ψ)
  结论: ¬Odd ψ
  证明: not_and.mp ψ.not_even_and_odd hψ

Depends on / 依赖: not_and, not_and.mp, not_even_and_odd
-/
lemma Even.not_odd [NeZero (2 : S)] (hψ : Even ψ) : ¬Odd ψ :=
  not_and.mp ψ.not_even_and_odd hψ

/--
lemma `Odd.not_even` / 引理 `Odd.not_even`

English:
lemma Odd.not_even
  given: [NeZero (2 : S)] (hψ : Odd ψ)
  statement: ¬Even ψ
  proof: not_and'.mp ψ.not_even_and_odd hψ

中文:
引理 Odd.not_even
  条件: [NeZero (2 : S)] (hψ : Odd ψ)
  结论: ¬Even ψ
  证明: not_and'.mp ψ.not_even_and_odd hψ

Depends on / 依赖: not_and, not_even_and_odd
-/
lemma Odd.not_even [NeZero (2 : S)] (hψ : Odd ψ) : ¬Even ψ :=
  not_and'.mp ψ.not_even_and_odd hψ

/--
lemma `Odd.toUnitHom_eval_neg_one` / 引理 `Odd.toUnitHom_eval_neg_one`

English:
lemma Odd.toUnitHom_eval_neg_one
  given: (hψ : ψ.Odd)
  statement: ψ.toUnitHom (-1) = -1
  proof: by
  rw [← Units.val_inj]; rw [MulChar.coe_toUnitHom]
  exact hψ

中文:
引理 Odd.toUnitHom_eval_neg_one
  条件: (hψ : ψ.Odd)
  结论: ψ.toUnitHom (-1) = -1
  证明: by
  rw [← Units.val_inj]; rw [MulChar.coe_toUnitHom]
  exact hψ

Depends on / 依赖: MulChar, MulChar.coe_toUnitHom, Units.val_inj, coe_toUnitHom, val_inj
-/
lemma Odd.toUnitHom_eval_neg_one (hψ : ψ.Odd) : ψ.toUnitHom (-1) = -1 := by
  rw [← Units.val_inj]; rw [MulChar.coe_toUnitHom]
  exact hψ

/--
lemma `Even.toUnitHom_eval_neg_one` / 引理 `Even.toUnitHom_eval_neg_one`

English:
lemma Even.toUnitHom_eval_neg_one
  given: (hψ : ψ.Even)
  statement: ψ.toUnitHom (-1) = 1
  proof: by
  rw [← Units.val_inj]; rw [MulChar.coe_toUnitHom]
  exact hψ

中文:
引理 Even.toUnitHom_eval_neg_one
  条件: (hψ : ψ.Even)
  结论: ψ.toUnitHom (-1) = 1
  证明: by
  rw [← Units.val_inj]; rw [MulChar.coe_toUnitHom]
  exact hψ

Depends on / 依赖: MulChar, MulChar.coe_toUnitHom, Units.val_inj, coe_toUnitHom, val_inj
-/
lemma Even.toUnitHom_eval_neg_one (hψ : ψ.Even) : ψ.toUnitHom (-1) = 1 := by
  rw [← Units.val_inj]; rw [MulChar.coe_toUnitHom]
  exact hψ

/--
lemma `Odd.eval_neg` / 引理 `Odd.eval_neg`

English:
lemma Odd.eval_neg
  given: (x : ZMod m) (hψ : ψ.Odd)
  statement: ψ (-x) = - ψ x
  proof: by
  rw [Odd] at hψ
  rw [← neg_one_mul]; rw [map_mul]
  simp [hψ]

中文:
引理 Odd.eval_neg
  条件: (x : ZMod m) (hψ : ψ.Odd)
  结论: ψ (-x) = - ψ x
  证明: by
  rw [Odd] at hψ
  rw [← neg_one_mul]; rw [map_mul]
  simp [hψ]

Depends on / 依赖: map_mul, neg_one_mul
-/
lemma Odd.eval_neg (x : ZMod m) (hψ : ψ.Odd) : ψ (-x) = - ψ x := by
  rw [Odd] at hψ
  rw [← neg_one_mul]; rw [map_mul]
  simp [hψ]

/--
lemma `Even.eval_neg` / 引理 `Even.eval_neg`

English:
lemma Even.eval_neg
  given: (x : ZMod m) (hψ : ψ.Even)
  statement: ψ (-x) = ψ x
  proof: by
  rw [Even] at hψ
  rw [← neg_one_mul]; rw [map_mul]
  simp [hψ]

中文:
引理 Even.eval_neg
  条件: (x : ZMod m) (hψ : ψ.Even)
  结论: ψ (-x) = ψ x
  证明: by
  rw [Even] at hψ
  rw [← neg_one_mul]; rw [map_mul]
  simp [hψ]

Depends on / 依赖: map_mul, neg_one_mul
-/
lemma Even.eval_neg (x : ZMod m) (hψ : ψ.Even) : ψ (-x) = ψ x := by
  rw [Even] at hψ
  rw [← neg_one_mul]; rw [map_mul]
  simp [hψ]

/--
lemma `Even.to_fun` / 引理 `Even.to_fun`

English:
lemma Even.to_fun
  given: {χ : DirichletCharacter S m} (hχ : Even χ)
  statement: Function.Even χ
  proof: fun _ => by rw [← neg_one_mul, map_mul, hχ, one_mul]

中文:
引理 Even.to_fun
  条件: {χ : DirichletCharacter S m} (hχ : Even χ)
  结论: 函数.Even χ
  证明: fun _ => by rw [← neg_one_mul, map_mul, hχ, one_mul]

Depends on / 依赖: map_mul, neg_one_mul, one_mul
-/
lemma Even.to_fun {χ : DirichletCharacter S m} (hχ : Even χ) : Function.Even χ :=
  fun _ => by rw [← neg_one_mul, map_mul, hχ, one_mul]

/--
lemma `Odd.to_fun` / 引理 `Odd.to_fun`

English:
lemma Odd.to_fun
  given: {χ : DirichletCharacter S m} (hχ : Odd χ)
  statement: Function.Odd χ
  proof: fun _ => by rw [← neg_one_mul, map_mul, hχ, neg_one_mul]

中文:
引理 Odd.to_fun
  条件: {χ : DirichletCharacter S m} (hχ : Odd χ)
  结论: 函数.Odd χ
  证明: fun _ => by rw [← neg_one_mul, map_mul, hχ, neg_one_mul]

Depends on / 依赖: map_mul, neg_one_mul
-/
lemma Odd.to_fun {χ : DirichletCharacter S m} (hχ : Odd χ) : Function.Odd χ :=
  fun _ => by rw [← neg_one_mul, map_mul, hχ, neg_one_mul]

end CommRing

end DirichletCharacter
