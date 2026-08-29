/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.RingTheory.Bezout
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Valuation.Integers
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Valuation Rings

A valuation ring is a domain such that for every pair of elements `a b`, either `a` divides
`b` or vice-versa.

Any valuation ring induces a natural valuation on its fraction field, as we show in this file.
Namely, given the following instances:
`[CommRing A] [IsDomain A] [ValuationRing A] [Field K] [Algebra A K] [IsFractionRing A K]`,
there is a natural valuation `Valuation A K` on `K` with values in `value_group A K` where
the image of `A` under `algebraMap A K` agrees with `(Valuation A K).integer`.

We also provide the equivalence of the following notions for a domain `R` in `ValuationRing.TFAE`.
1. `R` is a valuation ring.
2. For each `x : FractionRing K`, either `x` or `x⁻¹` is in `R`.
3. "divides" is a total relation on the elements of `R`.
4. "contains" is a total relation on the ideals of `R`.
5. `R` is a local bezout domain.

We also show that, given a valuation `v` on a field `K`, the ring of valuation integers is a
valuation ring and `K` is the fraction field of this ring.

## Implementation details

The Mathlib definition of a valuation ring requires `IsDomain A` even though the condition
does not mention zero divisors. Thus, there is a technical `PreValuationRing A` that
is defined in further generality that can be used in places where the ring cannot be a domain.
The `ValuationRing` class is kept to be in sync with the literature.

-/

@[expose] public section

assert_not_exists IsDiscreteValuationRing

universe u v w

/--
Definition of `PreValuationRing` / `PreValuationRing` 的定义

English:
class PreValuationRing
  parameters: (A : Type u) [Mul A]
  axioms and operations (1):
    - cond' : forall a b : A, exists c : A, a * c = b ∨ b * c = a

中文:
类 PreValuationRing
  参数: (A : 类型u) [Mul A]
  公理与运算 (1 个):
    - cond' : 对任意 a b : A, 存在 c : A, a * c = b ∨ b * c = a
-/
class PreValuationRing (A : Type u) [Mul A] : Prop where
  cond' : forall a b : A, exists c : A, a * c = b ∨ b * c = a

/--
lemma `PreValuationRing.cond` / 引理 `PreValuationRing.cond`

English:
lemma PreValuationRing.cond
  given: {A : Type u} [Mul A] [PreValuationRing A] (a b : A)
  proof: @PreValuationRing.cond' A _ _ _ _

中文:
引理 PreValuationRing.cond
  条件: {A : 类型u} [Mul A] [PreValuationRing A] (a b : A)
  证明: @PreValuationRing.cond' A _ _ _ _

Depends on / 依赖: PreValuationRing, PreValuationRing.cond
-/
lemma PreValuationRing.cond {A : Type u} [Mul A] [PreValuationRing A] (a b : A) :
    exists c : A, a * c = b ∨ b * c = a := @PreValuationRing.cond' A _ _ _ _

/--
Definition of `ValuationRing` / `ValuationRing` 的定义

English:
class ValuationRing
  parameters: (A : Type u) [CommRing A] [IsDomain A]
  extends: PreValuationRing A
  (no additional axioms)

中文:
类 ValuationRing
  参数: (A : 类型u) [CommRing A] [IsDomain A]
  继承: PreValuationRing A
  (无附加公理)

Depends on / 依赖: PreValuationRing, PreValuationRing.cond
-/
class ValuationRing (A : Type u) [CommRing A] [IsDomain A] : Prop extends PreValuationRing A

/-- An abbreviation for `PreValuationRing.cond` which should save some writing. -/
alias ValuationRing.cond := PreValuationRing.cond

namespace ValuationRing

section

variable (A : Type u) [CommRing A]
variable (K : Type v) [Field K] [Algebra A K]

/--
Definition of `ValueGroup` / `ValueGroup` 的定义

English:
definition ValueGroup
  signature: : Type v
  body: Quotient (MulAction.orbitRel Aˣ K)

中文:
定义 ValueGroup
  签名: : 类型v
  定义体: Quotient (MulAction.orbitRel Aˣ K)

Depends on / 依赖: MulAction, MulAction.orbitRel, Quotient, orbitRel
-/
def ValueGroup : Type v := Quotient (MulAction.orbitRel Aˣ K)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ValueGroup A K)
  body: ⟨Quotient.mk'' 0⟩

中文:
实例 :
  签名: Inhabited (ValueGroup A K)
  定义体: ⟨Quotient.mk'' 0⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
instance : Inhabited (ValueGroup A K) := ⟨Quotient.mk'' 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (ValueGroup A K)
  body: LE.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => exists c : A, c • b = a)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩; ext
        constructor
        · rintro ⟨e, he⟩; use (c⁻¹ : Aˣ) * e * d
          apply_fun fun t => c⁻¹ • t at he
          simpa [mul_smul] using! he
        · rintr

中文:
实例 :
  签名: LE (ValueGroup A K)
  定义体: LE.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => exists c : A, c • b = a)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩; ext
        constructor
        · rintro ⟨e, he⟩; use (c⁻¹ : Aˣ) * e * d
          apply_fun fun t => c⁻¹ • t at he
          simpa [mul_smul] using! he
        · rintr

Depends on / 依赖: LE.mk, Quotient, Quotient.liftOn, Units.inv_mul, Units.smul_def, apply_fun, inv_mul, mul_smul, one_smul, simp_rw, smul_def
-/
instance : LE (ValueGroup A K) :=
  LE.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => exists c : A, c • b = a)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩; ext
        constructor
        · rintro ⟨e, he⟩; use (c⁻¹ : Aˣ) * e * d
          apply_fun fun t => c⁻¹ • t at he
          simpa [mul_smul] using! he
        · rintro ⟨e, he⟩; dsimp
          use c * e * (d⁻¹ : Aˣ)
          simp_rw [Units.smul_def, ← he, mul_smul]
          rw [← mul_smul _ _ b]; rw [Units.inv_mul]; rw [one_smul])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (ValueGroup A K)
  body: ⟨Quotient.mk'' 0⟩

中文:
实例 :
  签名: Zero (ValueGroup A K)
  定义体: ⟨Quotient.mk'' 0⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
instance : Zero (ValueGroup A K) := ⟨Quotient.mk'' 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (ValueGroup A K)
  body: ⟨Quotient.mk'' 1⟩

中文:
实例 :
  签名: One (ValueGroup A K)
  定义体: ⟨Quotient.mk'' 1⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
instance : One (ValueGroup A K) := ⟨Quotient.mk'' 1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (ValueGroup A K)
  body: Mul.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => Quotient.mk'' <| a * b)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩
        apply Quotient.sound'
        dsimp
        use c * d
        simp only [mul_smul, Algebra.smul_def, Units.smul_def]
        ring)

中文:
实例 :
  签名: Mul (ValueGroup A K)
  定义体: Mul.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => Quotient.mk'' <| a * b)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩
        apply Quotient.sound'
        dsimp
        use c * d
        simp only [mul_smul, Algebra.smul_def, Units.smul_def]
        ring)

Depends on / 依赖: Algebra, Algebra.smul_def, Mul.mk, Quotient, Quotient.liftOn, Quotient.mk, Quotient.sound, Units.smul_def, mul_smul, smul_def
-/
instance : Mul (ValueGroup A K) :=
  Mul.mk fun x y =>
    Quotient.liftOn₂' x y (fun a b => Quotient.mk'' <| a * b)
      (by
        rintro _ _ a b ⟨c, rfl⟩ ⟨d, rfl⟩
        apply Quotient.sound'
        dsimp
        use c * d
        simp only [mul_smul, Algebra.smul_def, Units.smul_def]
        ring)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (ValueGroup A K)
  body: Inv.mk fun x =>
    Quotient.liftOn' x (fun a => Quotient.mk'' a⁻¹)
      (by
        rintro _ a ⟨b, rfl⟩
        apply Quotient.sound'
        use b⁻¹
        dsimp
        rw [Units.smul_def]; rw [Units.smul_def]; rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [mul_inv]; rw [map_units_inv])

中文:
实例 :
  签名: Inv (ValueGroup A K)
  定义体: Inv.mk fun x =>
    Quotient.liftOn' x (fun a => Quotient.mk'' a⁻¹)
      (by
        rintro _ a ⟨b, rfl⟩
        apply Quotient.sound'
        use b⁻¹
        dsimp
        rw [Units.smul_def]; rw [Units.smul_def]; rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [mul_inv]; rw [map_units_inv])

Depends on / 依赖: Algebra, Algebra.smul_def, Inv.mk, Quotient, Quotient.liftOn, Quotient.mk, Quotient.sound, Units.smul_def, liftOn, map_units_inv, mul_inv, smul_def
-/
instance : Inv (ValueGroup A K) :=
  Inv.mk fun x =>
    Quotient.liftOn' x (fun a => Quotient.mk'' a⁻¹)
      (by
        rintro _ a ⟨b, rfl⟩
        apply Quotient.sound'
        use b⁻¹
        dsimp
        rw [Units.smul_def]; rw [Units.smul_def]; rw [Algebra.smul_def]; rw [Algebra.smul_def]; rw [mul_inv]; rw [map_units_inv])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial (ValueGroup A K)
  body: ⟨0, 1, fun c => by
    obtain ⟨d, hd⟩ := Quotient.exact' c
    apply_fun fun t => d⁻¹ • t at hd
    dsimp at hd
    simp only [inv_smul_smul, smul_zero, one_ne_zero] at hd⟩

中文:
实例 :
  签名: Nontrivial (ValueGroup A K)
  定义体: ⟨0, 1, fun c => by
    obtain ⟨d, hd⟩ := Quotient.exact' c
    apply_fun fun t => d⁻¹ • t at hd
    dsimp at hd
    simp only [inv_smul_smul, smul_zero, one_ne_zero] at hd⟩

Depends on / 依赖: Quotient, Quotient.exact, apply_fun, inv_smul_smul, one_ne_zero, smul_zero
-/
instance : Nontrivial (ValueGroup A K) where
  exists_pair_ne := ⟨0, 1, fun c => by
    obtain ⟨d, hd⟩ := Quotient.exact' c
    apply_fun fun t => d⁻¹ • t at hd
    dsimp at hd
    simp only [inv_smul_smul, smul_zero, one_ne_zero] at hd⟩

variable [IsDomain A] [ValuationRing A] [IsFractionRing A K]

/--
theorem `le_total` / 定理 `le_total`

English:
theorem le_total
  given: (a b : ValueGroup A K)
  statement: a <= b ∨ b <= a
  proof: by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  obtain ⟨xa, ya, hya, rfl⟩ := IsFractionRing.div_surjective A a
  obtain ⟨xb, yb, hyb, rfl⟩ := IsFractionRing.div_surjective A b
  have : (algebraMap A K) ya != 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
  have : (algebraMap A K) yb != 0 

中文:
定理 le_total
  条件: (a b : ValueGroup A K)
  结论: a <= b ∨ b <= a
  证明: by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  obtain ⟨xa, ya, hya, rfl⟩ := IsFractionRing.div_surjective A a
  obtain ⟨xb, yb, hyb, rfl⟩ := IsFractionRing.div_surjective A b
  have : (algebraMap A K) ya != 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
  have : (algebraMap A K) yb != 0 
-/
protected theorem le_total (a b : ValueGroup A K) : a <= b ∨ b <= a := by
  rcases a with ⟨a⟩; rcases b with ⟨b⟩
  obtain ⟨xa, ya, hya, rfl⟩ := IsFractionRing.div_surjective A a
  obtain ⟨xb, yb, hyb, rfl⟩ := IsFractionRing.div_surjective A b
  have : (algebraMap A K) ya != 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
  have : (algebraMap A K) yb != 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
  obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
  · right
    use c
    rw [Algebra.smul_def]
    field_simp
    simp only [← map_mul]; congr 1; linear_combination h
  · left
    use c
    rw [Algebra.smul_def]
    field_simp
    simp only [← map_mul]; congr 1; linear_combination h

set_option backward.isDefEq.respectTransparency false in
/--
Instance `linearOrder` / 实例 `linearOrder`

English:
instance linearOrder
  signature: : LinearOrder (ValueGroup A K) where
  body: by rintro ⟨⟩; use 1; rw [one_smul]
  le_trans := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨e, rfl⟩ ⟨f, rfl⟩; use e * f; rw [mul_smul]
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ ⟨e, rfl⟩ ⟨f, hf⟩
    by_cases hb : b = 0; · simp [hb]
    have : IsUnit e := by
      apply isUnit_of_dvd_one
      use f
      rw [mul_comm]
    

中文:
实例 linearOrder
  签名: : LinearOrder (ValueGroup A K) where
  定义体: by rintro ⟨⟩; use 1; rw [one_smul]
  le_trans := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨e, rfl⟩ ⟨f, rfl⟩; use e * f; rw [mul_smul]
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ ⟨e, rfl⟩ ⟨f, hf⟩
    by_cases hb : b = 0; · simp [hb]
    have : IsUnit e := by
      apply isUnit_of_dvd_one
      use f
      rw [mul_comm]
    

Depends on / 依赖: Algebra, Algebra.smul_def, IsFractionRing, IsFractionRing.injective, IsUnit, Quotient, Quotient.sound, algebraMap, injective, isUnit_of_dvd_one, le_antisymm, le_total, le_trans, map_one, mul_comm, mul_smul, nth_rw, one_mul, one_smul, smul_def
-/
noncomputable instance linearOrder : LinearOrder (ValueGroup A K) where
  le_refl := by rintro ⟨⟩; use 1; rw [one_smul]
  le_trans := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ⟨e, rfl⟩ ⟨f, rfl⟩; use e * f; rw [mul_smul]
  le_antisymm := by
    rintro ⟨a⟩ ⟨b⟩ ⟨e, rfl⟩ ⟨f, hf⟩
    by_cases hb : b = 0; · simp [hb]
    have : IsUnit e := by
      apply isUnit_of_dvd_one
      use f
      rw [mul_comm]
      rw [← mul_smul]; rw [Algebra.smul_def] at hf
      nth_rw 2 [← one_mul b] at hf
      rw [← (algebraMap A K).map_one] at hf
      exact IsFractionRing.injective _ _ (mul_right_cancel₀ hb hf).symm
    apply Quotient.sound'
    exact ⟨this.unit, rfl⟩
  le_total := ValuationRing.le_total _ _
  toDecidableLE := Classical.decRel _

/--
Instance `commGroupWithZero` / 实例 `commGroupWithZero`

English:
instance commGroupWithZero
  signature: :
  body: { mul_assoc := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; apply Quotient.sound'; rw [mul_assoc]
    one_mul := by rintro ⟨a⟩; apply Quotient.sound'; rw [one_mul]
    mul_one := by rintro ⟨a⟩; apply Quotient.sound'; rw [mul_one]
    mul_comm := by rintro ⟨a⟩ ⟨b⟩; apply Quotient.sound'; rw [mul_comm]
    zero_mul := by r

中文:
实例 commGroupWithZero
  签名: :
  定义体: { mul_assoc := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; apply Quotient.sound'; rw [mul_assoc]
    one_mul := by rintro ⟨a⟩; apply Quotient.sound'; rw [one_mul]
    mul_one := by rintro ⟨a⟩; apply Quotient.sound'; rw [mul_one]
    mul_comm := by rintro ⟨a⟩ ⟨b⟩; apply Quotient.sound'; rw [mul_comm]
    zero_mul := by r

Depends on / 依赖: Quotient, Quotient.so, Quotient.sound, inv_zero, mul_assoc, mul_comm, mul_inv_cancel, mul_one, mul_zero, one_mul, zero_mul
-/
instance commGroupWithZero :
    CommGroupWithZero (ValueGroup A K) :=
  { mul_assoc := by rintro ⟨a⟩ ⟨b⟩ ⟨c⟩; apply Quotient.sound'; rw [mul_assoc]
    one_mul := by rintro ⟨a⟩; apply Quotient.sound'; rw [one_mul]
    mul_one := by rintro ⟨a⟩; apply Quotient.sound'; rw [mul_one]
    mul_comm := by rintro ⟨a⟩ ⟨b⟩; apply Quotient.sound'; rw [mul_comm]
    zero_mul := by rintro ⟨a⟩; apply Quotient.sound'; rw [zero_mul]
    mul_zero := by rintro ⟨a⟩; apply Quotient.sound'; rw [mul_zero]
    inv_zero := by apply Quotient.sound'; rw [inv_zero]
    mul_inv_cancel := by
      rintro ⟨a⟩ ha
      apply Quotient.sound'
      use 1
      simp only [one_smul]
      apply (mul_inv_cancel₀ _).symm
      contrapose ha
      rw [ha]
      rfl }

/--
Instance `linearOrderedCommGroupWithZero` / 实例 `linearOrderedCommGroupWithZero`

English:
instance linearOrderedCommGroupWithZero
  signature: :
  body: 0
  bot_le := by rintro ⟨a⟩; exact ⟨0, zero_smul ..⟩
  isBot_zero := by rintro ⟨a⟩; exact ⟨0, zero_smul ..⟩
  mul_lt_mul_of_pos_left := by
    simp_rw [← not_le]
    rintro ⟨a⟩ ha ⟨b⟩ ⟨c⟩ hbc
    contrapose hbc
    obtain ⟨d, hd⟩ := hbc
    simp only [Algebra.smul_def, mul_left_comm, mul_eq_mul_left

中文:
实例 linearOrderedCommGroupWithZero
  签名: :
  定义体: 0
  bot_le := by rintro ⟨a⟩; exact ⟨0, zero_smul ..⟩
  isBot_zero := by rintro ⟨a⟩; exact ⟨0, zero_smul ..⟩
  mul_lt_mul_of_pos_left := by
    simp_rw [← not_le]
    rintro ⟨a⟩ ha ⟨b⟩ ⟨c⟩ hbc
    contrapose hbc
    obtain ⟨d, hd⟩ := hbc
    simp only [Algebra.smul_def, mul_left_comm, mul_eq_mul_left
-/
noncomputable instance linearOrderedCommGroupWithZero :
    LinearOrderedCommGroupWithZero (ValueGroup A K) where
  bot := 0
  bot_le := by rintro ⟨a⟩; exact ⟨0, zero_smul ..⟩
  isBot_zero := by rintro ⟨a⟩; exact ⟨0, zero_smul ..⟩
  mul_lt_mul_of_pos_left := by
    simp_rw [← not_le]
    rintro ⟨a⟩ ha ⟨b⟩ ⟨c⟩ hbc
    contrapose hbc
    obtain ⟨d, hd⟩ := hbc
    simp only [Algebra.smul_def, mul_left_comm, mul_eq_mul_left_iff] at hd
    obtain rfl | rfl := hd
    · exact ⟨d, by simp [Algebra.smul_def]⟩
    · cases ha le_rfl

/--
Definition of `valuation` / `valuation` 的定义

English:
definition valuation
  signature: : Valuation K (ValueGroup A K) where
  body: Quotient.mk''
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add_le_max' := by
    intro a b
    obtain ⟨xa, ya, hya, rfl⟩ := IsFractionRing.div_surjective A a
    obtain ⟨xb, yb, hyb, rfl⟩ := IsFractionRing.div_surjective A b
    have : (algebraMap A K) ya != 0 := IsFractionRing.t

中文:
定义 valuation
  签名: : Valuation K (ValueGroup A K) where
  定义体: Quotient.mk''
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add_le_max' := by
    intro a b
    obtain ⟨xa, ya, hya, rfl⟩ := IsFractionRing.div_surjective A a
    obtain ⟨xb, yb, hyb, rfl⟩ := IsFractionRing.div_surjective A b
    have : (algebraMap A K) ya != 0 := IsFractionRing.t

Depends on / 依赖: Quotient, Quotient.mk
-/
noncomputable def valuation : Valuation K (ValueGroup A K) where
  toFun := Quotient.mk''
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := rfl
  map_add_le_max' := by
    intro a b
    obtain ⟨xa, ya, hya, rfl⟩ := IsFractionRing.div_surjective A a
    obtain ⟨xb, yb, hyb, rfl⟩ := IsFractionRing.div_surjective A b
    have : (algebraMap A K) ya != 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hya
    have : (algebraMap A K) yb != 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hyb
    obtain ⟨c, h | h⟩ := ValuationRing.cond (xa * yb) (xb * ya)
    · apply le_trans _ (le_max_left _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [← map_mul, ← map_add]
      congr 1; linear_combination h
    · apply le_trans _ (le_max_right _ _)
      use c + 1
      rw [Algebra.smul_def]
      field_simp
      simp only [← map_mul, ← map_add]
      congr 1; linear_combination h

/--
theorem `mem_integer_iff` / 定理 `mem_integer_iff`

English:
theorem mem_integer_iff
  given: (x : K)
  statement: x in (valuation A K).integer ↔ exists a : A, algebraMap A K a = x
  proof: by
  constructor
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def]; rw [mul_one]
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def]; rw [mul_one]

中文:
定理 mem_integer_iff
  条件: (x : K)
  结论: x in (valuation A K).integer ↔ 存在 a : A, algebraMap A K a = x
  证明: by
  constructor
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def]; rw [mul_one]
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def]; rw [mul_one]

Depends on / 依赖: Algebra, Algebra.smul_def, mul_one, smul_def
-/
theorem mem_integer_iff (x : K) : x in (valuation A K).integer ↔ exists a : A, algebraMap A K a = x := by
  constructor
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def]; rw [mul_one]
  · rintro ⟨c, rfl⟩
    use c
    rw [Algebra.smul_def]; rw [mul_one]

/--
Definition of `equivInteger` / `equivInteger` 的定义

English:
definition equivInteger
  signature: : A ≃+* (valuation A K).integer
  body: RingEquiv.ofBijective
    (show A ->ₙ+* (valuation A K).integer from
      { toFun := fun a => ⟨algebraMap A K a, (mem_integer_iff _ _ _).mpr ⟨a, rfl⟩⟩
        map_mul' := fun _ _ => by ext1; exact (algebraMap A K).map_mul _ _
        map_zero' := by ext1; exact (algebraMap A K).map_zero
        map

中文:
定义 equivInteger
  签名: : A ≃+* (valuation A K).integer
  定义体: RingEquiv.ofBijective
    (show A ->ₙ+* (valuation A K).integer from
      { toFun := fun a => ⟨algebraMap A K a, (mem_integer_iff _ _ _).mpr ⟨a, rfl⟩⟩
        map_mul' := fun _ _ => by ext1; exact (algebraMap A K).map_mul _ _
        map_zero' := by ext1; exact (algebraMap A K).map_zero
        map

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, RingEquiv, RingEquiv.ofBijective, algebraMap, apply_fun, injective, integer, map_add, map_mul, map_zero, mem_integer_iff, ofBijective, valuation
-/
noncomputable def equivInteger : A ≃+* (valuation A K).integer :=
  RingEquiv.ofBijective
    (show A ->ₙ+* (valuation A K).integer from
      { toFun := fun a => ⟨algebraMap A K a, (mem_integer_iff _ _ _).mpr ⟨a, rfl⟩⟩
        map_mul' := fun _ _ => by ext1; exact (algebraMap A K).map_mul _ _
        map_zero' := by ext1; exact (algebraMap A K).map_zero
        map_add' := fun _ _ => by ext1; exact (algebraMap A K).map_add _ _ })
    (by
      constructor
      · intro x y h
        apply_fun (algebraMap (valuation A K).integer K) at h
        exact IsFractionRing.injective _ _ h
      · rintro ⟨-, ha⟩
        rw [mem_integer_iff] at ha
        obtain ⟨a, rfl⟩ := ha
        exact ⟨a, rfl⟩)

@[simp]
/--
theorem `coe_equivInteger_apply` / 定理 `coe_equivInteger_apply`

English:
theorem coe_equivInteger_apply
  given: (a : A)
  statement: (equivInteger A K a : K) = algebraMap A K a
  proof: rfl

中文:
定理 coe_equivInteger_apply
  条件: (a : A)
  结论: (equiv整数eger A K a : K) = algebraMap A K a
  证明: rfl
-/
theorem coe_equivInteger_apply (a : A) : (equivInteger A K a : K) = algebraMap A K a := rfl

/--
theorem `range_algebraMap_eq` / 定理 `range_algebraMap_eq`

English:
theorem range_algebraMap_eq
  statement: (valuation A K).integer = (algebraMap A K).range
  proof: by
  ext; exact mem_integer_iff _ _ _

中文:
定理 range_algebraMap_eq
  结论: (valuation A K).integer = (algebraMap A K).range
  证明: by
  ext; exact mem_integer_iff _ _ _

Depends on / 依赖: mem_integer_iff
-/
theorem range_algebraMap_eq : (valuation A K).integer = (algebraMap A K).range := by
  ext; exact mem_integer_iff _ _ _

end

section

variable (A : Type u) [CommRing A] [Nontrivial A] [PreValuationRing A]

instance (priority := 100) isLocalRing : IsLocalRing A :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    obtain ⟨c, h | h⟩ := PreValuationRing.cond a (1 - a)
    · left
      refine .of_mul_eq_one (c + 1) ?_
      simp [mul_add, h]
    · right
      refine .of_mul_eq_one (c + 1) ?_
      simp [mul_add, h]

/--
Instance `le_total_ideal` / 实例 `le_total_ideal`

English:
instance le_total_ideal
  signature: : @Std.Total (Ideal A) (· <= ·)
  body: by
  constructor; intro α β
  by_cases! h : forall x : A, x in α -> x in β
  · exact Or.inl h
  obtain ⟨a, h₁, h₂⟩ := h
  right
  intro b hb
  obtain ⟨c, h | h⟩ := PreValuationRing.cond a b
  · rw [← h]
    exact Ideal.mul_mem_right _ _ h₁
  · exfalso; apply h₂; rw [← h]
    apply Ideal.mul_mem_righ

中文:
实例 le_total_ideal
  签名: : @Std.Total (Ideal A) (· <= ·)
  定义体: by
  constructor; intro α β
  by_cases! h : forall x : A, x in α -> x in β
  · exact Or.inl h
  obtain ⟨a, h₁, h₂⟩ := h
  right
  intro b hb
  obtain ⟨c, h | h⟩ := PreValuationRing.cond a b
  · rw [← h]
    exact Ideal.mul_mem_right _ _ h₁
  · exfalso; apply h₂; rw [← h]
    apply Ideal.mul_mem_righ

Depends on / 依赖: Ideal.mul_mem_right, Or.inl, PreValuationRing, PreValuationRing.cond, mul_mem_right
-/
instance le_total_ideal : @Std.Total (Ideal A) (· <= ·) := by
  constructor; intro α β
  by_cases! h : forall x : A, x in α -> x in β
  · exact Or.inl h
  obtain ⟨a, h₁, h₂⟩ := h
  right
  intro b hb
  obtain ⟨c, h | h⟩ := PreValuationRing.cond a b
  · rw [← h]
    exact Ideal.mul_mem_right _ _ h₁
  · exfalso; apply h₂; rw [← h]
    apply Ideal.mul_mem_right _ _ hb

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableLE
  signature: (Ideal A)] : LinearOrder (Ideal A)
  body: Lattice.toLinearOrder (Ideal A)

中文:
实例 [DecidableLE
  签名: (Ideal A)] : LinearOrder (Ideal A)
  定义体: Lattice.toLinearOrder (Ideal A)

Depends on / 依赖: Lattice, Lattice.toLinearOrder, toLinearOrder
-/
noncomputable instance [DecidableLE (Ideal A)] : LinearOrder (Ideal A) :=
  Lattice.toLinearOrder (Ideal A)

end

section

section dvd

variable {R : Type*}

/--
theorem `_root_.PreValuationRing.iff_dvd_total` / 定理 `_root_.PreValuationRing.iff_dvd_total`

English:
theorem _root_.PreValuationRing.iff_dvd_total
  given: [Semigroup R]
  proof: by
  refine ⟨fun H => ⟨fun a b => ?_⟩, fun H => ⟨fun a b => ?_⟩⟩
  · obtain ⟨c, rfl | rfl⟩ := PreValuationRing.cond a b <;> simp
  · obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := H.total a b <;> use c <;> simp

中文:
定理 _root_.PreValuationRing.iff_dvd_total
  条件: [Semigroup R]
  证明: by
  refine ⟨fun H => ⟨fun a b => ?_⟩, fun H => ⟨fun a b => ?_⟩⟩
  · obtain ⟨c, rfl | rfl⟩ := PreValuationRing.cond a b <;> simp
  · obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := H.total a b <;> use c <;> simp

Depends on / 依赖: H.total, PreValuationRing, PreValuationRing.cond
-/
theorem _root_.PreValuationRing.iff_dvd_total [Semigroup R] :
    PreValuationRing R ↔ @Std.Total R (· ∣ ·) := by
  refine ⟨fun H => ⟨fun a b => ?_⟩, fun H => ⟨fun a b => ?_⟩⟩
  · obtain ⟨c, rfl | rfl⟩ := PreValuationRing.cond a b <;> simp
  · obtain ⟨c, rfl⟩ | ⟨c, rfl⟩ := H.total a b <;> use c <;> simp

/--
theorem `_root_.PreValuationRing.iff_ideal_total` / 定理 `_root_.PreValuationRing.iff_ideal_total`

English:
theorem _root_.PreValuationRing.iff_ideal_total
  given: [CommRing R]
  proof: by
  classical
  refine ⟨fun _ => ⟨le_total⟩, fun H => PreValuationRing.iff_dvd_total.mpr ⟨fun a b => ?_⟩⟩
  have := H.total (Ideal.span {a}) (Ideal.span {b})
  simp_rw [Ideal.span_singleton_le_span_singleton] at this
  exact this.symm

中文:
定理 _root_.PreValuationRing.iff_ideal_total
  条件: [CommRing R]
  证明: by
  classical
  refine ⟨fun _ => ⟨le_total⟩, fun H => PreValuationRing.iff_dvd_total.mpr ⟨fun a b => ?_⟩⟩
  have := H.total (Ideal.span {a}) (Ideal.span {b})
  simp_rw [Ideal.span_singleton_le_span_singleton] at this
  exact this.symm

Depends on / 依赖: H.total, Ideal.span, Ideal.span_singleton_le_span_singleton, PreValuationRing, PreValuationRing.iff_dvd_total.mpr, classical, iff_dvd_total, le_total, simp_rw, span_singleton_le_span_singleton, this.symm
-/
theorem _root_.PreValuationRing.iff_ideal_total [CommRing R] :
    PreValuationRing R ↔ @Std.Total (Ideal R) (· <= ·) := by
  classical
  refine ⟨fun _ => ⟨le_total⟩, fun H => PreValuationRing.iff_dvd_total.mpr ⟨fun a b => ?_⟩⟩
  have := H.total (Ideal.span {a}) (Ideal.span {b})
  simp_rw [Ideal.span_singleton_le_span_singleton] at this
  exact this.symm

variable (K)

/--
theorem `dvd_total` / 定理 `dvd_total`

English:
theorem dvd_total
  given: [Semigroup R] [h : PreValuationRing R] (x y : R)
  statement: x ∣ y ∨ y ∣ x
  proof: (PreValuationRing.iff_dvd_total.mp h).total x y

中文:
定理 dvd_total
  条件: [Semigroup R] [h : PreValuationRing R] (x y : R)
  结论: x ∣ y ∨ y ∣ x
  证明: (PreValuationRing.iff_dvd_total.mp h).total x y

Depends on / 依赖: PreValuationRing, PreValuationRing.iff_dvd_total.mp, iff_dvd_total
-/
theorem dvd_total [Semigroup R] [h : PreValuationRing R] (x y : R) : x ∣ y ∨ y ∣ x :=
  (PreValuationRing.iff_dvd_total.mp h).total x y

end dvd

variable {R : Type*} [CommRing R] [IsDomain R] (K : Type*)
variable [Field K] [Algebra R K] [IsFractionRing R K]

/--
theorem `iff_dvd_total` / 定理 `iff_dvd_total`

English:
theorem iff_dvd_total
  statement: ValuationRing R ↔ @Std.Total R (· ∣ ·)
  proof: Iff.trans (⟨fun inst => inst.toPreValuationRing, fun _ => .mk⟩)
    PreValuationRing.iff_dvd_total

中文:
定理 iff_dvd_total
  结论: ValuationRing R ↔ @Std.Total R (· ∣ ·)
  证明: Iff.trans (⟨fun inst => inst.toPreValuationRing, fun _ => .mk⟩)
    PreValuationRing.iff_dvd_total

Depends on / 依赖: Iff.trans, PreValuationRing, PreValuationRing.iff_dvd_total, iff_dvd_total, inst.toPreValuationRing, toPreValuationRing
-/
theorem iff_dvd_total : ValuationRing R ↔ @Std.Total R (· ∣ ·) :=
  Iff.trans (⟨fun inst => inst.toPreValuationRing, fun _ => .mk⟩)
    PreValuationRing.iff_dvd_total

/--
theorem `iff_ideal_total` / 定理 `iff_ideal_total`

English:
theorem iff_ideal_total
  statement: ValuationRing R ↔ @Std.Total (Ideal R) (· <= ·)
  proof: Iff.trans (⟨fun inst => inst.toPreValuationRing, fun _ => .mk⟩)
    PreValuationRing.iff_ideal_total

中文:
定理 iff_ideal_total
  结论: ValuationRing R ↔ @Std.Total (Ideal R) (· <= ·)
  证明: Iff.trans (⟨fun inst => inst.toPreValuationRing, fun _ => .mk⟩)
    PreValuationRing.iff_ideal_total

Depends on / 依赖: Iff.trans, PreValuationRing, PreValuationRing.iff_ideal_total, iff_ideal_total, inst.toPreValuationRing, toPreValuationRing
-/
theorem iff_ideal_total : ValuationRing R ↔ @Std.Total (Ideal R) (· <= ·) :=
  Iff.trans (⟨fun inst => inst.toPreValuationRing, fun _ => .mk⟩)
    PreValuationRing.iff_ideal_total

/--
theorem `unique_irreducible` / 定理 `unique_irreducible`

English:
theorem unique_irreducible
  given: [PreValuationRing R] ⦃p q
  statement: R⦄ (hp : Irreducible p)
  proof: by
  have := dvd_total p q
  rw [Irreducible.dvd_comm hp hq]; rw [or_self_iff] at this
  exact associated_of_dvd_dvd (Irreducible.dvd_symm hq hp this) this

中文:
定理 unique_irreducible
  条件: [PreValuationRing R] ⦃p q
  结论: R⦄ (hp : Irreducible p)
  证明: by
  have := dvd_total p q
  rw [Irreducible.dvd_comm hp hq]; rw [or_self_iff] at this
  exact associated_of_dvd_dvd (Irreducible.dvd_symm hq hp this) this

Depends on / 依赖: Irreducible, Irreducible.dvd_comm, Irreducible.dvd_symm, associated_of_dvd_dvd, dvd_comm, dvd_symm, dvd_total, or_self_iff
-/
theorem unique_irreducible [PreValuationRing R] ⦃p q : R⦄ (hp : Irreducible p)
    (hq : Irreducible q) : Associated p q := by
  have := dvd_total p q
  rw [Irreducible.dvd_comm hp hq]; rw [or_self_iff] at this
  exact associated_of_dvd_dvd (Irreducible.dvd_symm hq hp this) this

variable (R)

/--
theorem `iff_isInteger_or_isInteger` / 定理 `iff_isInteger_or_isInteger`

English:
theorem iff_isInteger_or_isInteger
  proof: by
  constructor
  · intro H x
    obtain ⟨x : R, y, hy, rfl⟩ := IsFractionRing.div_surjective R x
    have := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hy)
    obtain ⟨s, rfl | rfl⟩ := ValuationRing.cond x y
    · exact Or.inr
⟨s, eq_inv_of_mul_eq_one_left by r

中文:
定理 iff_isInteger_or_isInteger
  证明: by
  constructor
  · intro H x
    obtain ⟨x : R, y, hy, rfl⟩ := IsFractionRing.div_surjective R x
    have := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hy)
    obtain ⟨s, rfl | rfl⟩ := ValuationRing.cond x y
    · exact Or.inr
⟨s, eq_inv_of_mul_eq_one_left by r

Depends on / 依赖: IsFractionRing, IsFractionRing.div_surjective, IsFractionRing.injective, Or.inl, Or.inr, PreValuationRing, ValuationRing, ValuationRing.cond, div_eq_one_iff_eq, div_surjective, eq_div_iff, eq_inv_of_mul_eq_one_left, injective, map_mul, map_ne_zero_iff, mul_comm, mul_div, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero
-/
theorem iff_isInteger_or_isInteger :
    ValuationRing R ↔ forall x : K, IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ := by
  constructor
  · intro H x
    obtain ⟨x : R, y, hy, rfl⟩ := IsFractionRing.div_surjective R x
    have := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hy)
    obtain ⟨s, rfl | rfl⟩ := ValuationRing.cond x y
    · exact Or.inr
⟨s, eq_inv_of_mul_eq_one_left by rwa [mul_div, div_eq_one_iff_eq, map_mul, mul_comm]⟩
    · exact Or.inl ⟨s, by rwa [eq_div_iff, map_mul, mul_comm]⟩
  · intro H
    suffices PreValuationRing R from mk
    constructor
    intro a b
by_cases ha : a = 0; · subst ha; exact ⟨0, Or.inr mul_zero b⟩
by_cases hb : b = 0; · subst hb; exact ⟨0, Or.inl mul_zero a⟩
    replace ha := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
    replace hb := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb
    obtain ⟨c, e⟩ | ⟨c, e⟩ := H (algebraMap R K a / algebraMap R K b)
    · rw [eq_div_iff hb, ← map_mul, (IsFractionRing.injective R K).eq_iff, mul_comm] at e
      exact ⟨c, Or.inr e⟩
    · rw [inv_div, eq_div_iff ha, ← map_mul, (IsFractionRing.injective R K).eq_iff, mul_comm c] at e
      exact ⟨c, Or.inl e⟩

variable {K}

/--
theorem `isInteger_or_isInteger` / 定理 `isInteger_or_isInteger`

English:
theorem isInteger_or_isInteger
  given: [h : ValuationRing R] (x : K)
  proof: (iff_isInteger_or_isInteger R K).mp h x

中文:
定理 isInteger_or_isInteger
  条件: [h : ValuationRing R] (x : K)
  证明: (iff_isInteger_or_isInteger R K).mp h x

Depends on / 依赖: iff_isInteger_or_isInteger
-/
theorem isInteger_or_isInteger [h : ValuationRing R] (x : K) :
    IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹ :=
  (iff_isInteger_or_isInteger R K).mp h x

variable {R}

-- This implies that valuation rings are integrally closed through typeclass search.
instance (priority := 100) [ValuationRing R] : IsBezout R := by
  classical
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  rw [Ideal.span_insert]
  rcases le_total (Ideal.span {x} : Ideal R) (Ideal.span {y}) with h | h
  · rw [sup_eq_right.mpr h]; exact ⟨⟨_, rfl⟩⟩
  · rw [sup_eq_left.mpr h]; exact ⟨⟨_, rfl⟩⟩

instance (priority := 100) [IsLocalRing R] [IsBezout R] : ValuationRing R := by
  refine iff_dvd_total.mpr ⟨fun a b => ?_⟩
  obtain ⟨g, e : _ = Ideal.span _⟩ := IsBezout.span_pair_isPrincipal a b
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp
      (show a in Ideal.span {g} by rw [← e]; exact Ideal.subset_span (by simp))
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp
      (show b in Ideal.span {g} by rw [← e]; exact Ideal.subset_span (by simp))
  obtain ⟨x, y, e'⟩ := Ideal.mem_span_pair.mp
      (show g in Ideal.span {a * g, b * g} by rw [e]; exact Ideal.subset_span (by simp))
  rcases eq_or_ne g 0 with h | h
  · simp [h]
  have : x * a + y * b = 1 := by
    apply mul_left_injective₀ h; convert! e' using 1 <;> ring
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one this with h' | h' <;> [left; right]
  all_goals exact mul_dvd_mul_right (isUnit_iff_forall_dvd.mp (isUnit_of_mul_isUnit_right h') _) _

/--
theorem `iff_local_bezout_domain` / 定理 `iff_local_bezout_domain`

English:
theorem iff_local_bezout_domain
  statement: ValuationRing R ↔ IsLocalRing R ∧ IsBezout R
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => inferInstance⟩

中文:
定理 iff_local_bezout_domain
  结论: ValuationRing R ↔ IsLocalRing R ∧ IsBezout R
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => inferInstance⟩
-/
theorem iff_local_bezout_domain : ValuationRing R ↔ IsLocalRing R ∧ IsBezout R :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => inferInstance⟩

/--
theorem `TFAE` / 定理 `TFAE`

English:
theorem TFAE
  given: (R : Type u) [CommRing R] [IsDomain R]
  proof: by
  tfae_have 1 ↔ 2 := iff_isInteger_or_isInteger R _
  tfae_have 1 ↔ 3 := iff_dvd_total
  tfae_have 1 ↔ 4 := iff_ideal_total
  tfae_have 1 ↔ 5 := iff_local_bezout_domain
  tfae_finish

中文:
定理 TFAE
  条件: (R : 类型u) [CommRing R] [IsDomain R]
  证明: by
  tfae_have 1 ↔ 2 := iff_isInteger_or_isInteger R _
  tfae_have 1 ↔ 3 := iff_dvd_total
  tfae_have 1 ↔ 4 := iff_ideal_total
  tfae_have 1 ↔ 5 := iff_local_bezout_domain
  tfae_finish
-/
protected theorem TFAE (R : Type u) [CommRing R] [IsDomain R] :
    List.TFAE
      [ValuationRing R,
        forall x : FractionRing R, IsLocalization.IsInteger R x ∨ IsLocalization.IsInteger R x⁻¹,
        @Std.Total R (· ∣ ·), @Std.Total (Ideal R) (· <= ·), IsLocalRing R ∧ IsBezout R] := by
  tfae_have 1 ↔ 2 := iff_isInteger_or_isInteger R _
  tfae_have 1 ↔ 3 := iff_dvd_total
  tfae_have 1 ↔ 4 := iff_ideal_total
  tfae_have 1 ↔ 5 := iff_local_bezout_domain
  tfae_finish

end

/--
theorem `_root_.Function.Surjective.preValuationRing` / 定理 `_root_.Function.Surjective.preValuationRing`

English:
theorem _root_.Function.Surjective.preValuationRing
  statement: {R S : Type*} [Mul R] [PreValuationRing R]
  proof: ⟨fun a b => by
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hf a, hf b
    obtain ⟨c, rfl | rfl⟩ := PreValuationRing.cond a b
    exacts [⟨f c, Or.inl <| (map_mul _ _ _).symm⟩, ⟨f c, Or.inr <| (map_mul _ _ _).symm⟩]⟩

中文:
定理 _root_.Function.Surjective.preValuationRing
  结论: {R S : 类型} [Mul R] [PreValuationRing R]
  证明: ⟨fun a b => by
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hf a, hf b
    obtain ⟨c, rfl | rfl⟩ := PreValuationRing.cond a b
    exacts [⟨f c, Or.inl <| (map_mul _ _ _).symm⟩, ⟨f c, Or.inr <| (map_mul _ _ _).symm⟩]⟩

Depends on / 依赖: Or.inl, Or.inr, PreValuationRing, PreValuationRing.cond, exacts, map_mul
-/
theorem _root_.Function.Surjective.preValuationRing {R S : Type*} [Mul R] [PreValuationRing R]
    [Mul S] (f : R ->ₙ* S) (hf : Function.Surjective f) :
    PreValuationRing S :=
  ⟨fun a b => by
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hf a, hf b
    obtain ⟨c, rfl | rfl⟩ := PreValuationRing.cond a b
    exacts [⟨f c, Or.inl <| (map_mul _ _ _).symm⟩, ⟨f c, Or.inr <| (map_mul _ _ _).symm⟩]⟩

/--
theorem `_root_.Function.Surjective.valuationRing` / 定理 `_root_.Function.Surjective.valuationRing`

English:
theorem _root_.Function.Surjective.valuationRing
  statement: {R S : Type*} [NonAssocSemiring R]
  proof: have : PreValuationRing S := Function.Surjective.preValuationRing (R := R) f hf
  .mk

中文:
定理 _root_.Function.Surjective.valuationRing
  结论: {R S : 类型} [NonAssocSemiring R]
  证明: have : PreValuationRing S := Function.Surjective.preValuationRing (R := R) f hf
  .mk

Depends on / 依赖: Function, Function.Surjective.preValuationRing, PreValuationRing, Surjective, preValuationRing
-/
theorem _root_.Function.Surjective.valuationRing {R S : Type*} [NonAssocSemiring R]
    [PreValuationRing R] [CommRing S] [IsDomain S] (f : R ->+* S) (hf : Function.Surjective f) :
    ValuationRing S :=
  have : PreValuationRing S := Function.Surjective.preValuationRing (R := R) f hf
  .mk

section

variable {𝒪 : Type u} {K : Type v} {Γ : Type w} [CommRing 𝒪] [Field K] [Algebra 𝒪 K]
  [LinearOrderedCommGroupWithZero Γ]

/--
lemma `_root_.isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective` / 引理 `_root_.isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective`

English:
lemma _root_.isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
  proof: by
  have : IsDomain 𝒪 := hinj.isDomain
  have := (faithfulSMul_iff_algebraMap_injective ..).2 hinj
  have := IsDomain.of_faithfulSMul 𝒪 K
  refine ⟨by simp, ?_, fun hab => ⟨1, by simpa using hab⟩⟩
  intro x
  obtain ⟨a, ha⟩ := h x
  by_cases h0 : a = 0
  · refine ⟨⟨0, 1⟩, by simpa [h0, eq_comm] usi

中文:
引理 _root_.isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
  证明: by
  have : IsDomain 𝒪 := hinj.isDomain
  have := (faithfulSMul_iff_algebraMap_injective ..).2 hinj
  have := IsDomain.of_faithfulSMul 𝒪 K
  refine ⟨by simp, ?_, fun hab => ⟨1, by simpa using hab⟩⟩
  intro x
  obtain ⟨a, ha⟩ := h x
  by_cases h0 : a = 0
  · refine ⟨⟨0, 1⟩, by simpa [h0, eq_comm] usi

Depends on / 依赖: IsDomain, IsDomain.of_faithfulSMul, algebraMap, eq_comm, eq_div_iff, faithfulSMul_iff_algebraMap_injective, hinj.isDomain, inv_eq_iff_eq_inv, isDomain, mem_nonZeroD, of_faithfulSMul, one_div
-/
lemma _root_.isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
    (h : forall (x : K), exists a : 𝒪, x = algebraMap 𝒪 K a ∨ x⁻¹ = algebraMap 𝒪 K a)
    (hinj : Function.Injective (algebraMap 𝒪 K)) :
    IsFractionRing 𝒪 K := by
  have : IsDomain 𝒪 := hinj.isDomain
  have := (faithfulSMul_iff_algebraMap_injective ..).2 hinj
  have := IsDomain.of_faithfulSMul 𝒪 K
  refine ⟨by simp, ?_, fun hab => ⟨1, by simpa using hab⟩⟩
  intro x
  obtain ⟨a, ha⟩ := h x
  by_cases h0 : a = 0
  · refine ⟨⟨0, 1⟩, by simpa [h0, eq_comm] using ha⟩
  · have : algebraMap 𝒪 K a != 0 := by simpa using h0
    rw [inv_eq_iff_eq_inv]; rw [← one_div]; rw [eq_div_iff this] at ha
    cases ha with
    | inl ha => exact ⟨⟨a, 1⟩, by simpa⟩
    | inr ha => exact ⟨⟨1, ⟨a, mem_nonZeroDivisors_of_ne_zero h0⟩⟩, by simpa using ha⟩

/--
lemma `_root_.Valuation.Integers.isFractionRing` / 引理 `_root_.Valuation.Integers.isFractionRing`

English:
lemma _root_.Valuation.Integers.isFractionRing
  given: {v : Valuation K Γ} (hv : v.Integers 𝒪)
  proof: isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
    hv.eq_algebraMap_or_inv_eq_algebraMap hv.hom_inj

中文:
引理 _root_.Valuation.Integers.isFractionRing
  条件: {v : Valuation K Γ} (hv : v.整数egers 𝒪)
  证明: isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
    hv.eq_algebraMap_or_inv_eq_algebraMap hv.hom_inj

Depends on / 依赖: eq_algebraMap_or_inv_eq_algebraMap, hom_inj, hv.eq_algebraMap_or_inv_eq_algebraMap, hv.hom_inj, isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
-/
lemma _root_.Valuation.Integers.isFractionRing {v : Valuation K Γ} (hv : v.Integers 𝒪) :
    IsFractionRing 𝒪 K :=
  isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective
    hv.eq_algebraMap_or_inv_eq_algebraMap hv.hom_inj

/--
Instance `instIsFractionRingInteger` / 实例 `instIsFractionRingInteger`

English:
instance instIsFractionRingInteger
  signature: (v : Valuation K Γ)
  body: (Valuation.integer.integers v).isFractionRing

中文:
实例 instIsFractionRingInteger
  签名: (v : Valuation K Γ)
  定义体: (Valuation.integer.integers v).isFractionRing

Depends on / 依赖: Valuation, Valuation.integer.integers, integer, integers, isFractionRing
-/
instance instIsFractionRingInteger (v : Valuation K Γ) : IsFractionRing v.integer K :=
  (Valuation.integer.integers v).isFractionRing

/--
theorem `of_integers` / 定理 `of_integers`

English:
theorem of_integers
  given: (v : Valuation K Γ) (hh : v.Integers 𝒪)
  proof: hh.hom_inj.isDomain
    ValuationRing 𝒪 := by
  have := hh.hom_inj.isDomain
  suffices PreValuationRing 𝒪 from .mk
  constructor
  intro a b
  rcases le_total (v (algebraMap 𝒪 K a)) (v (algebraMap 𝒪 K b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    use c; exact Or.inr hc.s

中文:
定理 of_integers
  条件: (v : Valuation K Γ) (hh : v.整数egers 𝒪)
  证明: hh.hom_inj.isDomain
    ValuationRing 𝒪 := by
  have := hh.hom_inj.isDomain
  suffices PreValuationRing 𝒪 from .mk
  constructor
  intro a b
  rcases le_total (v (algebraMap 𝒪 K a)) (v (algebraMap 𝒪 K b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    use c; exact Or.inr hc.s

Depends on / 依赖: hh.hom_inj.isDomain, hom_inj, isDomain
-/
theorem of_integers (v : Valuation K Γ) (hh : v.Integers 𝒪) :
    haveI := hh.hom_inj.isDomain
    ValuationRing 𝒪 := by
  have := hh.hom_inj.isDomain
  suffices PreValuationRing 𝒪 from .mk
  constructor
  intro a b
  rcases le_total (v (algebraMap 𝒪 K a)) (v (algebraMap 𝒪 K b)) with h | h
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    use c; exact Or.inr hc.symm
  · obtain ⟨c, hc⟩ := Valuation.Integers.dvd_of_le hh h
    use c; exact Or.inl hc.symm

/--
Instance `instValuationRingInteger` / 实例 `instValuationRingInteger`

English:
instance instValuationRingInteger
  signature: (v : Valuation K Γ)
  body: of_integers (v := v) (Valuation.integer.integers v)

中文:
实例 instValuationRingInteger
  签名: (v : Valuation K Γ)
  定义体: of_integers (v := v) (Valuation.integer.integers v)

Depends on / 依赖: Valuation, Valuation.integer.integers, integer, integers, of_integers
-/
instance instValuationRingInteger (v : Valuation K Γ) : ValuationRing v.integer :=
  of_integers (v := v) (Valuation.integer.integers v)

/--
theorem `isFractionRing_iff` / 定理 `isFractionRing_iff`

English:
theorem isFractionRing_iff
  given: [IsDomain 𝒪] [ValuationRing 𝒪]
  proof: by
  refine ⟨fun h => ⟨fun x => ?_, IsFractionRing.injective _ _⟩, fun h => ?_⟩
  · obtain (⟨a, e⟩ | ⟨a, e⟩) := isInteger_or_isInteger 𝒪 x
    exacts [⟨a, .inl e.symm⟩, ⟨a, .inr e.symm⟩]
  · exact isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective h.1 h.2

中文:
定理 isFractionRing_iff
  条件: [IsDomain 𝒪] [ValuationRing 𝒪]
  证明: by
  refine ⟨fun h => ⟨fun x => ?_, IsFractionRing.injective _ _⟩, fun h => ?_⟩
  · obtain (⟨a, e⟩ | ⟨a, e⟩) := isInteger_or_isInteger 𝒪 x
    exacts [⟨a, .inl e.symm⟩, ⟨a, .inr e.symm⟩]
  · exact isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective h.1 h.2

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, e.symm, exacts, injective, isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective, isInteger_or_isInteger
-/
theorem isFractionRing_iff [IsDomain 𝒪] [ValuationRing 𝒪] :
    IsFractionRing 𝒪 K ↔
      (forall (x : K), exists a : 𝒪, x = algebraMap 𝒪 K a ∨ x⁻¹ = algebraMap 𝒪 K a) ∧
        Function.Injective (algebraMap 𝒪 K) := by
  refine ⟨fun h => ⟨fun x => ?_, IsFractionRing.injective _ _⟩, fun h => ?_⟩
  · obtain (⟨a, e⟩ | ⟨a, e⟩) := isInteger_or_isInteger 𝒪 x
    exacts [⟨a, .inl e.symm⟩, ⟨a, .inr e.symm⟩]
  · exact isFractionRing_of_exists_eq_algebraMap_or_inv_eq_algebraMap_of_injective h.1 h.2

end

section

variable (K : Type u) [Field K]

/-- A field is a valuation ring. -/
instance (priority := 100) of_field : ValuationRing K := inferInstance

end

end ValuationRing
