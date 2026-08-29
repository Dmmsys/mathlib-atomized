/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Group.Submonoid.Units
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Multiplicative characters of finite rings and fields

Let `R` and `R'` be commutative rings.
A *multiplicative character* of `R` with values in `R'` is a morphism of
monoids from the multiplicative monoid of `R` into that of `R'`
that sends non-units to zero.

We use the namespace `MulChar` for the definitions and results.

## Main results

We show that the multiplicative characters form a group (if `R'` is commutative);
see `MulChar.commGroup`. We also provide an equivalence with the
homomorphisms `Rˣ →* R'ˣ`; see `MulChar.equivToUnitHom`.

We define a multiplicative character to be *quadratic* if its values
are among `0`, `1` and `-1`, and we prove some properties of quadratic characters.

Finally, we show that the sum of all values of a nontrivial multiplicative
character vanishes; see `MulChar.IsNontrivial.sum_eq_zero`.

## Tags

multiplicative character
-/

@[expose] public section

open scoped Ring


/-!
### Definitions related to multiplicative characters

Even though the intended use is when domain and target of the characters
are commutative rings, we define them in the more general setting when
the domain is a commutative monoid and the target is a commutative monoid
with zero. (We need a zero in the target, since non-units are supposed
to map to zero.)

In this setting, there is an equivalence between multiplicative characters
`R → R'` and group homomorphisms `Rˣ → R'ˣ`, and the multiplicative characters
have a natural structure as a commutative group.
-/


section Defi

-- The domain of our multiplicative characters
variable (R : Type*) [CommMonoid R]

-- The target
variable (R' : Type*) [CommMonoidWithZero R']

/--
Definition of `MulChar` / `MulChar` 的定义

English:
structure MulChar
  parameters: extends MonoidHom R R'
  extends: MonoidHom R R'
  axioms and operations (1):
    - map_nonunit' : forall a : R, ¬IsUnit a -> toFun a = 0

中文:
结构 MulChar
  参数: extends MonoidHom R R'
  继承: MonoidHom R R'
  公理与运算 (1 个):
    - map_nonunit' : 对任意 a : R, ¬IsUnit a -> toFun a = 0
-/
structure MulChar extends MonoidHom R R' where
  map_nonunit' : forall a : R, ¬IsUnit a -> toFun a = 0

/--
Instance `MulChar.instFunLike` / 实例 `MulChar.instFunLike`

English:
instance MulChar.instFunLike
  signature: : FunLike (MulChar R R') R R'
  body: ⟨fun χ => χ.toFun,
    fun χ₀ χ₁ h => by cases χ₀; cases χ₁; congr; apply MonoidHom.ext (fun _ => congr_fun h _)⟩

中文:
实例 MulChar.instFunLike
  签名: : FunLike (MulChar R R') R R'
  定义体: ⟨fun χ => χ.toFun,
    fun χ₀ χ₁ h => by cases χ₀; cases χ₁; congr; apply MonoidHom.ext (fun _ => congr_fun h _)⟩

Depends on / 依赖: MonoidHom, MonoidHom.ext, congr_fun
-/
instance MulChar.instFunLike : FunLike (MulChar R R') R R' :=
  ⟨fun χ => χ.toFun,
    fun χ₀ χ₁ h => by cases χ₀; cases χ₁; congr; apply MonoidHom.ext (fun _ => congr_fun h _)⟩

/--
Definition of `MulCharClass` / `MulCharClass` 的定义

English:
class MulCharClass
  parameters: (F : Type*) (R R' : outParam Type*) [CommMonoid R]
  extends: MonoidHomClass F R R'
  axioms and operations (1):
    - map_nonunit : forall (χ : F) {a : R} (_ : ¬IsUnit a), χ a = 0

中文:
类 MulCharClass
  参数: (F : 类型) (R R' : outParam 类型) [CommMonoid R]
  继承: MonoidHomClass F R R'
  公理与运算 (1 个):
    - map_nonunit : 对任意 (χ : F) {a : R} (_ : ¬IsUnit a), χ a = 0
-/
class MulCharClass (F : Type*) (R R' : outParam Type*) [CommMonoid R]
    [CommMonoidWithZero R'] [FunLike F R R'] : Prop extends MonoidHomClass F R R' where
  map_nonunit : forall (χ : F) {a : R} (_ : ¬IsUnit a), χ a = 0

initialize_simps_projections MulChar (toFun -> apply, -toMonoidHom)

end Defi

namespace MulChar

attribute [scoped simp] MulCharClass.map_nonunit

section Group

-- The domain of our multiplicative characters
variable {R : Type*} [CommMonoid R]

-- The target
variable {R' : Type*} [CommMonoidWithZero R']

variable (R R') in
/-- The trivial multiplicative character. It takes the value `0` on non-units and
the value `1` on units. -/
@[simps]
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : MulChar R R' where
  body: by classical exact fun x => if IsUnit x then 1 else 0
  map_nonunit' := by
    intro a ha
    simp only [ha, if_false]
  map_one' := by simp only [isUnit_one, if_true]
  map_mul' := by
    intro x y
    classical
      simp only [IsUnit.mul_iff, boole_mul]
      split_ifs <;> tauto

@[simp]

中文:
定义 trivial
  签名: : MulChar R R' where
  定义体: by classical exact fun x => if IsUnit x then 1 else 0
  map_nonunit' := by
    intro a ha
    simp only [ha, if_false]
  map_one' := by simp only [isUnit_one, if_true]
  map_mul' := by
    intro x y
    classical
      simp only [IsUnit.mul_iff, boole_mul]
      split_ifs <;> tauto

@[simp]

Depends on / 依赖: IsUnit, IsUnit.mul_iff, boole_mul, classical, if_false, if_true, isUnit_one, map_mul, map_nonunit, map_one, mul_iff, split_ifs
-/
noncomputable def trivial : MulChar R R' where
  toFun := by classical exact fun x => if IsUnit x then 1 else 0
  map_nonunit' := by
    intro a ha
    simp only [ha, if_false]
  map_one' := by simp only [isUnit_one, if_true]
  map_mul' := by
    intro x y
    classical
      simp only [IsUnit.mul_iff, boole_mul]
      split_ifs <;> tauto

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : R ->* R') (hf)
  statement: (MulChar.mk f hf : R -> R') = f
  proof: rfl

中文:
定理 coe_mk
  条件: (f : R ->* R') (hf)
  结论: (MulChar.mk f hf : R -> R') = f
  证明: rfl
-/
theorem coe_mk (f : R ->* R') (hf) : (MulChar.mk f hf : R -> R') = f :=
  rfl

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {χ χ' : MulChar R R'} (h : forall a, χ a = χ' a)
  statement: χ = χ'
  proof: DFunLike.ext _ _ h

中文:
定理 ext'
  条件: {χ χ' : MulChar R R'} (h : 对任意 a, χ a = χ' a)
  结论: χ = χ'
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext' {χ χ' : MulChar R R'} (h : forall a, χ a = χ' a) : χ = χ' := DFunLike.ext _ _ h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulCharClass (MulChar R R') R R'
  body: χ.map_mul'
  map_one χ := χ.map_one'
  map_nonunit χ := χ.map_nonunit' _

中文:
实例 :
  签名: MulCharClass (MulChar R R') R R'
  定义体: χ.map_mul'
  map_one χ := χ.map_one'
  map_nonunit χ := χ.map_nonunit' _

Depends on / 依赖: map_mul
-/
instance : MulCharClass (MulChar R R') R R' where
  map_mul χ := χ.map_mul'
  map_one χ := χ.map_one'
  map_nonunit χ := χ.map_nonunit' _

/--
theorem `map_nonunit` / 定理 `map_nonunit`

English:
theorem map_nonunit
  given: (χ : MulChar R R') {a : R} (ha : ¬IsUnit a)
  statement: χ a = 0
  proof: χ.map_nonunit' a ha

中文:
定理 map_nonunit
  条件: (χ : MulChar R R') {a : R} (ha : ¬IsUnit a)
  结论: χ a = 0
  证明: χ.map_nonunit' a ha

Depends on / 依赖: map_nonunit
-/
theorem map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUnit a) : χ a = 0 :=
  χ.map_nonunit' a ha

/-- Extensionality. Since `MulChar`s always take the value zero on non-units, it is sufficient
to compare the values on units. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a)
  statement: χ = χ'
  proof: by
  apply ext'
  intro a
  by_cases ha : IsUnit a
  · exact h ha.unit
  · rw [map_nonunit χ ha, map_nonunit χ' ha]

中文:
定理 ext
  条件: {χ χ' : MulChar R R'} (h : 对任意 a : Rˣ, χ a = χ' a)
  结论: χ = χ'
  证明: by
  apply ext'
  intro a
  by_cases ha : IsUnit a
  · exact h ha.unit
  · rw [map_nonunit χ ha, map_nonunit χ' ha]

Depends on / 依赖: IsUnit, ha.unit, map_nonunit
-/
theorem ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) : χ = χ' := by
  apply ext'
  intro a
  by_cases ha : IsUnit a
  · exact h ha.unit
  · rw [map_nonunit χ ha, map_nonunit χ' ha]

/-!
### Equivalence of multiplicative characters with homomorphisms on units

We show that restriction / extension by zero gives an equivalence
between `MulChar R R'` and `Rˣ →* R'ˣ`.
-/


/--
Definition of `toUnitHom` / `toUnitHom` 的定义

English:
definition toUnitHom
  signature: (χ : MulChar R R')
  body: Units.map χ

中文:
定义 toUnitHom
  签名: (χ : MulChar R R')
  定义体: Units.map χ

Depends on / 依赖: Units.map
-/
def toUnitHom (χ : MulChar R R') : Rˣ ->* R'ˣ :=
  Units.map χ

/--
theorem `coe_toUnitHom` / 定理 `coe_toUnitHom`

English:
theorem coe_toUnitHom
  given: (χ : MulChar R R') (a : Rˣ)
  statement: ↑(χ.toUnitHom a) = χ a
  proof: rfl

中文:
定理 coe_toUnitHom
  条件: (χ : MulChar R R') (a : Rˣ)
  结论: ↑(χ.toUnitHom a) = χ a
  证明: rfl
-/
theorem coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.toUnitHom a) = χ a :=
  rfl

/--
Definition of `ofUnitHom` / `ofUnitHom` 的定义

English:
definition ofUnitHom
  signature: (f : Rˣ ->* R'ˣ)
  body: by classical exact fun x => if hx : IsUnit x then f hx.unit else 0
  map_one' := by
    have h1 : (isUnit_one.unit : Rˣ) = 1 := Units.ext rfl
    simp only [h1, dif_pos, Units.val_eq_one, map_one, isUnit_one]
  map_mul' := by
    classical
      intro x y
      by_cases hx : IsUnit x
      · simp on

中文:
定义 ofUnitHom
  签名: (f : Rˣ ->* R'ˣ)
  定义体: by classical exact fun x => if hx : IsUnit x then f hx.unit else 0
  map_one' := by
    have h1 : (isUnit_one.unit : Rˣ) = 1 := Units.ext rfl
    simp only [h1, dif_pos, Units.val_eq_one, map_one, isUnit_one]
  map_mul' := by
    classical
      intro x y
      by_cases hx : IsUnit x
      · simp on

Depends on / 依赖: IsUnit, IsUnit.mul_iff, Units.ext, Units.val_eq_one, classical, dif_neg, dif_pos, hx.mul, hx.unit, hy.unit, isUnit_one, isUnit_one.unit, map_mul, map_one, mul_iff, mul_z, not_false_iff, true_and, val_eq_one
-/
noncomputable def ofUnitHom (f : Rˣ ->* R'ˣ) : MulChar R R' where
  toFun := by classical exact fun x => if hx : IsUnit x then f hx.unit else 0
  map_one' := by
    have h1 : (isUnit_one.unit : Rˣ) = 1 := Units.ext rfl
    simp only [h1, dif_pos, Units.val_eq_one, map_one, isUnit_one]
  map_mul' := by
    classical
      intro x y
      by_cases hx : IsUnit x
      · simp only [hx, IsUnit.mul_iff, true_and, dif_pos]
        by_cases hy : IsUnit y
        · simp only [hy, dif_pos]
          have hm : (hx.mul hy).unit = hx.unit * hy.unit := Units.ext rfl
          rw [hm]; rw [map_mul]
          norm_cast
        · simp only [hy, not_false_iff, dif_neg, mul_zero]
      · simp only [hx, IsUnit.mul_iff, false_and, not_false_iff, dif_neg, zero_mul]
  map_nonunit' := by
    intro a ha
    simp only [ha, not_false_iff, dif_neg]

/--
theorem `ofUnitHom_coe` / 定理 `ofUnitHom_coe`

English:
theorem ofUnitHom_coe
  given: (f : Rˣ ->* R'ˣ) (a : Rˣ)
  statement: ofUnitHom f ↑a = f a
  proof: by simp [ofUnitHom]

中文:
定理 ofUnitHom_coe
  条件: (f : Rˣ ->* R'ˣ) (a : Rˣ)
  结论: ofUnitHom f ↑a = f a
  证明: by simp [ofUnitHom]

Depends on / 依赖: ofUnitHom
-/
theorem ofUnitHom_coe (f : Rˣ ->* R'ˣ) (a : Rˣ) : ofUnitHom f ↑a = f a := by simp [ofUnitHom]

/--
Definition of `equivToUnitHom` / `equivToUnitHom` 的定义

English:
definition equivToUnitHom
  signature: : MulChar R R' ≃ (Rˣ ->* R'ˣ) where
  body: toUnitHom
  invFun := ofUnitHom
  left_inv := by
    intro χ
    ext x
    rw [ofUnitHom_coe]; rw [coe_toUnitHom]
  right_inv := by
    intro f
    ext x
    simp only [coe_toUnitHom, ofUnitHom_coe]

@[simp]

中文:
定义 equivToUnitHom
  签名: : MulChar R R' ≃ (Rˣ ->* R'ˣ) where
  定义体: toUnitHom
  invFun := ofUnitHom
  left_inv := by
    intro χ
    ext x
    rw [ofUnitHom_coe]; rw [coe_toUnitHom]
  right_inv := by
    intro f
    ext x
    simp only [coe_toUnitHom, ofUnitHom_coe]

@[simp]

Depends on / 依赖: toUnitHom
-/
noncomputable def equivToUnitHom : MulChar R R' ≃ (Rˣ ->* R'ˣ) where
  toFun := toUnitHom
  invFun := ofUnitHom
  left_inv := by
    intro χ
    ext x
    rw [ofUnitHom_coe]; rw [coe_toUnitHom]
  right_inv := by
    intro f
    ext x
    simp only [coe_toUnitHom, ofUnitHom_coe]

@[simp]
/--
theorem `toUnitHom_eq` / 定理 `toUnitHom_eq`

English:
theorem toUnitHom_eq
  given: (χ : MulChar R R')
  statement: toUnitHom χ = equivToUnitHom χ
  proof: rfl

@[simp]

中文:
定理 toUnitHom_eq
  条件: (χ : MulChar R R')
  结论: toUnitHom χ = equivToUnitHom χ
  证明: rfl

@[simp]
-/
theorem toUnitHom_eq (χ : MulChar R R') : toUnitHom χ = equivToUnitHom χ :=
  rfl

@[simp]
/--
theorem `ofUnitHom_eq` / 定理 `ofUnitHom_eq`

English:
theorem ofUnitHom_eq
  given: (χ : Rˣ ->* R'ˣ)
  statement: ofUnitHom χ = equivToUnitHom.symm χ
  proof: rfl

@[simp]

中文:
定理 ofUnitHom_eq
  条件: (χ : Rˣ ->* R'ˣ)
  结论: ofUnitHom χ = equivToUnitHom.symm χ
  证明: rfl

@[simp]
-/
theorem ofUnitHom_eq (χ : Rˣ ->* R'ˣ) : ofUnitHom χ = equivToUnitHom.symm χ :=
  rfl

@[simp]
/--
theorem `coe_equivToUnitHom` / 定理 `coe_equivToUnitHom`

English:
theorem coe_equivToUnitHom
  given: (χ : MulChar R R') (a : Rˣ)
  statement: ↑(equivToUnitHom χ a) = χ a
  proof: coe_toUnitHom χ a

@[simp]

中文:
定理 coe_equivToUnitHom
  条件: (χ : MulChar R R') (a : Rˣ)
  结论: ↑(equivToUnitHom χ a) = χ a
  证明: coe_toUnitHom χ a

@[simp]

Depends on / 依赖: coe_toUnitHom
-/
theorem coe_equivToUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(equivToUnitHom χ a) = χ a :=
  coe_toUnitHom χ a

@[simp]
/--
theorem `equivToUnitHom_symm_coe` / 定理 `equivToUnitHom_symm_coe`

English:
theorem equivToUnitHom_symm_coe
  given: (f : Rˣ ->* R'ˣ) (a : Rˣ)
  statement: equivToUnitHom.symm f ↑a = f a
  proof: ofUnitHom_coe f a

@[simp]

中文:
定理 equivToUnitHom_symm_coe
  条件: (f : Rˣ ->* R'ˣ) (a : Rˣ)
  结论: equivToUnitHom.symm f ↑a = f a
  证明: ofUnitHom_coe f a

@[simp]

Depends on / 依赖: ofUnitHom_coe
-/
theorem equivToUnitHom_symm_coe (f : Rˣ ->* R'ˣ) (a : Rˣ) : equivToUnitHom.symm f ↑a = f a :=
  ofUnitHom_coe f a

@[simp]
/--
lemma `coe_toMonoidHom` / 引理 `coe_toMonoidHom`

English:
lemma coe_toMonoidHom
  statement: (χ : MulChar R R')
  proof: rfl

中文:
引理 coe_toMonoidHom
  结论: (χ : MulChar R R')
  证明: rfl
-/
lemma coe_toMonoidHom (χ : MulChar R R')
    (x : R) : χ.toMonoidHom x = χ x := rfl

/--
theorem `apply_ne_zero_iff` / 定理 `apply_ne_zero_iff`

English:
theorem apply_ne_zero_iff
  given: [Nontrivial R'] {χ : MulChar R R'} {a : R}
  proof: ⟨by simpa using (map_nonunit χ).mt, fun h => (h.map χ).ne_zero⟩

中文:
定理 apply_ne_zero_iff
  条件: [Nontrivial R'] {χ : MulChar R R'} {a : R}
  证明: ⟨by simpa using (map_nonunit χ).mt, fun h => (h.map χ).ne_zero⟩

Depends on / 依赖: h.map, map_nonunit, ne_zero
-/
theorem apply_ne_zero_iff [Nontrivial R'] {χ : MulChar R R'} {a : R} :
    χ a != 0 ↔ IsUnit a :=
  ⟨by simpa using (map_nonunit χ).mt, fun h => (h.map χ).ne_zero⟩

/--
theorem `apply_eq_zero_iff` / 定理 `apply_eq_zero_iff`

English:
theorem apply_eq_zero_iff
  given: [Nontrivial R'] {χ : MulChar R R'} {a : R}
  proof: by
  simpa using χ.apply_ne_zero_iff.not

中文:
定理 apply_eq_zero_iff
  条件: [Nontrivial R'] {χ : MulChar R R'} {a : R}
  证明: by
  simpa using χ.apply_ne_zero_iff.not

Depends on / 依赖: apply_ne_zero_iff, apply_ne_zero_iff.not
-/
theorem apply_eq_zero_iff [Nontrivial R'] {χ : MulChar R R'} {a : R} :
    χ a = 0 ↔ ¬ IsUnit a := by
  simpa using χ.apply_ne_zero_iff.not



/--
theorem `map_one` / 定理 `map_one`

English:
theorem map_one
  given: (χ : MulChar R R')
  statement: χ (1 : R) = 1
  proof: χ.map_one'

中文:
定理 map_one
  条件: (χ : MulChar R R')
  结论: χ (1 : R) = 1
  证明: χ.map_one'

Depends on / 依赖: P.Rel, trans_of
-/
protected theorem map_one (χ : MulChar R R') : χ (1 : R) = 1 :=
  χ.map_one'

/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R')
  proof: by rw [map_nonunit χ not_isUnit_zero]

中文:
定理 map_zero
  条件: {R : 类型} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R')
  证明: by rw [map_nonunit χ not_isUnit_zero]
-/
protected theorem map_zero {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R') :
    χ (0 : R) = 0 := by rw [map_nonunit χ not_isUnit_zero]

/-- We can convert a multiplicative character into a homomorphism of monoids with zero when
the source has a zero and another element. -/
@[coe, simps]
/--
Definition of `toMonoidWithZeroHom` / `toMonoidWithZeroHom` 的定义

English:
definition toMonoidWithZeroHom
  signature: {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R')
  body: χ.toFun
  map_zero' := χ.map_zero
  map_one' := χ.map_one'
  map_mul' := χ.map_mul'

中文:
定义 toMonoidWithZeroHom
  签名: {R : 类型} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R')
  定义体: χ.toFun
  map_zero' := χ.map_zero
  map_one' := χ.map_one'
  map_mul' := χ.map_mul'
-/
def toMonoidWithZeroHom {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R') :
    R ->*₀ R' where
  toFun := χ.toFun
  map_zero' := χ.map_zero
  map_one' := χ.map_one'
  map_mul' := χ.map_mul'

/--
theorem `map_ringChar` / 定理 `map_ringChar`

English:
theorem map_ringChar
  given: {R : Type*} [CommSemiring R] [Nontrivial R] (χ : MulChar R R')
  proof: by rw [ringChar.Nat.cast_ringChar, χ.map_zero]

中文:
定理 map_ringChar
  条件: {R : 类型} [CommSemiring R] [Nontrivial R] (χ : MulChar R R')
  证明: by rw [ringChar.Nat.cast_ringChar, χ.map_zero]

Depends on / 依赖: cast_ringChar, map_zero, ringChar, ringChar.Nat.cast_ringChar
-/
theorem map_ringChar {R : Type*} [CommSemiring R] [Nontrivial R] (χ : MulChar R R') :
    χ (ringChar R) = 0 := by rw [ringChar.Nat.cast_ringChar, χ.map_zero]

/--
Instance `hasOne` / 实例 `hasOne`

English:
instance hasOne
  signature: : One (MulChar R R')
  body: ⟨trivial R R'⟩

中文:
实例 hasOne
  签名: : One (MulChar R R')
  定义体: ⟨trivial R R'⟩
-/
noncomputable instance hasOne : One (MulChar R R') :=
  ⟨trivial R R'⟩

/--
Instance `inhabited` / 实例 `inhabited`

English:
instance inhabited
  signature: : Inhabited (MulChar R R')
  body: ⟨1⟩

中文:
实例 inhabited
  签名: : Inhabited (MulChar R R')
  定义体: ⟨1⟩
-/
noncomputable instance inhabited : Inhabited (MulChar R R') :=
  ⟨1⟩

/-- Evaluation of the trivial character -/
@[simp]
/--
theorem `one_apply_coe` / 定理 `one_apply_coe`

English:
theorem one_apply_coe
  given: (a : Rˣ)
  statement: (1 : MulChar R R') a = 1
  proof: by exact dif_pos a.isUnit

中文:
定理 one_apply_coe
  条件: (a : Rˣ)
  结论: (1 : MulChar R R') a = 1
  证明: by exact dif_pos a.isUnit

Depends on / 依赖: a.isUnit, dif_pos, isUnit
-/
theorem one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1 := by exact dif_pos a.isUnit

/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: {x : R} (hx : IsUnit x)
  statement: (1 : MulChar R R') x = 1
  proof: one_apply_coe hx.unit

中文:
引理 one_apply
  条件: {x : R} (hx : IsUnit x)
  结论: (1 : MulChar R R') x = 1
  证明: one_apply_coe hx.unit

Depends on / 依赖: hx.unit, one_apply_coe
-/
lemma one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R') x = 1 := one_apply_coe hx.unit

/--
Definition of `mul` / `mul` 的定义

English:
definition mul
  signature: (χ χ' : MulChar R R')
  body: { χ.toMonoidHom * χ'.toMonoidHom with
    toFun := χ * χ'
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, zero_mul, Pi.mul_apply] }

中文:
定义 mul
  签名: (χ χ' : MulChar R R')
  定义体: { χ.toMonoidHom * χ'.toMonoidHom with
    toFun := χ * χ'
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, zero_mul, Pi.mul_apply] }

Depends on / 依赖: Pi.mul_apply, map_nonunit, mul_apply, toMonoidHom, zero_mul
-/
def mul (χ χ' : MulChar R R') : MulChar R R' :=
  { χ.toMonoidHom * χ'.toMonoidHom with
    toFun := χ * χ'
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, zero_mul, Pi.mul_apply] }

/--
Instance `hasMul` / 实例 `hasMul`

English:
instance hasMul
  signature: : Mul (MulChar R R')
  body: ⟨mul⟩

中文:
实例 hasMul
  签名: : Mul (MulChar R R')
  定义体: ⟨mul⟩
-/
instance hasMul : Mul (MulChar R R') :=
  ⟨mul⟩

/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (χ χ' : MulChar R R') (a : R)
  statement: (χ * χ') a = χ a * χ' a
  proof: rfl

@[simp]

中文:
定理 mul_apply
  条件: (χ χ' : MulChar R R') (a : R)
  结论: (χ * χ') a = χ a * χ' a
  证明: rfl

@[simp]
-/
theorem mul_apply (χ χ' : MulChar R R') (a : R) : (χ * χ') a = χ a * χ' a :=
  rfl

@[simp]
/--
theorem `coeToFun_mul` / 定理 `coeToFun_mul`

English:
theorem coeToFun_mul
  given: (χ χ' : MulChar R R')
  statement: ⇑(χ * χ') = χ * χ'
  proof: rfl

中文:
定理 coeToFun_mul
  条件: (χ χ' : MulChar R R')
  结论: ⇑(χ * χ') = χ * χ'
  证明: rfl
-/
theorem coeToFun_mul (χ χ' : MulChar R R') : ⇑(χ * χ') = χ * χ' :=
  rfl

/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  given: (χ : MulChar R R')
  statement: (1 : MulChar R R') * χ = χ
  proof: by
  ext
  simp only [one_mul, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]

中文:
定理 one_mul
  条件: (χ : MulChar R R')
  结论: (1 : MulChar R R') * χ = χ
  证明: by
  ext
  simp only [one_mul, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]
-/
protected theorem one_mul (χ : MulChar R R') : (1 : MulChar R R') * χ = χ := by
  ext
  simp only [one_mul, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]

/--
theorem `mul_one` / 定理 `mul_one`

English:
theorem mul_one
  given: (χ : MulChar R R')
  statement: χ * 1 = χ
  proof: by
  ext
  simp only [mul_one, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]

中文:
定理 mul_one
  条件: (χ : MulChar R R')
  结论: χ * 1 = χ
  证明: by
  ext
  simp only [mul_one, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]
-/
protected theorem mul_one (χ : MulChar R R') : χ * 1 = χ := by
  ext
  simp only [mul_one, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]

/--
Definition of `inv` / `inv` 的定义

English:
definition inv
  signature: (χ : MulChar R R')
  body: { MonoidWithZero.inverse.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => MonoidWithZero.inverse (χ a)
    map_nonunit' := fun a ha => by simp [map_nonunit _ ha] }

中文:
定义 inv
  签名: (χ : MulChar R R')
  定义体: { MonoidWithZero.inverse.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => MonoidWithZero.inverse (χ a)
    map_nonunit' := fun a ha => by simp [map_nonunit _ ha] }

Depends on / 依赖: MonoidWithZero, MonoidWithZero.inverse, MonoidWithZero.inverse.toMonoidHom.comp, inverse, map_nonunit, toMonoidHom
-/
noncomputable def inv (χ : MulChar R R') : MulChar R R' :=
  { MonoidWithZero.inverse.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => MonoidWithZero.inverse (χ a)
    map_nonunit' := fun a ha => by simp [map_nonunit _ ha] }

/--
Instance `hasInv` / 实例 `hasInv`

English:
instance hasInv
  signature: : Inv (MulChar R R')
  body: ⟨inv⟩

中文:
实例 hasInv
  签名: : Inv (MulChar R R')
  定义体: ⟨inv⟩
-/
noncomputable instance hasInv : Inv (MulChar R R') :=
  ⟨inv⟩

/--
theorem `inv_apply_eq_inv` / 定理 `inv_apply_eq_inv`

English:
theorem inv_apply_eq_inv
  given: (χ : MulChar R R') (a : R)
  statement: χ⁻¹ a = (χ a)⁻¹ʳ
  proof: Eq.refl inv χ a

中文:
定理 inv_apply_eq_inv
  条件: (χ : MulChar R R') (a : R)
  结论: χ⁻¹ a = (χ a)⁻¹ʳ
  证明: Eq.refl inv χ a

Depends on / 依赖: Eq.refl
-/
theorem inv_apply_eq_inv (χ : MulChar R R') (a : R) : χ⁻¹ a = (χ a)⁻¹ʳ :=
Eq.refl inv χ a

/--
theorem `inv_apply_eq_inv'` / 定理 `inv_apply_eq_inv'`

English:
theorem inv_apply_eq_inv'
  given: {R' : Type*} [CommGroupWithZero R'] (χ : MulChar R R') (a : R)
  proof: (inv_apply_eq_inv χ a).trans Ring.inverse_eq_inv (χ a)

中文:
定理 inv_apply_eq_inv'
  条件: {R' : 类型} [CommGroupWithZero R'] (χ : MulChar R R') (a : R)
  证明: (inv_apply_eq_inv χ a).trans Ring.inverse_eq_inv (χ a)

Depends on / 依赖: Ring.inverse_eq_inv, inv_apply_eq_inv, inverse_eq_inv
-/
theorem inv_apply_eq_inv' {R' : Type*} [CommGroupWithZero R'] (χ : MulChar R R') (a : R) :
    χ⁻¹ a = (χ a)⁻¹ :=
(inv_apply_eq_inv χ a).trans Ring.inverse_eq_inv (χ a)

/--
theorem `inv_apply` / 定理 `inv_apply`

English:
theorem inv_apply
  given: {R : Type*} [CommMonoidWithZero R] (χ : MulChar R R') (a : R)
  proof: by
  by_cases ha : IsUnit a
  · rw [inv_apply_eq_inv]
    have h := IsUnit.map χ ha
    apply_fun (χ a * ·) using IsUnit.mul_right_injective h
    dsimp only
    rw [Ring.mul_inverse_cancel _ h]; rw [← map_mul]; rw [Ring.mul_inverse_cancel _ ha]; rw [map_one]
  · revert ha
    nontriviality R
    in

中文:
定理 inv_apply
  条件: {R : 类型} [CommMonoidWithZero R] (χ : MulChar R R') (a : R)
  证明: by
  by_cases ha : IsUnit a
  · rw [inv_apply_eq_inv]
    have h := IsUnit.map χ ha
    apply_fun (χ a * ·) using IsUnit.mul_right_injective h
    dsimp only
    rw [Ring.mul_inverse_cancel _ h]; rw [← map_mul]; rw [Ring.mul_inverse_cancel _ ha]; rw [map_one]
  · revert ha
    nontriviality R
    in

Depends on / 依赖: IsUnit, IsUnit.map, IsUnit.mul_right_injective, Ring.mul_inverse_cancel, apply_fun, inv_apply_eq_inv, map_mul, map_one, mul_inverse_cancel, mul_right_injective, nontriviality, revert
-/
theorem inv_apply {R : Type*} [CommMonoidWithZero R] (χ : MulChar R R') (a : R) :
    χ⁻¹ a = χ a⁻¹ʳ := by
  by_cases ha : IsUnit a
  · rw [inv_apply_eq_inv]
    have h := IsUnit.map χ ha
    apply_fun (χ a * ·) using IsUnit.mul_right_injective h
    dsimp only
    rw [Ring.mul_inverse_cancel _ h]; rw [← map_mul]; rw [Ring.mul_inverse_cancel _ ha]; rw [map_one]
  · revert ha
    nontriviality R
    intro ha
    -- `nontriviality R` by itself doesn't do it
    rw [map_nonunit _ ha]; rw [Ring.inverse_non_unit a ha]; rw [MulChar.map_zero χ]

/--
theorem `inv_apply'` / 定理 `inv_apply'`

English:
theorem inv_apply'
  given: {R : Type*} [CommGroupWithZero R] (χ : MulChar R R') (a : R)
  statement: χ⁻¹ a = χ a⁻¹
  proof: (inv_apply χ a).trans congr_arg _ (Ring.inverse_eq_inv a)

中文:
定理 inv_apply'
  条件: {R : 类型} [CommGroupWithZero R] (χ : MulChar R R') (a : R)
  结论: χ⁻¹ a = χ a⁻¹
  证明: (inv_apply χ a).trans congr_arg _ (Ring.inverse_eq_inv a)

Depends on / 依赖: Ring.inverse_eq_inv, congr_arg, inv_apply, inverse_eq_inv
-/
theorem inv_apply' {R : Type*} [CommGroupWithZero R] (χ : MulChar R R') (a : R) : χ⁻¹ a = χ a⁻¹ :=
(inv_apply χ a).trans congr_arg _ (Ring.inverse_eq_inv a)

/--
theorem `inv_mul` / 定理 `inv_mul`

English:
theorem inv_mul
  given: (χ : MulChar R R')
  statement: χ⁻¹ * χ = 1
  proof: by
  ext x
  rw [coeToFun_mul]; rw [Pi.mul_apply]; rw [inv_apply_eq_inv]
  simp only [Ring.inverse_mul_cancel _ (IsUnit.map χ x.isUnit)]
  rw [one_apply_coe]

中文:
定理 inv_mul
  条件: (χ : MulChar R R')
  结论: χ⁻¹ * χ = 1
  证明: by
  ext x
  rw [coeToFun_mul]; rw [Pi.mul_apply]; rw [inv_apply_eq_inv]
  simp only [Ring.inverse_mul_cancel _ (IsUnit.map χ x.isUnit)]
  rw [one_apply_coe]

Depends on / 依赖: IsUnit, IsUnit.map, Pi.mul_apply, Ring.inverse_mul_cancel, coeToFun_mul, inv_apply_eq_inv, inverse_mul_cancel, isUnit, mul_apply, one_apply_coe, x.isUnit
-/
theorem inv_mul (χ : MulChar R R') : χ⁻¹ * χ = 1 := by
  ext x
  rw [coeToFun_mul]; rw [Pi.mul_apply]; rw [inv_apply_eq_inv]
  simp only [Ring.inverse_mul_cancel _ (IsUnit.map χ x.isUnit)]
  rw [one_apply_coe]

/--
Instance `commGroup` / 实例 `commGroup`

English:
instance commGroup
  signature: : CommGroup (MulChar R R') where
  body: inv_mul
  mul_assoc := by
    intro χ₁ χ₂ χ₃
    ext a
    simp only [mul_assoc, Pi.mul_apply, MulChar.coeToFun_mul]
  mul_comm := by
    intro χ₁ χ₂
    ext a
    simp only [mul_comm, Pi.mul_apply, MulChar.coeToFun_mul]
  one_mul := MulChar.one_mul
  mul_one := MulChar.mul_one

中文:
实例 commGroup
  签名: : CommGroup (MulChar R R') where
  定义体: inv_mul
  mul_assoc := by
    intro χ₁ χ₂ χ₃
    ext a
    simp only [mul_assoc, Pi.mul_apply, MulChar.coeToFun_mul]
  mul_comm := by
    intro χ₁ χ₂
    ext a
    simp only [mul_comm, Pi.mul_apply, MulChar.coeToFun_mul]
  one_mul := MulChar.one_mul
  mul_one := MulChar.mul_one

Depends on / 依赖: inv_mul
-/
noncomputable instance commGroup : CommGroup (MulChar R R') where
  inv_mul_cancel := inv_mul
  mul_assoc := by
    intro χ₁ χ₂ χ₃
    ext a
    simp only [mul_assoc, Pi.mul_apply, MulChar.coeToFun_mul]
  mul_comm := by
    intro χ₁ χ₂
    ext a
    simp only [mul_comm, Pi.mul_apply, MulChar.coeToFun_mul]
  one_mul := MulChar.one_mul
  mul_one := MulChar.mul_one

/--
theorem `pow_apply_coe` / 定理 `pow_apply_coe`

English:
theorem pow_apply_coe
  given: (χ : MulChar R R') (n : Nat) (a : Rˣ)
  statement: (χ ^ n) a = χ a ^ n
  proof: by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_apply_coe]
  | succ n ih => rw [pow_succ, pow_succ, mul_apply, ih]

中文:
定理 pow_apply_coe
  条件: (χ : MulChar R R') (n : 自然数) (a : Rˣ)
  结论: (χ ^ n) a = χ a ^ n
  证明: by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_apply_coe]
  | succ n ih => rw [pow_succ, pow_succ, mul_apply, ih]

Depends on / 依赖: mul_apply, one_apply_coe, pow_succ, pow_zero
-/
theorem pow_apply_coe (χ : MulChar R R') (n : Nat) (a : Rˣ) : (χ ^ n) a = χ a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_apply_coe]
  | succ n ih => rw [pow_succ, pow_succ, mul_apply, ih]

/--
theorem `pow_apply'` / 定理 `pow_apply'`

English:
theorem pow_apply'
  given: (χ : MulChar R R') {n : Nat} (hn : n != 0) (a : R)
  statement: (χ ^ n) a = χ a ^ n
  proof: by
  by_cases ha : IsUnit a
  · exact pow_apply_coe χ n ha.unit
  · rw [map_nonunit (χ ^ n) ha, map_nonunit χ ha, zero_pow hn]

中文:
定理 pow_apply'
  条件: (χ : MulChar R R') {n : 自然数} (hn : n != 0) (a : R)
  结论: (χ ^ n) a = χ a ^ n
  证明: by
  by_cases ha : IsUnit a
  · exact pow_apply_coe χ n ha.unit
  · rw [map_nonunit (χ ^ n) ha, map_nonunit χ ha, zero_pow hn]

Depends on / 依赖: IsUnit, ha.unit, map_nonunit, pow_apply_coe, zero_pow
-/
theorem pow_apply' (χ : MulChar R R') {n : Nat} (hn : n != 0) (a : R) : (χ ^ n) a = χ a ^ n := by
  by_cases ha : IsUnit a
  · exact pow_apply_coe χ n ha.unit
  · rw [map_nonunit (χ ^ n) ha, map_nonunit χ ha, zero_pow hn]

/--
lemma `equivToUnitHom_mul_apply` / 引理 `equivToUnitHom_mul_apply`

English:
lemma equivToUnitHom_mul_apply
  given: (χ₁ χ₂ : MulChar R R') (a : Rˣ)
  proof: by
  apply_fun ((↑) : R'ˣ -> R') using Units.val_injective
  push_cast
  simp_rw [coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply]

中文:
引理 equivToUnitHom_mul_apply
  条件: (χ₁ χ₂ : MulChar R R') (a : Rˣ)
  证明: by
  apply_fun ((↑) : R'ˣ -> R') using Units.val_injective
  push_cast
  simp_rw [coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply]

Depends on / 依赖: Pi.mul_apply, Units.val_injective, apply_fun, coeToFun_mul, coe_equivToUnitHom, mul_apply, simp_rw, val_injective
-/
lemma equivToUnitHom_mul_apply (χ₁ χ₂ : MulChar R R') (a : Rˣ) :
    equivToUnitHom (χ₁ * χ₂) a = equivToUnitHom χ₁ a * equivToUnitHom χ₂ a := by
  apply_fun ((↑) : R'ˣ -> R') using Units.val_injective
  push_cast
  simp_rw [coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply]

/-- The equivalence between multiplicative characters and homomorphisms of unit groups
as a multiplicative equivalence. -/
@[simps! apply symm_apply]
/--
Definition of `mulEquivToUnitHom` / `mulEquivToUnitHom` 的定义

English:
definition mulEquivToUnitHom
  signature: : MulChar R R' ≃* (Rˣ ->* R'ˣ)
  body: { equivToUnitHom with
    map_mul' := by
      intro χ ψ
      ext
      simp only [Equiv.toFun_as_coe, coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply,
        MonoidHom.mul_apply, Units.val_mul]
  }

中文:
定义 mulEquivToUnitHom
  签名: : MulChar R R' ≃* (Rˣ ->* R'ˣ)
  定义体: { equivToUnitHom with
    map_mul' := by
      intro χ ψ
      ext
      simp only [Equiv.toFun_as_coe, coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply,
        MonoidHom.mul_apply, Units.val_mul]
  }

Depends on / 依赖: Equiv.toFun_as_coe, MonoidHom, MonoidHom.mul_apply, Pi.mul_apply, Units.val_mul, coeToFun_mul, coe_equivToUnitHom, equivToUnitHom, map_mul, mul_apply, toFun_as_coe, val_mul
-/
noncomputable def mulEquivToUnitHom : MulChar R R' ≃* (Rˣ ->* R'ˣ) :=
  { equivToUnitHom with
    map_mul' := by
      intro χ ψ
      ext
      simp only [Equiv.toFun_as_coe, coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply,
        MonoidHom.mul_apply, Units.val_mul]
  }

/--
The restriction of a `MulChar` to a submonoid.
-/
@[simps! apply]
/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S)
  body: ofUnitHom χ.toUnitHom.comp Units.map (SubmonoidClass.subtype T)

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply

中文:
定义 domRestrict
  签名: {S : 类型} [SetLike S R] [SubmonoidClass S R] (T : S)
  定义体: ofUnitHom χ.toUnitHom.comp Units.map (SubmonoidClass.subtype T)

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply

Depends on / 依赖: SubmonoidClass, SubmonoidClass.subtype, Units.map, ofUnitHom, subtype, toUnitHom, toUnitHom.comp
-/
noncomputable def domRestrict {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S)
    (χ : MulChar R R') : MulChar T R' :=
ofUnitHom χ.toUnitHom.comp Units.map (SubmonoidClass.subtype T)

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply

/--
The restriction of a `MulChar` to a submonoid as an homomorphism.
-/
@[simps]
/--
Definition of `domRestrictHom` / `domRestrictHom` 的定义

English:
definition domRestrictHom
  signature: {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S)
  body: domRestrict T
  map_one' := by
    ext x
    rw [domRestrict_apply]; rw [if_pos x.isUnit]; rw [MulChar.one_apply x.isUnit.coe]; rw [one_apply_coe]
  map_mul' x y := by ext; simp

@[deprecated (since := "2026-07-19")] alias restrictHom := domRestrictHom
@[deprecated (since := "2026-07-19")] alias res

中文:
定义 domRestrictHom
  签名: {S : 类型} [SetLike S R] [SubmonoidClass S R] (T : S)
  定义体: domRestrict T
  map_one' := by
    ext x
    rw [domRestrict_apply]; rw [if_pos x.isUnit]; rw [MulChar.one_apply x.isUnit.coe]; rw [one_apply_coe]
  map_mul' x y := by ext; simp

@[deprecated (since := "2026-07-19")] alias restrictHom := domRestrictHom
@[deprecated (since := "2026-07-19")] alias res

Depends on / 依赖: domRestrict
-/
noncomputable def domRestrictHom {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S)
    (R'' : Type*) [CommMonoidWithZero R''] :
    (MulChar R R'') ->* MulChar T R'' where
  toFun := domRestrict T
  map_one' := by
    ext x
    rw [domRestrict_apply]; rw [if_pos x.isUnit]; rw [MulChar.one_apply x.isUnit.coe]; rw [one_apply_coe]
  map_mul' x y := by ext; simp

@[deprecated (since := "2026-07-19")] alias restrictHom := domRestrictHom
@[deprecated (since := "2026-07-19")] alias restrictHom_apply := domRestrictHom_apply

end Group

/-!
### Properties of multiplicative characters

We introduce the properties of being nontrivial or quadratic and prove
some basic facts about them.

We now (mostly) assume that the target is a commutative ring.
-/


section Properties

section nontrivial

variable {R : Type*} [CommMonoid R] {R' : Type*} [CommMonoidWithZero R']

/--
lemma `eq_one_iff` / 引理 `eq_one_iff`

English:
lemma eq_one_iff
  given: {χ : MulChar R R'}
  statement: χ = 1 ↔ forall a : Rˣ, χ a = 1
  proof: by
  simp only [MulChar.ext_iff, one_apply_coe]

中文:
引理 eq_one_iff
  条件: {χ : MulChar R R'}
  结论: χ = 1 ↔ 对任意 a : Rˣ, χ a = 1
  证明: by
  simp only [MulChar.ext_iff, one_apply_coe]

Depends on / 依赖: MulChar, MulChar.ext_iff, ext_iff, one_apply_coe
-/
lemma eq_one_iff {χ : MulChar R R'} : χ = 1 ↔ forall a : Rˣ, χ a = 1 := by
  simp only [MulChar.ext_iff, one_apply_coe]

/--
lemma `ne_one_iff` / 引理 `ne_one_iff`

English:
lemma ne_one_iff
  given: {χ : MulChar R R'}
  statement: χ != 1 ↔ exists a : Rˣ, χ a != 1
  proof: by
  simp only [Ne, eq_one_iff, not_forall]

中文:
引理 ne_one_iff
  条件: {χ : MulChar R R'}
  结论: χ != 1 ↔ 存在 a : Rˣ, χ a != 1
  证明: by
  simp only [Ne, eq_one_iff, not_forall]

Depends on / 依赖: eq_one_iff, not_forall
-/
lemma ne_one_iff {χ : MulChar R R'} : χ != 1 ↔ exists a : Rˣ, χ a != 1 := by
  simp only [Ne, eq_one_iff, not_forall]

/--
theorem `domRestrict_eq_one_iff` / 定理 `domRestrict_eq_one_iff`

English:
theorem domRestrict_eq_one_iff
  statement: {S : Type*} [SetLike S R] [SubmonoidClass S R] {T : S}
  proof: by
  simp [eq_one_iff]

@[deprecated (since := "2026-07-19")] alias restrict_eq_one_iff := domRestrict_eq_one_iff

中文:
定理 domRestrict_eq_one_iff
  结论: {S : 类型} [SetLike S R] [SubmonoidClass S R] {T : S}
  证明: by
  simp [eq_one_iff]

@[deprecated (since := "2026-07-19")] alias restrict_eq_one_iff := domRestrict_eq_one_iff

Depends on / 依赖: eq_one_iff
-/
theorem domRestrict_eq_one_iff {S : Type*} [SetLike S R] [SubmonoidClass S R] {T : S}
    {χ : MulChar R R'} : χ.domRestrict T = 1 ↔ forall x : Tˣ, χ x = 1 := by
  simp [eq_one_iff]

@[deprecated (since := "2026-07-19")] alias restrict_eq_one_iff := domRestrict_eq_one_iff

end nontrivial

section quadratic_and_comp

variable {R : Type*} [CommMonoid R] {R' : Type*} [CommRing R'] {R'' : Type*} [CommRing R'']

/--
Definition of `IsQuadratic` / `IsQuadratic` 的定义

English:
definition IsQuadratic
  signature: (χ : MulChar R R')
  body: forall a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1

中文:
定义 IsQuadratic
  签名: (χ : MulChar R R')
  定义体: forall a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1
-/
def IsQuadratic (χ : MulChar R R') : Prop :=
  forall a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1

/--
theorem `IsQuadratic.eq_of_eq_coe` / 定理 `IsQuadratic.eq_of_eq_coe`

English:
theorem IsQuadratic.eq_of_eq_coe
  statement: {χ : MulChar R Int} (hχ : IsQuadratic χ) {χ' : MulChar R' Int}
  proof: Int.cast_injOn_of_ringChar_ne_two hR'' (hχ a) (hχ' a') h

中文:
定理 IsQuadratic.eq_of_eq_coe
  结论: {χ : MulChar R 整数} (hχ : IsQuadratic χ) {χ' : MulChar R' 整数}
  证明: Int.cast_injOn_of_ringChar_ne_two hR'' (hχ a) (hχ' a') h

Depends on / 依赖: Int.cast_injOn_of_ringChar_ne_two, cast_injOn_of_ringChar_ne_two
-/
theorem IsQuadratic.eq_of_eq_coe {χ : MulChar R Int} (hχ : IsQuadratic χ) {χ' : MulChar R' Int}
    (hχ' : IsQuadratic χ') [Nontrivial R''] (hR'' : ringChar R'' != 2) {a : R} {a' : R'}
    (h : (χ a : R'') = χ' a') : χ a = χ' a' :=
  Int.cast_injOn_of_ringChar_ne_two hR'' (hχ a) (hχ' a') h

/-- We can post-compose a multiplicative character with a ring homomorphism. -/
@[simps]
/--
Definition of `ringHomComp` / `ringHomComp` 的定义

English:
definition ringHomComp
  signature: (χ : MulChar R R') (f : R' ->+* R'')
  body: { f.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => f (χ a)
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, map_zero] }

@[simp]

中文:
定义 ringHomComp
  签名: (χ : MulChar R R') (f : R' ->+* R'')
  定义体: { f.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => f (χ a)
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, map_zero] }

@[simp]

Depends on / 依赖: f.toMonoidHom.comp, map_nonunit, map_zero, toMonoidHom
-/
def ringHomComp (χ : MulChar R R') (f : R' ->+* R'') : MulChar R R'' :=
  { f.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => f (χ a)
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, map_zero] }

@[simp]
/--
lemma `ringHomComp_one` / 引理 `ringHomComp_one`

English:
lemma ringHomComp_one
  given: (f : R' ->+* R'')
  statement: (1 : MulChar R R').ringHomComp f = 1
  proof: by
  ext1
  simp only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one]

中文:
引理 ringHomComp_one
  条件: (f : R' ->+* R'')
  结论: (1 : MulChar R R').ringHomComp f = 1
  证明: by
  ext1
  simp only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one]

Depends on / 依赖: MulChar, MulChar.one_apply_coe, MulChar.ringHomComp_apply, map_one, one_apply_coe, ringHomComp_apply
-/
lemma ringHomComp_one (f : R' ->+* R'') : (1 : MulChar R R').ringHomComp f = 1 := by
  ext1
  simp only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one]

/--
lemma `ringHomComp_inv` / 引理 `ringHomComp_inv`

English:
lemma ringHomComp_inv
  given: {R : Type*} [CommMonoidWithZero R] (χ : MulChar R R') (f : R' ->+* R'')
  proof: by
  ext1
  simp only [inv_apply, Ring.inverse_unit, ringHomComp_apply]

中文:
引理 ringHomComp_inv
  条件: {R : 类型} [CommMonoidWithZero R] (χ : MulChar R R') (f : R' ->+* R'')
  证明: by
  ext1
  simp only [inv_apply, Ring.inverse_unit, ringHomComp_apply]

Depends on / 依赖: Ring.inverse_unit, inv_apply, inverse_unit, ringHomComp_apply
-/
lemma ringHomComp_inv {R : Type*} [CommMonoidWithZero R] (χ : MulChar R R') (f : R' ->+* R'') :
    (χ.ringHomComp f)⁻¹ = χ⁻¹.ringHomComp f := by
  ext1
  simp only [inv_apply, Ring.inverse_unit, ringHomComp_apply]

/--
lemma `ringHomComp_mul` / 引理 `ringHomComp_mul`

English:
lemma ringHomComp_mul
  given: (χ φ : MulChar R R') (f : R' ->+* R'')
  proof: by
  ext1
  simp only [ringHomComp_apply, coeToFun_mul, Pi.mul_apply, map_mul]

中文:
引理 ringHomComp_mul
  条件: (χ φ : MulChar R R') (f : R' ->+* R'')
  证明: by
  ext1
  simp only [ringHomComp_apply, coeToFun_mul, Pi.mul_apply, map_mul]

Depends on / 依赖: Pi.mul_apply, coeToFun_mul, map_mul, mul_apply, ringHomComp_apply
-/
lemma ringHomComp_mul (χ φ : MulChar R R') (f : R' ->+* R'') :
    (χ * φ).ringHomComp f = χ.ringHomComp f * φ.ringHomComp f := by
  ext1
  simp only [ringHomComp_apply, coeToFun_mul, Pi.mul_apply, map_mul]

/--
lemma `ringHomComp_pow` / 引理 `ringHomComp_pow`

English:
lemma ringHomComp_pow
  given: (χ : MulChar R R') (f : R' ->+* R'') (n : Nat)
  proof: by
  induction n with
  | zero => simp only [pow_zero, ringHomComp_one]
  | succ n ih => simp only [pow_succ, ih, ringHomComp_mul]

中文:
引理 ringHomComp_pow
  条件: (χ : MulChar R R') (f : R' ->+* R'') (n : 自然数)
  证明: by
  induction n with
  | zero => simp only [pow_zero, ringHomComp_one]
  | succ n ih => simp only [pow_succ, ih, ringHomComp_mul]

Depends on / 依赖: pow_succ, pow_zero, ringHomComp_mul, ringHomComp_one
-/
lemma ringHomComp_pow (χ : MulChar R R') (f : R' ->+* R'') (n : Nat) :
    χ.ringHomComp f ^ n = (χ ^ n).ringHomComp f := by
  induction n with
  | zero => simp only [pow_zero, ringHomComp_one]
  | succ n ih => simp only [pow_succ, ih, ringHomComp_mul]

/-- Bundled version of `MulChar.ringHomComp` as a `MonoidHom`. -/
@[simps]
/--
Definition of `ringHomCompHom` / `ringHomCompHom` 的定义

English:
definition ringHomCompHom
  signature: (f : R' ->+* R'')
  body: χ.ringHomComp f
  map_one' := ringHomComp_one f
  map_mul' _ _ := ringHomComp_mul _ _ f

中文:
定义 ringHomCompHom
  签名: (f : R' ->+* R'')
  定义体: χ.ringHomComp f
  map_one' := ringHomComp_one f
  map_mul' _ _ := ringHomComp_mul _ _ f

Depends on / 依赖: ringHomComp
-/
def ringHomCompHom (f : R' ->+* R'') : MulChar R R' ->* MulChar R R'' where
  toFun χ := χ.ringHomComp f
  map_one' := ringHomComp_one f
  map_mul' _ _ := ringHomComp_mul _ _ f

/--
lemma `ringHomComp_zpow` / 引理 `ringHomComp_zpow`

English:
lemma ringHomComp_zpow
  given: (χ : MulChar R R') (f : R' ->+* R'') (n : Int)
  proof: ((ringHomCompHom f).map_zpow χ n).symm

中文:
引理 ringHomComp_zpow
  条件: (χ : MulChar R R') (f : R' ->+* R'') (n : 整数)
  证明: ((ringHomCompHom f).map_zpow χ n).symm

Depends on / 依赖: map_zpow, ringHomCompHom
-/
lemma ringHomComp_zpow (χ : MulChar R R') (f : R' ->+* R'') (n : Int) :
    χ.ringHomComp f ^ n = (χ ^ n).ringHomComp f :=
  ((ringHomCompHom f).map_zpow χ n).symm

/--
theorem `zpow_apply_coe` / 定理 `zpow_apply_coe`

English:
theorem zpow_apply_coe
  statement: {R : Type*} [CommGroupWithZero R] {R' : Type*} [CommRing R']
  proof: by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp [pow_apply_coe]
  · simp [pow_apply_coe, inv_apply', ← inv_pow]

中文:
定理 zpow_apply_coe
  结论: {R : 类型} [CommGroupWithZero R] {R' : 类型} [CommRing R']
  证明: by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp [pow_apply_coe]
  · simp [pow_apply_coe, inv_apply', ← inv_pow]

Depends on / 依赖: Int.eq_nat_or_neg, eq_nat_or_neg, inv_apply, inv_pow, pow_apply_coe
-/
theorem zpow_apply_coe {R : Type*} [CommGroupWithZero R] {R' : Type*} [CommRing R']
    (χ : MulChar R R') (n : Int) (a : Rˣ) : (χ ^ n) a = χ (a ^ n : Rˣ) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp [pow_apply_coe]
  · simp [pow_apply_coe, inv_apply', ← inv_pow]

/--
lemma `injective_ringHomComp` / 引理 `injective_ringHomComp`

English:
lemma injective_ringHomComp
  given: {f : R' ->+* R''} (hf : Function.Injective f)
  proof: by
  simpa
    only [Function.Injective, MulChar.ext_iff, ringHomComp, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    using fun χ χ' h a => hf (h a)

中文:
引理 injective_ringHomComp
  条件: {f : R' ->+* R''} (hf : Function.Injective f)
  证明: by
  simpa
    only [Function.Injective, MulChar.ext_iff, ringHomComp, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    using fun χ χ' h a => hf (h a)

Depends on / 依赖: Function, Function.Injective, Injective, MonoidHom, MonoidHom.coe_mk, MulChar, MulChar.ext_iff, OneHom, OneHom.coe_mk, coe_mk, ext_iff, ringHomComp
-/
lemma injective_ringHomComp {f : R' ->+* R''} (hf : Function.Injective f) :
    Function.Injective (ringHomComp (R := R) · f) := by
  simpa
    only [Function.Injective, MulChar.ext_iff, ringHomComp, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    using fun χ χ' h a => hf (h a)

/--
lemma `ringHomComp_eq_one_iff` / 引理 `ringHomComp_eq_one_iff`

English:
lemma ringHomComp_eq_one_iff
  given: {f : R' ->+* R''} (hf : Function.Injective f) {χ : MulChar R R'}
  proof: by
  conv_lhs => rw [← (show (1 : MulChar R R').ringHomComp f = 1 by simp)]
  exact (injective_ringHomComp hf).eq_iff

中文:
引理 ringHomComp_eq_one_iff
  条件: {f : R' ->+* R''} (hf : Function.Injective f) {χ : MulChar R R'}
  证明: by
  conv_lhs => rw [← (show (1 : MulChar R R').ringHomComp f = 1 by simp)]
  exact (injective_ringHomComp hf).eq_iff

Depends on / 依赖: MulChar, conv_lhs, eq_iff, injective_ringHomComp, ringHomComp
-/
lemma ringHomComp_eq_one_iff {f : R' ->+* R''} (hf : Function.Injective f) {χ : MulChar R R'} :
    χ.ringHomComp f = 1 ↔ χ = 1 := by
  conv_lhs => rw [← (show (1 : MulChar R R').ringHomComp f = 1 by simp)]
  exact (injective_ringHomComp hf).eq_iff

/--
lemma `ringHomComp_ne_one_iff` / 引理 `ringHomComp_ne_one_iff`

English:
lemma ringHomComp_ne_one_iff
  given: {f : R' ->+* R''} (hf : Function.Injective f) {χ : MulChar R R'}
  proof: (ringHomComp_eq_one_iff hf).not

中文:
引理 ringHomComp_ne_one_iff
  条件: {f : R' ->+* R''} (hf : Function.Injective f) {χ : MulChar R R'}
  证明: (ringHomComp_eq_one_iff hf).not

Depends on / 依赖: ringHomComp_eq_one_iff
-/
lemma ringHomComp_ne_one_iff {f : R' ->+* R''} (hf : Function.Injective f) {χ : MulChar R R'} :
    χ.ringHomComp f != 1 ↔ χ != 1 :=
  (ringHomComp_eq_one_iff hf).not

/--
theorem `IsQuadratic.comp` / 定理 `IsQuadratic.comp`

English:
theorem IsQuadratic.comp
  given: {χ : MulChar R R'} (hχ : χ.IsQuadratic) (f : R' ->+* R'')
  proof: by
  intro a
  rcases hχ a with (ha | ha | ha) <;> simp [ha]

中文:
定理 IsQuadratic.comp
  条件: {χ : MulChar R R'} (hχ : χ.IsQuadratic) (f : R' ->+* R'')
  证明: by
  intro a
  rcases hχ a with (ha | ha | ha) <;> simp [ha]
-/
theorem IsQuadratic.comp {χ : MulChar R R'} (hχ : χ.IsQuadratic) (f : R' ->+* R'') :
    (χ.ringHomComp f).IsQuadratic := by
  intro a
  rcases hχ a with (ha | ha | ha) <;> simp [ha]

/--
theorem `IsQuadratic.inv` / 定理 `IsQuadratic.inv`

English:
theorem IsQuadratic.inv
  given: {χ : MulChar R R'} (hχ : χ.IsQuadratic)
  statement: χ⁻¹ = χ
  proof: by
  ext x
  rw [inv_apply_eq_inv]
  rcases hχ x with (h₀ | h₁ | h₂)
  · rw [h₀, Ring.inverse_zero]
  · rw [h₁, Ring.inverse_one]
  · -- Porting note (#11573): was `by norm_cast`
    have : (-1 : R') = (-1 : R'ˣ) := by norm_cast; simp
    rw [h₂]; rw [this]; rw [Ring.inverse_unit (-1 : R'ˣ)]; rw [in

中文:
定理 IsQuadratic.inv
  条件: {χ : MulChar R R'} (hχ : χ.IsQuadratic)
  结论: χ⁻¹ = χ
  证明: by
  ext x
  rw [inv_apply_eq_inv]
  rcases hχ x with (h₀ | h₁ | h₂)
  · rw [h₀, Ring.inverse_zero]
  · rw [h₁, Ring.inverse_one]
  · -- Porting note (#11573): was `by norm_cast`
    have : (-1 : R') = (-1 : R'ˣ) := by norm_cast; simp
    rw [h₂]; rw [this]; rw [Ring.inverse_unit (-1 : R'ˣ)]; rw [in

Depends on / 依赖: Porting, Ring.inverse_one, Ring.inverse_unit, Ring.inverse_zero, inv_apply_eq_inv, inv_neg, inv_one, inverse_one, inverse_unit, inverse_zero
-/
theorem IsQuadratic.inv {χ : MulChar R R'} (hχ : χ.IsQuadratic) : χ⁻¹ = χ := by
  ext x
  rw [inv_apply_eq_inv]
  rcases hχ x with (h₀ | h₁ | h₂)
  · rw [h₀, Ring.inverse_zero]
  · rw [h₁, Ring.inverse_one]
  · -- Porting note (#11573): was `by norm_cast`
    have : (-1 : R') = (-1 : R'ˣ) := by norm_cast; simp
    rw [h₂]; rw [this]; rw [Ring.inverse_unit (-1 : R'ˣ)]; rw [inv_neg]; rw [inv_one]

/--
theorem `IsQuadratic.sq_eq_one` / 定理 `IsQuadratic.sq_eq_one`

English:
theorem IsQuadratic.sq_eq_one
  given: {χ : MulChar R R'} (hχ : χ.IsQuadratic)
  statement: χ ^ 2 = 1
  proof: by
  rw [← inv_mul_cancel χ]; rw [pow_two]; rw [hχ.inv]

中文:
定理 IsQuadratic.sq_eq_one
  条件: {χ : MulChar R R'} (hχ : χ.IsQuadratic)
  结论: χ ^ 2 = 1
  证明: by
  rw [← inv_mul_cancel χ]; rw [pow_two]; rw [hχ.inv]

Depends on / 依赖: inv_mul_cancel, pow_two
-/
theorem IsQuadratic.sq_eq_one {χ : MulChar R R'} (hχ : χ.IsQuadratic) : χ ^ 2 = 1 := by
  rw [← inv_mul_cancel χ]; rw [pow_two]; rw [hχ.inv]

/--
theorem `IsQuadratic.pow_char` / 定理 `IsQuadratic.pow_char`

English:
theorem IsQuadratic.pow_char
  statement: {χ : MulChar R R'} (hχ : χ.IsQuadratic) (p : Nat) [hp : Fact p.Prime]
  proof: by
  ext x
  rw [pow_apply_coe]
  rcases hχ x with (hx | hx | hx) <;> rw [hx]
  · rw [zero_pow (@Fact.out p.Prime).ne_zero]
  · rw [one_pow]
  · exact neg_one_pow_char R' p

中文:
定理 IsQuadratic.pow_char
  结论: {χ : MulChar R R'} (hχ : χ.IsQuadratic) (p : 自然数) [hp : Fact p.Prime]
  证明: by
  ext x
  rw [pow_apply_coe]
  rcases hχ x with (hx | hx | hx) <;> rw [hx]
  · rw [zero_pow (@Fact.out p.Prime).ne_zero]
  · rw [one_pow]
  · exact neg_one_pow_char R' p

Depends on / 依赖: Fact.out, ne_zero, neg_one_pow_char, one_pow, p.Prime, pow_apply_coe, zero_pow
-/
theorem IsQuadratic.pow_char {χ : MulChar R R'} (hχ : χ.IsQuadratic) (p : Nat) [hp : Fact p.Prime]
    [CharP R' p] : χ ^ p = χ := by
  ext x
  rw [pow_apply_coe]
  rcases hχ x with (hx | hx | hx) <;> rw [hx]
  · rw [zero_pow (@Fact.out p.Prime).ne_zero]
  · rw [one_pow]
  · exact neg_one_pow_char R' p

/--
theorem `IsQuadratic.pow_even` / 定理 `IsQuadratic.pow_even`

English:
theorem IsQuadratic.pow_even
  given: {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : Nat} (hn : Even n)
  proof: by
  obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp hn
  rw [pow_mul]; rw [hχ.sq_eq_one]; rw [one_pow]

中文:
定理 IsQuadratic.pow_even
  条件: {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : 自然数} (hn : Even n)
  证明: by
  obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp hn
  rw [pow_mul]; rw [hχ.sq_eq_one]; rw [one_pow]

Depends on / 依赖: even_iff_two_dvd, even_iff_two_dvd.mp, one_pow, pow_mul, sq_eq_one
-/
theorem IsQuadratic.pow_even {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : Nat} (hn : Even n) :
    χ ^ n = 1 := by
  obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp hn
  rw [pow_mul]; rw [hχ.sq_eq_one]; rw [one_pow]

/--
theorem `IsQuadratic.pow_odd` / 定理 `IsQuadratic.pow_odd`

English:
theorem IsQuadratic.pow_odd
  given: {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : Nat} (hn : Odd n)
  proof: by
  obtain ⟨n, rfl⟩ := hn
  rw [pow_add]; rw [pow_one]; rw [hχ.pow_even (even_two_mul _)]; rw [one_mul]

中文:
定理 IsQuadratic.pow_odd
  条件: {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : 自然数} (hn : Odd n)
  证明: by
  obtain ⟨n, rfl⟩ := hn
  rw [pow_add]; rw [pow_one]; rw [hχ.pow_even (even_two_mul _)]; rw [one_mul]

Depends on / 依赖: even_two_mul, one_mul, pow_add, pow_even, pow_one
-/
theorem IsQuadratic.pow_odd {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : Nat} (hn : Odd n) :
    χ ^ n = χ := by
  obtain ⟨n, rfl⟩ := hn
  rw [pow_add]; rw [pow_one]; rw [hχ.pow_even (even_two_mul _)]; rw [one_mul]

/--
lemma `isQuadratic_iff_sq_eq_one` / 引理 `isQuadratic_iff_sq_eq_one`

English:
lemma isQuadratic_iff_sq_eq_one
  statement: {M R : Type*} [CommMonoid M] [CommRing R] [NoZeroDivisors R]
  proof: by
  refine ⟨fun h => ext (fun x => ?_), fun h x => ?_⟩
  · rw [one_apply_coe, χ.pow_apply_coe]
    rcases h x with H | H | H
    · exact (not_isUnit_zero <| H ▸ IsUnit.map χ <| x.isUnit).elim
    · simp only [H, one_pow]
    · simp only [H, even_two, Even.neg_pow, one_pow]
  · by_cases hx : IsUnit 

中文:
引理 isQuadratic_iff_sq_eq_one
  结论: {M R : 类型} [CommMonoid M] [CommRing R] [NoZeroDivisors R]
  证明: by
  refine ⟨fun h => ext (fun x => ?_), fun h x => ?_⟩
  · rw [one_apply_coe, χ.pow_apply_coe]
    rcases h x with H | H | H
    · exact (not_isUnit_zero <| H ▸ IsUnit.map χ <| x.isUnit).elim
    · simp only [H, one_pow]
    · simp only [H, even_two, Even.neg_pow, one_pow]
  · by_cases hx : IsUnit 

Depends on / 依赖: Even.neg_pow, IsUnit, IsUnit.map, MulChar, MulChar.one_apply, even_two, isUnit, map_nonunit, neg_pow, not_isUnit_zero, one_apply, one_apply_coe, one_pow, pow_apply, pow_apply_coe, sq_eq_one_iff, sq_eq_one_iff.mp, two_ne_zero, x.isUnit
-/
lemma isQuadratic_iff_sq_eq_one {M R : Type*} [CommMonoid M] [CommRing R] [NoZeroDivisors R]
    [Nontrivial R] {χ : MulChar M R} :
    IsQuadratic χ ↔ χ ^ 2 = 1 := by
  refine ⟨fun h => ext (fun x => ?_), fun h x => ?_⟩
  · rw [one_apply_coe, χ.pow_apply_coe]
    rcases h x with H | H | H
    · exact (not_isUnit_zero <| H ▸ IsUnit.map χ <| x.isUnit).elim
    · simp only [H, one_pow]
    · simp only [H, even_two, Even.neg_pow, one_pow]
  · by_cases hx : IsUnit x
· refine .inr sq_eq_one_iff.mp ?_
      rw [← χ.pow_apply' two_ne_zero]; rw [h]; rw [MulChar.one_apply hx]
· exact .inl map_nonunit χ hx

end quadratic_and_comp

end Properties

/-!
### Multiplicative characters with finite domain
-/

section Finite

variable {M : Type*} [CommMonoid M]
variable {R : Type*} [CommMonoidWithZero R]

/--
lemma `pow_card_eq_one` / 引理 `pow_card_eq_one`

English:
lemma pow_card_eq_one
  given: [Fintype Mˣ] (χ : MulChar M R)
  statement: χ ^ (Fintype.card Mˣ) = 1
  proof: by
  ext1
  rw [pow_apply_coe]; rw [← map_pow]; rw [one_apply_coe]; rw [← Units.val_pow_eq_pow_val]; rw [pow_card_eq_one]; rw [Units.val_eq_one.mpr rfl]; rw [map_one]

中文:
引理 pow_card_eq_one
  条件: [Fintype Mˣ] (χ : MulChar M R)
  结论: χ ^ (Fintype.card Mˣ) = 1
  证明: by
  ext1
  rw [pow_apply_coe]; rw [← map_pow]; rw [one_apply_coe]; rw [← Units.val_pow_eq_pow_val]; rw [pow_card_eq_one]; rw [Units.val_eq_one.mpr rfl]; rw [map_one]
-/
protected lemma pow_card_eq_one [Fintype Mˣ] (χ : MulChar M R) : χ ^ (Fintype.card Mˣ) = 1 := by
  ext1
  rw [pow_apply_coe]; rw [← map_pow]; rw [one_apply_coe]; rw [← Units.val_pow_eq_pow_val]; rw [pow_card_eq_one]; rw [Units.val_eq_one.mpr rfl]; rw [map_one]

/--
lemma `orderOf_pos` / 引理 `orderOf_pos`

English:
lemma orderOf_pos
  given: [Finite Mˣ] (χ : MulChar M R)
  statement: 0 < orderOf χ
  proof: by
  cases nonempty_fintype Mˣ
  apply IsOfFinOrder.orderOf_pos
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, Fintype.card_pos, χ.pow_card_eq_one⟩

中文:
引理 orderOf_pos
  条件: [Finite Mˣ] (χ : MulChar M R)
  结论: 0 < orderOf χ
  证明: by
  cases nonempty_fintype Mˣ
  apply IsOfFinOrder.orderOf_pos
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, Fintype.card_pos, χ.pow_card_eq_one⟩

Depends on / 依赖: Fintype, Fintype.card_pos, IsOfFinOrder, IsOfFinOrder.orderOf_pos, card_pos, isOfFinOrder_iff_pow_eq_one, nonempty_fintype, orderOf_pos, pow_card_eq_one
-/
lemma orderOf_pos [Finite Mˣ] (χ : MulChar M R) : 0 < orderOf χ := by
  cases nonempty_fintype Mˣ
  apply IsOfFinOrder.orderOf_pos
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, Fintype.card_pos, χ.pow_card_eq_one⟩

end Finite

section sum

variable {R : Type*} [CommMonoid R] [Fintype R] {R' : Type*} [CommRing R']

/--
theorem `sum_eq_zero_of_ne_one` / 定理 `sum_eq_zero_of_ne_one`

English:
theorem sum_eq_zero_of_ne_one
  given: [IsDomain R'] {χ : MulChar R R'} (hχ : χ != 1)
  statement: ∑ a, χ a = 0
  proof: by
  rcases ne_one_iff.mp hχ with ⟨b, hb⟩
  refine eq_zero_of_mul_eq_self_left hb ?_
  simpa only [Finset.mul_sum, ← map_mul] using b.mulLeft_bijective.sum_comp _

中文:
定理 sum_eq_zero_of_ne_one
  条件: [IsDomain R'] {χ : MulChar R R'} (hχ : χ != 1)
  结论: ∑ a, χ a = 0
  证明: by
  rcases ne_one_iff.mp hχ with ⟨b, hb⟩
  refine eq_zero_of_mul_eq_self_left hb ?_
  simpa only [Finset.mul_sum, ← map_mul] using b.mulLeft_bijective.sum_comp _

Depends on / 依赖: Finset, Finset.mul_sum, b.mulLeft_bijective.sum_comp, eq_zero_of_mul_eq_self_left, map_mul, mulLeft_bijective, mul_sum, ne_one_iff, ne_one_iff.mp, sum_comp
-/
theorem sum_eq_zero_of_ne_one [IsDomain R'] {χ : MulChar R R'} (hχ : χ != 1) : ∑ a, χ a = 0 := by
  rcases ne_one_iff.mp hχ with ⟨b, hb⟩
  refine eq_zero_of_mul_eq_self_left hb ?_
  simpa only [Finset.mul_sum, ← map_mul] using b.mulLeft_bijective.sum_comp _

/--
theorem `sum_one_eq_card_units` / 定理 `sum_one_eq_card_units`

English:
theorem sum_one_eq_card_units
  given: [DecidableEq R]
  proof: by
  calc
    (∑ a, (1 : MulChar R R') a) = ∑ a : R, if IsUnit a then 1 else 0 :=
      Finset.sum_congr rfl fun a _ => ?_
    _ = ((Finset.univ : Finset R).filter IsUnit).card := Finset.sum_boole _ _
    _ = (Finset.univ.map ⟨((↑) : Rˣ -> R), Units.val_injective⟩).card := ?_
    _ = Fintype.card Rˣ

中文:
定理 sum_one_eq_card_units
  条件: [DecidableEq R]
  证明: by
  calc
    (∑ a, (1 : MulChar R R') a) = ∑ a : R, if IsUnit a then 1 else 0 :=
      Finset.sum_congr rfl fun a _ => ?_
    _ = ((Finset.univ : Finset R).filter IsUnit).card := Finset.sum_boole _ _
    _ = (Finset.univ.map ⟨((↑) : Rˣ -> R), Units.val_injective⟩).card := ?_
    _ = Fintype.card Rˣ

Depends on / 依赖: Finset, Finset.card_map, Finset.sum_boole, Finset.sum_congr, Finset.univ, Finset.univ.map, Fintype, Fintype.card, IsUnit, MulChar, Units.val_injective, card_map, congr_arg, filter, h.unit, map_nonunit, one_apply_coe, split_ifs, sum_boole, sum_congr
-/
theorem sum_one_eq_card_units [DecidableEq R] :
    (∑ a, (1 : MulChar R R') a) = Fintype.card Rˣ := by
  calc
    (∑ a, (1 : MulChar R R') a) = ∑ a : R, if IsUnit a then 1 else 0 :=
      Finset.sum_congr rfl fun a _ => ?_
    _ = ((Finset.univ : Finset R).filter IsUnit).card := Finset.sum_boole _ _
    _ = (Finset.univ.map ⟨((↑) : Rˣ -> R), Units.val_injective⟩).card := ?_
    _ = Fintype.card Rˣ := congr_arg _ (Finset.card_map _)
  · split_ifs with h
    · exact one_apply_coe h.unit
    · exact map_nonunit _ h
  · congr
    ext a
    simp [IsUnit]

end sum

/-!
### Multiplicative characters on rings
-/

section Ring

variable {R R' : Type*} [CommRing R] [CommMonoidWithZero R']

/--
lemma `val_neg_one_eq_one_of_odd_order` / 引理 `val_neg_one_eq_one_of_odd_order`

English:
lemma val_neg_one_eq_one_of_odd_order
  given: {χ : MulChar R R'} {n : Nat} (hn : Odd n) (hχ : χ ^ n = 1)
  proof: by
  rw [← hn.neg_one_pow]; rw [map_pow]; rw [← χ.pow_apply' (Nat.ne_of_odd_add hn)]; rw [hχ]
  exact MulChar.one_apply_coe (-1)

中文:
引理 val_neg_one_eq_one_of_odd_order
  条件: {χ : MulChar R R'} {n : 自然数} (hn : Odd n) (hχ : χ ^ n = 1)
  证明: by
  rw [← hn.neg_one_pow]; rw [map_pow]; rw [← χ.pow_apply' (Nat.ne_of_odd_add hn)]; rw [hχ]
  exact MulChar.one_apply_coe (-1)

Depends on / 依赖: MulChar, MulChar.one_apply_coe, Nat.ne_of_odd_add, hn.neg_one_pow, map_pow, ne_of_odd_add, neg_one_pow, one_apply_coe, pow_apply
-/
lemma val_neg_one_eq_one_of_odd_order {χ : MulChar R R'} {n : Nat} (hn : Odd n) (hχ : χ ^ n = 1) :
    χ (-1) = 1 := by
  rw [← hn.neg_one_pow]; rw [map_pow]; rw [← χ.pow_apply' (Nat.ne_of_odd_add hn)]; rw [hχ]
  exact MulChar.one_apply_coe (-1)

end Ring

end MulChar
