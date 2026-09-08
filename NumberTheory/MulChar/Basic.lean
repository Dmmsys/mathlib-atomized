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

/-- Define a structure for multiplicative characters.
A multiplicative character from a commutative monoid `R` to a commutative monoid with zero `R'`
is a homomorphism of (multiplicative) monoids that sends non-units to zero. -/
/-
**MulChar** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [CommMonoid R] → (R' : Type u_2) → [CommMonoidWithZero R'
] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a structure for multiplicative characters.
A multiplicative character from a commutative monoid `R` to a commutative monoid
 with zero `R'`
is a homomorphism of (multiplicative) monoids that sends non-units to zero.
-/
structure MulChar extends MonoidHom R R' where
  map_nonunit' : ∀ a : R, ¬IsUnit a → toFun a = 0
/-
**MulChar.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：MulChar.instFunLike : FunLike (MulChar R R') R R'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance MulChar.instFunLike : FunLike (MulChar R R') R R' :=
  ⟨fun χ => χ.toFun,
    fun χ₀ χ₁ h => by cases χ₀; cases χ₁; congr; apply MonoidHom.ext (fun _ => congr_fun h _)⟩

/-- This is the corresponding extension of `MonoidHomClass`. -/
/-
**MulCharClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_3) →   (R : outParam (Type u_4)) →     (R' : outParam (Type u_
5)) → [CommMonoid R] → [CommMonoidWithZero R'] → [FunLike F R R'] → Prop
参数：Type u_4；Type u_5。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the corresponding extension of `MonoidHomClass`.
-/
class MulCharClass (F : Type*) (R R' : outParam Type*) [CommMonoid R]
    [CommMonoidWithZero R'] [FunLike F R R'] : Prop extends MonoidHomClass F R R' where
  map_nonunit : ∀ (χ : F) {a : R} (_ : ¬IsUnit a), χ a = 0

initialize_simps_projections MulChar (toFun → apply, -toMonoidHom)

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
/-
**MulChar.trivial** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：trivial : MulChar R R' where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial multiplicative character. It takes the value `0` on non-units and
the value `1` on units.
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
/-
**MulChar.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：coe_mk (f : R ->* R') (hf) : (MulChar.mk f hf : R -> R') = f
参数：f : R ->* R'；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : R →* R') (hf) : (MulChar.mk f hf : R → R') = f :=
  rfl

/-- Extensionality. See `ext` below for the version that will actually be used. -/
/-
**MulChar.ext'** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：ext' {χ χ' : MulChar R R'} (h : forall a, χ a = χ' a) : χ = χ'
参数：h : forall a, χ a = χ' a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g

--- 原说明 ---
Extensionality. See `ext` below for the version that will actually be used.
-/
theorem ext' {χ χ' : MulChar R R'} (h : ∀ a, χ a = χ' a) : χ = χ' := DFunLike.ext _ _ h
/-
**MulChar.** 是 Mathlib 中的一个实例，位于命名空间 `MulChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulCharClass (MulChar R R') R R' where
  map_mul χ := χ.map_mul'
  map_one χ := χ.map_one'
  map_nonunit χ := χ.map_nonunit' _
/-
**MulChar.map_nonunit** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUnit a) : χ a = 0
参数：χ : MulChar R R'；ha : ¬IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.map_nonunit'`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type 
u_2} [inst_1 : CommMonoidWithZero R'] (self : MulChar R R') (a : R),   ¬IsUnit a
 → (↑self.…
-/
theorem map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUnit a) : χ a = 0 :=
  χ.map_nonunit' a ha

/-- Extensionality. Since `MulChar`s always take the value zero on non-units, it is sufficient
to compare the values on units. -/
@[ext]
/-
**MulChar.ext** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) : χ = χ'
参数：h : forall a : Rˣ, χ a = χ' a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext'`：ext' {χ χ' : MulChar R R'} (h : forall a, χ a = χ' a) : χ 
= χ'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0

--- 原说明 ---
Extensionality. Since `MulChar`s always take the value zero on non-units, it is 
sufficient
to compare the values on units.
-/
theorem ext {χ χ' : MulChar R R'} (h : ∀ a : Rˣ, χ a = χ' a) : χ = χ' := by
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


/-- Turn a `MulChar` into a homomorphism between the unit groups. -/
/-
**MulChar.toUnitHom** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：toUnitHom (χ : MulChar R R') : Rˣ ->* R'ˣ
参数：χ : MulChar R R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a `MulChar` into a homomorphism between the unit groups.
-/
def toUnitHom (χ : MulChar R R') : Rˣ →* R'ˣ :=
  Units.map χ
/-
**MulChar.coe_toUnitHom** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.toUnitHom a) = χ a
参数：χ : MulChar R R'；a : Rˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.toUnitHom a) = χ a :=
  rfl

/-- Turn a homomorphism between unit groups into a `MulChar`. -/
/-
**MulChar.ofUnitHom** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：ofUnitHom (f : Rˣ ->* R'ˣ) : MulChar R R' where toFun
参数：f : Rˣ ->* R'ˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a homomorphism between unit groups into a `MulChar`.
-/
noncomputable def ofUnitHom (f : Rˣ →* R'ˣ) : MulChar R R' where
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
          rw [hm, map_mul]
          norm_cast
        · simp only [hy, not_false_iff, dif_neg, mul_zero]
      · simp only [hx, IsUnit.mul_iff, false_and, not_false_iff, dif_neg, zero_mul]
  map_nonunit' := by
    intro a ha
    simp only [ha, not_false_iff, dif_neg]
/-
**MulChar.ofUnitHom_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：ofUnitHom_coe (f : Rˣ ->* R'ˣ) (a : Rˣ) : ofUnitHom f ↑a = f a
参数：f : Rˣ ->* R'ˣ；a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `IsUnit.unit_of_val_units`：unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)
) : h.unit = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofUnitHom_coe (f : Rˣ →* R'ˣ) (a : Rˣ) : ofUnitHom f ↑a = f a := by simp [ofUnitHom]

/-- The equivalence between multiplicative characters and homomorphisms of unit groups. -/
/-
**MulChar.equivToUnitHom** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：equivToUnitHom : MulChar R R' ≃ (Rˣ ->* R'ˣ) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between multiplicative characters and homomorphisms of unit grou
ps.
-/
noncomputable def equivToUnitHom : MulChar R R' ≃ (Rˣ →* R'ˣ) where
  toFun := toUnitHom
  invFun := ofUnitHom
  left_inv := by
    intro χ
    ext x
    rw [ofUnitHom_coe, coe_toUnitHom]
  right_inv := by
    intro f
    ext x
    simp only [coe_toUnitHom, ofUnitHom_coe]

@[simp]
/-
**MulChar.toUnitHom_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：toUnitHom_eq (χ : MulChar R R') : toUnitHom χ = equivToUnitHom χ
参数：χ : MulChar R R'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toUnitHom_eq (χ : MulChar R R') : toUnitHom χ = equivToUnitHom χ :=
  rfl

@[simp]
/-
**MulChar.ofUnitHom_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：ofUnitHom_eq (χ : Rˣ ->* R'ˣ) : ofUnitHom χ = equivToUnitHom.symm χ
参数：χ : Rˣ ->* R'ˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofUnitHom_eq (χ : Rˣ →* R'ˣ) : ofUnitHom χ = equivToUnitHom.symm χ :=
  rfl

@[simp]
/-
**MulChar.coe_equivToUnitHom** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：coe_equivToUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(equivToUnitHom χ a) = χ
 a
参数：χ : MulChar R R'；a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.coe_toUnitHom`：coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.t
oUnitHom a) = χ a
-/
theorem coe_equivToUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(equivToUnitHom χ a) = χ a :=
  coe_toUnitHom χ a

@[simp]
/-
**MulChar.equivToUnitHom_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：equivToUnitHom_symm_coe (f : Rˣ ->* R'ˣ) (a : Rˣ) : equivToUnitHom.symm f 
↑a = f a
参数：f : Rˣ ->* R'ˣ；a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ofUnitHom_coe`：ofUnitHom_coe (f : Rˣ ->* R'ˣ) (a : Rˣ) : ofUnitH
om f ↑a = f a
-/
theorem equivToUnitHom_symm_coe (f : Rˣ →* R'ˣ) (a : Rˣ) : equivToUnitHom.symm f ↑a = f a :=
  ofUnitHom_coe f a

@[simp]
/-
**MulChar.coe_toMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：coe_toMonoidHom (χ : MulChar R R') (x : R) : χ.toMonoidHom x = χ x
参数：χ : MulChar R R'；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toMonoidHom (χ : MulChar R R')
    (x : R) : χ.toMonoidHom x = χ x := rfl
/-
**MulChar.apply_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：apply_ne_zero_iff [Nontrivial R'] {χ : MulChar R R'} {a : R} : χ a != 0 ↔ 
IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
-/
theorem apply_ne_zero_iff [Nontrivial R'] {χ : MulChar R R'} {a : R} :
    χ a ≠ 0 ↔ IsUnit a :=
  ⟨by simpa using (map_nonunit χ).mt, fun h ↦ (h.map χ).ne_zero⟩
/-
**MulChar.apply_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：apply_eq_zero_iff [Nontrivial R'] {χ : MulChar R R'} {a : R} : χ a = 0 ↔ ¬
 IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `MulChar.apply_ne_zero_iff`：apply_ne_zero_iff [Nontrivial R'] {χ : MulCha
r R R'} {a : R} : χ a != 0 ↔ IsUnit a
-/
theorem apply_eq_zero_iff [Nontrivial R'] {χ : MulChar R R'} {a : R} :
    χ a = 0 ↔ ¬ IsUnit a := by
  simpa using χ.apply_ne_zero_iff.not

/-!
### Commutative group structure on multiplicative characters

The multiplicative characters `R → R'` form a commutative group.
-/


/-
**MulChar.map_one** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} [inst_1 : CommMonoi
dWithZero R'] (χ : MulChar R R'), χ 1 = 1
参数：χ : MulChar R R'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OneHom.map_one'`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [inst_
1 : One N] (self : OneHom M N), self.toFun 1 = 1

--- 原说明 ---
### Commutative group structure on multiplicative characters

The multiplicative characters `R → R'` form a commutative group.
-/
protected theorem map_one (χ : MulChar R R') : χ (1 : R) = 1 :=
  χ.map_one'

/-- If the domain has a zero (and is nontrivial), then `χ 0 = 0`. -/
/-
**MulChar.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：∀ {R' : Type u_2} [inst : CommMonoidWithZero R'] {R : Type u_3} [inst_1 : 
CommMonoidWithZero R] [Nontrivial R]   (χ : MulChar R R'), χ 0 = 0
参数：χ : MulChar R R'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)

--- 原说明 ---
If the domain has a zero (and is nontrivial), then `χ 0 = 0`.
-/
protected theorem map_zero {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R') :
    χ (0 : R) = 0 := by rw [map_nonunit χ not_isUnit_zero]

/-- We can convert a multiplicative character into a homomorphism of monoids with zero when
the source has a zero and another element. -/
@[coe, simps]
/-
**MulChar.toMonoidWithZeroHom** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：toMonoidWithZeroHom {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ :
 MulChar R R') : R ->*₀ R' where toFun
参数：χ : MulChar R R'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.map_zero`：∀ {R' : Type u_2} [inst : CommMonoidWithZero R'] {R : 
Type u_3} [inst_1 : CommMonoidWithZero R] [Nontrivial R]   (χ : MulChar R R'), χ
 0 = 0

--- 原说明 ---
We can convert a multiplicative character into a homomorphism of monoids with ze
ro when
the source has a zero and another element.
-/
def toMonoidWithZeroHom {R : Type*} [CommMonoidWithZero R] [Nontrivial R] (χ : MulChar R R') :
    R →*₀ R' where
  toFun := χ.toFun
  map_zero' := χ.map_zero
  map_one' := χ.map_one'
  map_mul' := χ.map_mul'

/-- If the domain is a ring `R`, then `χ (ringChar R) = 0`. -/
/-
**MulChar.map_ringChar** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：map_ringChar {R : Type*} [CommSemiring R] [Nontrivial R] (χ : MulChar R R'
) : χ (ringChar R) = 0
参数：χ : MulChar R R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ringChar.Nat.cast_ringChar`：∀ {R : Type u_1} [inst : NonAssocSemiring R]
, ↑(ringChar R) = 0
· 使用定理 `MulChar.map_zero`：∀ {R' : Type u_2} [inst : CommMonoidWithZero R'] {R : 
Type u_3} [inst_1 : CommMonoidWithZero R] [Nontrivial R]   (χ : MulChar R R'), χ
 0 = 0

--- 原说明 ---
If the domain is a ring `R`, then `χ (ringChar R) = 0`.
-/
theorem map_ringChar {R : Type*} [CommSemiring R] [Nontrivial R] (χ : MulChar R R') :
    χ (ringChar R) = 0 := by rw [ringChar.Nat.cast_ringChar, χ.map_zero]
/-
**MulChar.hasOne** 是 Mathlib 中的一个实例，位于命名空间 `MulChar`。
形式化陈述：hasOne : One (MulChar R R')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance hasOne : One (MulChar R R') :=
  ⟨trivial R R'⟩
/-
**MulChar.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `MulChar`。
形式化陈述：inhabited : Inhabited (MulChar R R')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance inhabited : Inhabited (MulChar R R') :=
  ⟨1⟩

/-- Evaluation of the trivial character -/
@[simp]
/-
**MulChar.one_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1
参数：a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u

--- 原说明 ---
Evaluation of the trivial character
-/
theorem one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1 := by exact dif_pos a.isUnit

/-- Evaluation of the trivial character -/
/-
**MulChar.one_apply** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R') x = 1
参数：hx : IsUnit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1

--- 原说明 ---
Evaluation of the trivial character
-/
lemma one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R') x = 1 := one_apply_coe hx.unit

/-- Multiplication of multiplicative characters. (This needs the target to be commutative.) -/
/-
**MulChar.mul** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：mul (χ χ' : MulChar R R') : MulChar R R'
参数：χ χ' : MulChar R R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplication of multiplicative characters. (This needs the target to be commut
ative.)
-/
def mul (χ χ' : MulChar R R') : MulChar R R' :=
  { χ.toMonoidHom * χ'.toMonoidHom with
    toFun := χ * χ'
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, zero_mul, Pi.mul_apply] }
/-
**MulChar.hasMul** 是 Mathlib 中的一个实例，位于命名空间 `MulChar`。
形式化陈述：hasMul : Mul (MulChar R R')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasMul : Mul (MulChar R R') :=
  ⟨mul⟩
/-
**MulChar.mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：mul_apply (χ χ' : MulChar R R') (a : R) : (χ * χ') a = χ a * χ' a
参数：χ χ' : MulChar R R'；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_apply (χ χ' : MulChar R R') (a : R) : (χ * χ') a = χ a * χ' a :=
  rfl

@[simp]
/-
**MulChar.coeToFun_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：coeToFun_mul (χ χ' : MulChar R R') : ⇑(χ * χ') = χ * χ'
参数：χ χ' : MulChar R R'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeToFun_mul (χ χ' : MulChar R R') : ⇑(χ * χ') = χ * χ' :=
  rfl
/-
**MulChar.one_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} [inst_1 : CommMonoi
dWithZero R'] (χ : MulChar R R'), 1 * χ = χ
参数：χ : MulChar R R'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem one_mul (χ : MulChar R R') : (1 : MulChar R R') * χ = χ := by
  ext
  simp only [one_mul, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]
/-
**MulChar.mul_one** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} [inst_1 : CommMonoi
dWithZero R'] (χ : MulChar R R'), χ * 1 = χ
参数：χ : MulChar R R'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mul_one (χ : MulChar R R') : χ * 1 = χ := by
  ext
  simp only [mul_one, Pi.mul_apply, MulChar.coeToFun_mul, MulChar.one_apply_coe]

/-- The inverse of a multiplicative character. We define it as `inverse ∘ χ`. -/
/-
**MulChar.inv** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：inv (χ : MulChar R R') : MulChar R R'
参数：χ : MulChar R R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a multiplicative character. We define it as `inverse ∘ χ`.
-/
noncomputable def inv (χ : MulChar R R') : MulChar R R' :=
  { MonoidWithZero.inverse.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => MonoidWithZero.inverse (χ a)
    map_nonunit' := fun a ha => by simp [map_nonunit _ ha] }
/-
**MulChar.hasInv** 是 Mathlib 中的一个实例，位于命名空间 `MulChar`。
形式化陈述：hasInv : Inv (MulChar R R')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance hasInv : Inv (MulChar R R') :=
  ⟨inv⟩

/-- The inverse of a multiplicative character `χ`, applied to `a`, is the inverse of `χ a`. -/
/-
**MulChar.inv_apply_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：inv_apply_eq_inv (χ : MulChar R R') (a : R) : χ⁻¹ a = (χ a)⁻¹ʳ
参数：χ : MulChar R R'；a : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a multiplicative character `χ`, applied to `a`, is the inverse of
 `χ a`.
-/
theorem inv_apply_eq_inv (χ : MulChar R R') (a : R) : χ⁻¹ a = (χ a)⁻¹ʳ :=
  Eq.refl <| inv χ a

/-- The inverse of a multiplicative character `χ`, applied to `a`, is the inverse of `χ a`.
Variant when the target is a field -/
/-
**MulChar.inv_apply_eq_inv'** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：inv_apply_eq_inv' {R' : Type*} [CommGroupWithZero R'] (χ : MulChar R R') (
a : R) : χ⁻¹ a = (χ a)⁻¹
参数：χ : MulChar R R'；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulChar.inv_apply_eq_inv`：inv_apply_eq_inv (χ : MulChar R R') (a : R) : 
χ⁻¹ a = (χ a)⁻¹ʳ
· 使用定理 `Ring.inverse_eq_inv`：Ring.inverse_eq_inv (a : G₀) : a⁻¹ʳ = a⁻¹

--- 原说明 ---
The inverse of a multiplicative character `χ`, applied to `a`, is the inverse of
 `χ a`.
Variant when the target is a field
-/
theorem inv_apply_eq_inv' {R' : Type*} [CommGroupWithZero R'] (χ : MulChar R R') (a : R) :
    χ⁻¹ a = (χ a)⁻¹ :=
  (inv_apply_eq_inv χ a).trans <| Ring.inverse_eq_inv (χ a)

/-- When the domain has a zero, then the inverse of a multiplicative character `χ`,
applied to `a`, is `χ` applied to the inverse of `a`. -/
/-
**MulChar.inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：inv_apply {R : Type*} [CommMonoidWithZero R] (χ : MulChar R R') (a : R) : 
χ⁻¹ a = χ a⁻¹ʳ
参数：χ : MulChar R R'；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.inv_apply_eq_inv`：inv_apply_eq_inv (χ : MulChar R R') (a : R) : 
χ⁻¹ a = (χ a)⁻¹ʳ
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `IsUnit.mul_right_injective`：∀ {M : Type u_1} [inst : Monoid M] {a : M}, 
IsUnit a → Function.Injective fun x => a * x
· 使用定理 `Ring.mul_inverse_cancel`：mul_inverse_cancel (x : M₀) (h : IsUnit x) : x 
* x⁻¹ʳ = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0
· 使用定理 `Ring.inverse_non_unit`：inverse_non_unit (x : M₀) (h : ¬IsUnit x) : x⁻¹ʳ 
= 0
· 使用定理 `MulChar.map_zero`：∀ {R' : Type u_2} [inst : CommMonoidWithZero R'] {R : 
Type u_3} [inst_1 : CommMonoidWithZero R] [Nontrivial R]   (χ : MulChar R R'), χ
 0 = 0

--- 原说明 ---
When the domain has a zero, then the inverse of a multiplicative character `χ`,
applied to `a`, is `χ` applied to the inverse of `a`.
-/
theorem inv_apply {R : Type*} [CommMonoidWithZero R] (χ : MulChar R R') (a : R) :
    χ⁻¹ a = χ a⁻¹ʳ := by
  by_cases ha : IsUnit a
  · rw [inv_apply_eq_inv]
    have h := IsUnit.map χ ha
    apply_fun (χ a * ·) using IsUnit.mul_right_injective h
    dsimp only
    rw [Ring.mul_inverse_cancel _ h, ← map_mul, Ring.mul_inverse_cancel _ ha, map_one]
  · revert ha
    nontriviality R
    intro ha
    -- `nontriviality R` by itself doesn't do it
    rw [map_nonunit _ ha, Ring.inverse_non_unit a ha, MulChar.map_zero χ]

/-- When the domain has a zero, then the inverse of a multiplicative character `χ`,
applied to `a`, is `χ` applied to the inverse of `a`. -/
/-
**MulChar.inv_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：inv_apply' {R : Type*} [CommGroupWithZero R] (χ : MulChar R R') (a : R) : 
χ⁻¹ a = χ a⁻¹
参数：χ : MulChar R R'；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulChar.inv_apply`：inv_apply {R : Type*} [CommMonoidWithZero R] (χ : Mul
Char R R') (a : R) : χ⁻¹ a = χ a⁻¹ʳ
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Ring.inverse_eq_inv`：Ring.inverse_eq_inv (a : G₀) : a⁻¹ʳ = a⁻¹

--- 原说明 ---
When the domain has a zero, then the inverse of a multiplicative character `χ`,
applied to `a`, is `χ` applied to the inverse of `a`.
-/
theorem inv_apply' {R : Type*} [CommGroupWithZero R] (χ : MulChar R R') (a : R) : χ⁻¹ a = χ a⁻¹ :=
  (inv_apply χ a).trans <| congr_arg _ (Ring.inverse_eq_inv a)

/-- The product of a character with its inverse is the trivial character. -/
/-
**MulChar.inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：inv_mul (χ : MulChar R R') : χ⁻¹ * χ = 1
参数：χ : MulChar R R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.coeToFun_mul`：coeToFun_mul (χ χ' : MulChar R R') : ⇑(χ * χ') = χ
 * χ'
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `MulChar.inv_apply_eq_inv`：inv_apply_eq_inv (χ : MulChar R R') (a : R) : 
χ⁻¹ a = (χ a)⁻¹ʳ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ring.inverse_mul_cancel`：inverse_mul_cancel (x : M₀) (h : IsUnit x) : x⁻
¹ʳ * x = 1
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1

--- 原说明 ---
The product of a character with its inverse is the trivial character.
-/
theorem inv_mul (χ : MulChar R R') : χ⁻¹ * χ = 1 := by
  ext x
  rw [coeToFun_mul, Pi.mul_apply, inv_apply_eq_inv]
  simp only [Ring.inverse_mul_cancel _ (IsUnit.map χ x.isUnit)]
  rw [one_apply_coe]

/-- The commutative group structure on `MulChar R R'`. -/
/-
**MulChar.commGroup** 是 Mathlib 中的一个实例，位于命名空间 `MulChar`。
形式化陈述：commGroup : CommGroup (MulChar R R') where inv_mul_cancel
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.one_mul`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} 
[inst_1 : CommMonoidWithZero R'] (χ : MulChar R R'), 1 * χ = χ
· 使用定理 `MulChar.mul_one`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} 
[inst_1 : CommMonoidWithZero R'] (χ : MulChar R R'), χ * 1 = χ
· 使用定理 `MulChar.inv_mul`：inv_mul (χ : MulChar R R') : χ⁻¹ * χ = 1

--- 原说明 ---
The commutative group structure on `MulChar R R'`.
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

/-- If `a` is a unit and `n : ℕ`, then `(χ ^ n) a = (χ a) ^ n`. -/
/-
**MulChar.pow_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：pow_apply_coe (χ : MulChar R R') (n : Nat) (a : Rˣ) : (χ ^ n) a = χ a ^ n
参数：χ : MulChar R R'；n : Nat；a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `MulChar.mul_apply`：mul_apply (χ χ' : MulChar R R') (a : R) : (χ * χ') a 
= χ a * χ' a

--- 原说明 ---
If `a` is a unit and `n : ℕ`, then `(χ ^ n) a = (χ a) ^ n`.
-/
theorem pow_apply_coe (χ : MulChar R R') (n : ℕ) (a : Rˣ) : (χ ^ n) a = χ a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_apply_coe]
  | succ n ih => rw [pow_succ, pow_succ, mul_apply, ih]

/-- If `n` is positive, then `(χ ^ n) a = (χ a) ^ n`. -/
/-
**MulChar.pow_apply'** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：pow_apply' (χ : MulChar R R') {n : Nat} (hn : n != 0) (a : R) : (χ ^ n) a 
= χ a ^ n
参数：χ : MulChar R R'；hn : n != 0；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.pow_apply_coe`：pow_apply_coe (χ : MulChar R R') (n : Nat) (a : R
ˣ) : (χ ^ n) a = χ a ^ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0

--- 原说明 ---
If `n` is positive, then `(χ ^ n) a = (χ a) ^ n`.
-/
theorem pow_apply' (χ : MulChar R R') {n : ℕ} (hn : n ≠ 0) (a : R) : (χ ^ n) a = χ a ^ n := by
  by_cases ha : IsUnit a
  · exact pow_apply_coe χ n ha.unit
  · rw [map_nonunit (χ ^ n) ha, map_nonunit χ ha, zero_pow hn]
/-
**MulChar.equivToUnitHom_mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：equivToUnitHom_mul_apply (χ₁ χ₂ : MulChar R R') (a : Rˣ) : equivToUnitHom 
(χ₁ * χ₂) a = equivToUnitHom χ₁ a * equivToUnitHom χ₂ a
参数：χ₁ χ₂ : MulChar R R'；a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.coe_equivToUnitHom`：coe_equivToUnitHom (χ : MulChar R R') (a : R
ˣ) : ↑(equivToUnitHom χ a) = χ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivToUnitHom_mul_apply (χ₁ χ₂ : MulChar R R') (a : Rˣ) :
    equivToUnitHom (χ₁ * χ₂) a = equivToUnitHom χ₁ a * equivToUnitHom χ₂ a := by
  apply_fun ((↑) : R'ˣ → R') using Units.val_injective
  push_cast
  simp_rw [coe_equivToUnitHom, coeToFun_mul, Pi.mul_apply]

/-- The equivalence between multiplicative characters and homomorphisms of unit groups
as a multiplicative equivalence. -/
@[simps! apply symm_apply]
/-
**MulChar.mulEquivToUnitHom** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：mulEquivToUnitHom : MulChar R R' ≃* (Rˣ ->* R'ˣ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between multiplicative characters and homomorphisms of unit grou
ps
as a multiplicative equivalence.
-/
noncomputable def mulEquivToUnitHom : MulChar R R' ≃* (Rˣ →* R'ˣ) :=
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
/-
**MulChar.domRestrict** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：domRestrict {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S) (χ : Mu
lChar R R') : MulChar T R'
参数：T : S；χ : MulChar R R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a `MulChar` to a submonoid.
-/
noncomputable def domRestrict {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S)
    (χ : MulChar R R') : MulChar T R' :=
  ofUnitHom <| χ.toUnitHom.comp <| Units.map (SubmonoidClass.subtype T)

@[deprecated (since := "2026-07-19")] alias restrict := domRestrict
@[deprecated (since := "2026-07-19")] alias restrict_apply := domRestrict_apply

/--
The restriction of a `MulChar` to a submonoid as an homomorphism.
-/
@[simps]
/-
**MulChar.domRestrictHom** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：domRestrictHom {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S) (R''
 : Type*) [CommMonoidWithZero R''] : (MulChar R R'') ->* MulChar T R'' where toF
un
参数：T : S；R'' : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a `MulChar` to a submonoid as an homomorphism.
-/
noncomputable def domRestrictHom {S : Type*} [SetLike S R] [SubmonoidClass S R] (T : S)
    (R'' : Type*) [CommMonoidWithZero R''] :
    (MulChar R R'') →* MulChar T R'' where
  toFun := domRestrict T
  map_one' := by
    ext x
    rw [domRestrict_apply, if_pos x.isUnit, MulChar.one_apply x.isUnit.coe, one_apply_coe]
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

/-
**MulChar.eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：eq_one_iff {χ : MulChar R R'} : χ = 1 ↔ forall a : Rˣ, χ a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma eq_one_iff {χ : MulChar R R'} : χ = 1 ↔ ∀ a : Rˣ, χ a = 1 := by
  simp only [MulChar.ext_iff, one_apply_coe]
/-
**MulChar.ne_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：ne_one_iff {χ : MulChar R R'} : χ != 1 ↔ exists a : Rˣ, χ a != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ne_one_iff {χ : MulChar R R'} : χ ≠ 1 ↔ ∃ a : Rˣ, χ a ≠ 1 := by
  simp only [Ne, eq_one_iff, not_forall]
/-
**MulChar.domRestrict_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：domRestrict_eq_one_iff {S : Type*} [SetLike S R] [SubmonoidClass S R] {T :
 S} {χ : MulChar R R'} : χ.domRestrict T = 1 ↔ forall x : Tˣ, χ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulChar.domRestrict_apply`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : 
Type u_2} [inst_1 : CommMonoidWithZero R'] {S : Type u_3}   [inst_2 : SetLike S 
R] [inst_3 : Su…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem domRestrict_eq_one_iff {S : Type*} [SetLike S R] [SubmonoidClass S R] {T : S}
    {χ : MulChar R R'} : χ.domRestrict T = 1 ↔ ∀ x : Tˣ, χ x = 1 := by
  simp [eq_one_iff]

@[deprecated (since := "2026-07-19")] alias restrict_eq_one_iff := domRestrict_eq_one_iff

end nontrivial

section quadratic_and_comp

variable {R : Type*} [CommMonoid R] {R' : Type*} [CommRing R'] {R'' : Type*} [CommRing R'']

/-- A multiplicative character is *quadratic* if it takes only the values `0`, `1`, `-1`. -/
/-
**MulChar.IsQuadratic** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：IsQuadratic (χ : MulChar R R') : Prop
参数：χ : MulChar R R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A multiplicative character is *quadratic* if it takes only the values `0`, `1`, 
`-1`.
-/
def IsQuadratic (χ : MulChar R R') : Prop :=
  ∀ a, χ a = 0 ∨ χ a = 1 ∨ χ a = -1

/-- If two values of quadratic characters with target `ℤ` agree after coercion into a ring
of characteristic not `2`, then they agree in `ℤ`. -/
/-
**MulChar.IsQuadratic.eq_of_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulChar.IsQuadrati
c`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} [inst_1 : CommRing 
R'] {R'' : Type u_3} [inst_2 : CommRing R'']   {χ : MulChar R ℤ},   χ.IsQuadrati
c →     ∀ {χ' : MulChar R' ℤ},       χ'.IsQuadratic → ∀ [Nontrivial R''], ringCh
ar R'' ≠ 2 → ∀ {a : R} {a' : R'}, ↑(χ a) = ↑(χ' a') → χ a = χ' a'
参数：χ a；χ' a'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.cast_injOn_of_ringChar_ne_two`：Int.cast_injOn_of_ringChar_ne_two {R 
: Type*} [NonAssocRing R] [Nontrivial R] (hR : ringChar R != 2) : ({0, 1, -1} : 
Set Int).InjOn ((↑) : I…

--- 原说明 ---
If two values of quadratic characters with target `ℤ` agree after coercion into 
a ring
of characteristic not `2`, then they agree in `ℤ`.
-/
theorem IsQuadratic.eq_of_eq_coe {χ : MulChar R ℤ} (hχ : IsQuadratic χ) {χ' : MulChar R' ℤ}
    (hχ' : IsQuadratic χ') [Nontrivial R''] (hR'' : ringChar R'' ≠ 2) {a : R} {a' : R'}
    (h : (χ a : R'') = χ' a') : χ a = χ' a' :=
  Int.cast_injOn_of_ringChar_ne_two hR'' (hχ a) (hχ' a') h

/-- We can post-compose a multiplicative character with a ring homomorphism. -/
@[simps]
/-
**MulChar.ringHomComp** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：ringHomComp (χ : MulChar R R') (f : R' ->+* R'') : MulChar R R''
参数：χ : MulChar R R'；f : R' ->+* R''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can post-compose a multiplicative character with a ring homomorphism.
-/
def ringHomComp (χ : MulChar R R') (f : R' →+* R'') : MulChar R R'' :=
  { f.toMonoidHom.comp χ.toMonoidHom with
    toFun := fun a => f (χ a)
    map_nonunit' := fun a ha => by simp only [map_nonunit χ ha, map_zero] }

@[simp]
/-
**MulChar.ringHomComp_one** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：ringHomComp_one (f : R' ->+* R'') : (1 : MulChar R R').ringHomComp f = 1
参数：f : R' ->+* R''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.ringHomComp_apply`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : 
Type u_2} [inst_1 : CommRing R'] {R'' : Type u_3} [inst_2 : CommRing R'']   (χ :
 MulChar R R') …
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ringHomComp_one (f : R' →+* R'') : (1 : MulChar R R').ringHomComp f = 1 := by
  ext1
  simp only [MulChar.ringHomComp_apply, MulChar.one_apply_coe, map_one]
/-
**MulChar.ringHomComp_inv** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：ringHomComp_inv {R : Type*} [CommMonoidWithZero R] (χ : MulChar R R') (f :
 R' ->+* R'') : (χ.ringHomComp f)⁻¹ = χ⁻¹.ringHomComp f
参数：χ : MulChar R R'；f : R' ->+* R''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.inv_apply`：inv_apply {R : Type*} [CommMonoidWithZero R] (χ : Mul
Char R R') (a : R) : χ⁻¹ a = χ a⁻¹ʳ
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用定理 `MulChar.ringHomComp_apply`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : 
Type u_2} [inst_1 : CommRing R'] {R'' : Type u_3} [inst_2 : CommRing R'']   (χ :
 MulChar R R') …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ringHomComp_inv {R : Type*} [CommMonoidWithZero R] (χ : MulChar R R') (f : R' →+* R'') :
    (χ.ringHomComp f)⁻¹ = χ⁻¹.ringHomComp f := by
  ext1
  simp only [inv_apply, Ring.inverse_unit, ringHomComp_apply]
/-
**MulChar.ringHomComp_mul** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：ringHomComp_mul (χ φ : MulChar R R') (f : R' ->+* R'') : (χ * φ).ringHomCo
mp f = χ.ringHomComp f * φ.ringHomComp f
参数：χ φ : MulChar R R'；f : R' ->+* R''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.ringHomComp_apply`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : 
Type u_2} [inst_1 : CommRing R'] {R'' : Type u_3} [inst_2 : CommRing R'']   (χ :
 MulChar R R') …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ringHomComp_mul (χ φ : MulChar R R') (f : R' →+* R'') :
    (χ * φ).ringHomComp f = χ.ringHomComp f * φ.ringHomComp f := by
  ext1
  simp only [ringHomComp_apply, coeToFun_mul, Pi.mul_apply, map_mul]
/-
**MulChar.ringHomComp_pow** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：ringHomComp_pow (χ : MulChar R R') (f : R' ->+* R'') (n : Nat) : χ.ringHom
Comp f ^ n = (χ ^ n).ringHomComp f
参数：χ : MulChar R R'；f : R' ->+* R''；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MulChar.ringHomComp_one`：ringHomComp_one (f : R' ->+* R'') : (1 : MulCha
r R R').ringHomComp f = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `MulChar.ringHomComp_mul`：ringHomComp_mul (χ φ : MulChar R R') (f : R' ->
+* R'') : (χ * φ).ringHomComp f = χ.ringHomComp f * φ.ringHomComp f
-/
lemma ringHomComp_pow (χ : MulChar R R') (f : R' →+* R'') (n : ℕ) :
    χ.ringHomComp f ^ n = (χ ^ n).ringHomComp f := by
  induction n with
  | zero => simp only [pow_zero, ringHomComp_one]
  | succ n ih => simp only [pow_succ, ih, ringHomComp_mul]

/-- Bundled version of `MulChar.ringHomComp` as a `MonoidHom`. -/
@[simps]
/-
**MulChar.ringHomCompHom** 是 Mathlib 中的一个定义，位于命名空间 `MulChar`。
形式化陈述：ringHomCompHom (f : R' ->+* R'') : MulChar R R' ->* MulChar R R'' where to
Fun χ
参数：f : R' ->+* R''。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `MulChar.ringHomComp_one`：ringHomComp_one (f : R' ->+* R'') : (1 : MulCha
r R R').ringHomComp f = 1
· 使用引理 `MulChar.ringHomComp_mul`：ringHomComp_mul (χ φ : MulChar R R') (f : R' ->
+* R'') : (χ * φ).ringHomComp f = χ.ringHomComp f * φ.ringHomComp f

--- 原说明 ---
Bundled version of `MulChar.ringHomComp` as a `MonoidHom`.
-/
def ringHomCompHom (f : R' →+* R'') : MulChar R R' →* MulChar R R'' where
  toFun χ := χ.ringHomComp f
  map_one' := ringHomComp_one f
  map_mul' _ _ := ringHomComp_mul _ _ f
/-
**MulChar.ringHomComp_zpow** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：ringHomComp_zpow (χ : MulChar R R') (f : R' ->+* R'') (n : Int) : χ.ringHo
mComp f ^ n = (χ ^ n).ringHomComp f
参数：χ : MulChar R R'；f : R' ->+* R''；n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
-/
lemma ringHomComp_zpow (χ : MulChar R R') (f : R' →+* R'') (n : ℤ) :
    χ.ringHomComp f ^ n = (χ ^ n).ringHomComp f :=
  ((ringHomCompHom f).map_zpow χ n).symm

/-- If `a` is a unit and `n : ℤ`, then `(χ ^ n) a = χ (a ^ n)`. -/
/-
**MulChar.zpow_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：zpow_apply_coe {R : Type*} [CommGroupWithZero R] {R' : Type*} [CommRing R'
] (χ : MulChar R R') (n : Int) (a : Rˣ) : (χ ^ n) a = χ (a ^ n : Rˣ)
参数：χ : MulChar R R'；n : Int；a : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `MulChar.pow_apply_coe`：pow_apply_coe (χ : MulChar R R') (n : Nat) (a : R
ˣ) : (χ ^ n) a = χ a ^ n
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `MulChar.inv_apply'`：inv_apply' {R : Type*} [CommGroupWithZero R] (χ : Mu
lChar R R') (a : R) : χ⁻¹ a = χ a⁻¹
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹

--- 原说明 ---
If `a` is a unit and `n : ℤ`, then `(χ ^ n) a = χ (a ^ n)`.
-/
theorem zpow_apply_coe {R : Type*} [CommGroupWithZero R] {R' : Type*} [CommRing R']
    (χ : MulChar R R') (n : ℤ) (a : Rˣ) : (χ ^ n) a = χ (a ^ n : Rˣ) := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp [pow_apply_coe]
  · simp [pow_apply_coe, inv_apply', ← inv_pow]
/-
**MulChar.injective_ringHomComp** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：injective_ringHomComp {f : R' ->+* R''} (hf : Function.Injective f) : Func
tion.Injective (ringHomComp (R
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma injective_ringHomComp {f : R' →+* R''} (hf : Function.Injective f) :
    Function.Injective (ringHomComp (R := R) · f) := by
  simpa
    only [Function.Injective, MulChar.ext_iff, ringHomComp, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    using fun χ χ' h a ↦ hf (h a)
/-
**MulChar.ringHomComp_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：ringHomComp_eq_one_iff {f : R' ->+* R''} (hf : Function.Injective f) {χ : 
MulChar R R'} : χ.ringHomComp f = 1 ↔ χ = 1
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `MulChar.ringHomComp_one`：ringHomComp_one (f : R' ->+* R'') : (1 : MulCha
r R R').ringHomComp f = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `MulChar.injective_ringHomComp`：injective_ringHomComp {f : R' ->+* R''} (
hf : Function.Injective f) : Function.Injective (ringHomComp (R
-/
lemma ringHomComp_eq_one_iff {f : R' →+* R''} (hf : Function.Injective f) {χ : MulChar R R'} :
    χ.ringHomComp f = 1 ↔ χ = 1 := by
  conv_lhs => rw [← (show (1 : MulChar R R').ringHomComp f = 1 by simp)]
  exact (injective_ringHomComp hf).eq_iff
/-
**MulChar.ringHomComp_ne_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：ringHomComp_ne_one_iff {f : R' ->+* R''} (hf : Function.Injective f) {χ : 
MulChar R R'} : χ.ringHomComp f != 1 ↔ χ != 1
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `MulChar.ringHomComp_eq_one_iff`：ringHomComp_eq_one_iff {f : R' ->+* R''}
 (hf : Function.Injective f) {χ : MulChar R R'} : χ.ringHomComp f = 1 ↔ χ = 1
-/
lemma ringHomComp_ne_one_iff {f : R' →+* R''} (hf : Function.Injective f) {χ : MulChar R R'} :
    χ.ringHomComp f ≠ 1 ↔ χ ≠ 1 :=
  (ringHomComp_eq_one_iff hf).not

/-- Composition with a ring homomorphism preserves the property of being a quadratic character. -/
/-
**MulChar.IsQuadratic.comp** 是 Mathlib 中的一个定理，位于命名空间 `MulChar.IsQuadratic`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} [inst_1 : CommRing 
R'] {R'' : Type u_3} [inst_2 : CommRing R'']   {χ : MulChar R R'}, χ.IsQuadratic
 → ∀ (f : R' →+* R''), (χ.ringHomComp f).IsQuadratic
参数：f : R' →+* R''；χ.ringHomComp f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulChar.ringHomComp_apply`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : 
Type u_2} [inst_1 : CommRing R'] {R'' : Type u_3} [inst_2 : CommRing R'']   (χ :
 MulChar R R') …
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
Composition with a ring homomorphism preserves the property of being a quadratic
 character.
-/
theorem IsQuadratic.comp {χ : MulChar R R'} (hχ : χ.IsQuadratic) (f : R' →+* R'') :
    (χ.ringHomComp f).IsQuadratic := by
  intro a
  rcases hχ a with (ha | ha | ha) <;> simp [ha]

/-- The inverse of a quadratic character is itself. → -/
/-
**MulChar.IsQuadratic.inv** 是 Mathlib 中的一个定理，位于命名空间 `MulChar.IsQuadratic`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} [inst_1 : CommRing 
R'] {χ : MulChar R R'},   χ.IsQuadratic → χ⁻¹ = χ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.inv_apply_eq_inv`：inv_apply_eq_inv (χ : MulChar R R') (a : R) : 
χ⁻¹ a = (χ a)⁻¹ʳ
· 使用定理 `Ring.inverse_zero`：inverse_zero : (0 : M₀)⁻¹ʳ = 0
· 使用定理 `Ring.inverse_one`：inverse_one : (1 : M₀)⁻¹ʳ = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1

--- 原说明 ---
The inverse of a quadratic character is itself. →
-/
theorem IsQuadratic.inv {χ : MulChar R R'} (hχ : χ.IsQuadratic) : χ⁻¹ = χ := by
  ext x
  rw [inv_apply_eq_inv]
  rcases hχ x with (h₀ | h₁ | h₂)
  · rw [h₀, Ring.inverse_zero]
  · rw [h₁, Ring.inverse_one]
  · -- Porting note (#11573): was `by norm_cast`
    have : (-1 : R') = (-1 : R'ˣ) := by norm_cast; simp
    rw [h₂, this, Ring.inverse_unit (-1 : R'ˣ), inv_neg, inv_one]

/-- The square of a quadratic character is the trivial character. -/
/-
**MulChar.IsQuadratic.sq_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MulChar.IsQuadratic`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} [inst_1 : CommRing 
R'] {χ : MulChar R R'},   χ.IsQuadratic → χ ^ 2 = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `MulChar.IsQuadratic.inv`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Ty
pe u_2} [inst_1 : CommRing R'] {χ : MulChar R R'},   χ.IsQuadratic → χ⁻¹ = χ

--- 原说明 ---
The square of a quadratic character is the trivial character.
-/
theorem IsQuadratic.sq_eq_one {χ : MulChar R R'} (hχ : χ.IsQuadratic) : χ ^ 2 = 1 := by
  rw [← inv_mul_cancel χ, pow_two, hχ.inv]

/-- The `p`th power of a quadratic character is itself, when `p` is the (prime) characteristic
of the target ring. -/
/-
**MulChar.IsQuadratic.pow_char** 是 Mathlib 中的一个定理，位于命名空间 `MulChar.IsQuadratic`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} [inst_1 : CommRing 
R'] {χ : MulChar R R'},   χ.IsQuadratic → ∀ (p : ℕ) [hp : Fact (Nat.Prime p)] [C
harP R' p], χ ^ p = χ
参数：p : ℕ；Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.pow_apply_coe`：pow_apply_coe (χ : MulChar R R') (n : Nat) (a : R
ˣ) : (χ ^ n) a = χ a ^ n
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `neg_one_pow_char`：neg_one_pow_char : (-1 : R) ^ p = -1

--- 原说明 ---
The `p`th power of a quadratic character is itself, when `p` is the (prime) char
acteristic
of the target ring.
-/
theorem IsQuadratic.pow_char {χ : MulChar R R'} (hχ : χ.IsQuadratic) (p : ℕ) [hp : Fact p.Prime]
    [CharP R' p] : χ ^ p = χ := by
  ext x
  rw [pow_apply_coe]
  rcases hχ x with (hx | hx | hx) <;> rw [hx]
  · rw [zero_pow (@Fact.out p.Prime).ne_zero]
  · rw [one_pow]
  · exact neg_one_pow_char R' p

/-- The `n`th power of a quadratic character is the trivial character, when `n` is even. -/
/-
**MulChar.IsQuadratic.pow_even** 是 Mathlib 中的一个定理，位于命名空间 `MulChar.IsQuadratic`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} [inst_1 : CommRing 
R'] {χ : MulChar R R'},   χ.IsQuadratic → ∀ {n : ℕ}, Even n → χ ^ n = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `even_iff_two_dvd`：even_iff_two_dvd : Even a ↔ 2 ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `MulChar.IsQuadratic.sq_eq_one`：∀ {R : Type u_1} [inst : CommMonoid R] {R
' : Type u_2} [inst_1 : CommRing R'] {χ : MulChar R R'},   χ.IsQuadratic → χ ^ 2
 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The `n`th power of a quadratic character is the trivial character, when `n` is e
ven.
-/
theorem IsQuadratic.pow_even {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : ℕ} (hn : Even n) :
    χ ^ n = 1 := by
  obtain ⟨n, rfl⟩ := even_iff_two_dvd.mp hn
  rw [pow_mul, hχ.sq_eq_one, one_pow]

/-- The `n`th power of a quadratic character is itself, when `n` is odd. -/
/-
**MulChar.IsQuadratic.pow_odd** 是 Mathlib 中的一个定理，位于命名空间 `MulChar.IsQuadratic`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} [inst_1 : CommRing 
R'] {χ : MulChar R R'},   χ.IsQuadratic → ∀ {n : ℕ}, Odd n → χ ^ n = χ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MulChar.IsQuadratic.pow_even`：∀ {R : Type u_1} [inst : CommMonoid R] {R'
 : Type u_2} [inst_1 : CommRing R'] {χ : MulChar R R'},   χ.IsQuadratic → ∀ {n :
 ℕ}, Even n → χ ^ …
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The `n`th power of a quadratic character is itself, when `n` is odd.
-/
theorem IsQuadratic.pow_odd {χ : MulChar R R'} (hχ : χ.IsQuadratic) {n : ℕ} (hn : Odd n) :
    χ ^ n = χ := by
  obtain ⟨n, rfl⟩ := hn
  rw [pow_add, pow_one, hχ.pow_even (even_two_mul _), one_mul]

/-- A multiplicative character `χ` into an integral domain is quadratic
if and only if `χ^2 = 1`. -/
/-
**MulChar.isQuadratic_iff_sq_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：isQuadratic_iff_sq_eq_one {M R : Type*} [CommMonoid M] [CommRing R] [NoZer
oDivisors R] [Nontrivial R] {χ : MulChar M R} : IsQuadratic χ ↔ χ ^ 2 = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1
· 使用定理 `MulChar.pow_apply_coe`：pow_apply_coe (χ : MulChar R R') (n : Nat) (a : R
ˣ) : (χ ^ n) a = χ a ^ n
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulChar.pow_apply'`：pow_apply' (χ : MulChar R R') {n : Nat} (hn : n != 0
) (a : R) : (χ ^ n) a = χ a ^ n
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用引理 `MulChar.one_apply`：one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R'
) x = 1
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0

--- 原说明 ---
A multiplicative character `χ` into an integral domain is quadratic
if and only if `χ^2 = 1`.
-/
lemma isQuadratic_iff_sq_eq_one {M R : Type*} [CommMonoid M] [CommRing R] [NoZeroDivisors R]
    [Nontrivial R] {χ : MulChar M R} :
    IsQuadratic χ ↔ χ ^ 2 = 1 := by
  refine ⟨fun h ↦ ext (fun x ↦ ?_), fun h x ↦ ?_⟩
  · rw [one_apply_coe, χ.pow_apply_coe]
    rcases h x with H | H | H
    · exact (not_isUnit_zero <| H ▸ IsUnit.map χ <| x.isUnit).elim
    · simp only [H, one_pow]
    · simp only [H, even_two, Even.neg_pow, one_pow]
  · by_cases hx : IsUnit x
    · refine .inr <| sq_eq_one_iff.mp ?_
      rw [← χ.pow_apply' two_ne_zero, h, MulChar.one_apply hx]
    · exact .inl <| map_nonunit χ hx

end quadratic_and_comp

end Properties

/-!
### Multiplicative characters with finite domain
-/

section Finite

variable {M : Type*} [CommMonoid M]
variable {R : Type*} [CommMonoidWithZero R]

/-- If `χ` is a multiplicative character on a commutative monoid `M` with finitely many units,
then `χ ^ #Mˣ = 1`. -/
/-
**MulChar.pow_card_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：∀ {M : Type u_1} [inst : CommMonoid M] {R : Type u_2} [inst_1 : CommMonoid
WithZero R] [inst_2 : Fintype Mˣ]   (χ : MulChar M R), χ ^ Fintype.card Mˣ = 1
参数：χ : MulChar M R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.pow_apply_coe`：pow_apply_coe (χ : MulChar R R') (n : Nat) (a : R
ˣ) : (χ ^ n) a = χ a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用定理 `pow_card_eq_one`：pow_card_eq_one : x ^ Fintype.card G = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Units.val_eq_one`：val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…

--- 原说明 ---
If `χ` is a multiplicative character on a commutative monoid `M` with finitely m
any units,
then `χ ^ #Mˣ = 1`.
-/
protected lemma pow_card_eq_one [Fintype Mˣ] (χ : MulChar M R) : χ ^ (Fintype.card Mˣ) = 1 := by
  ext1
  rw [pow_apply_coe, ← map_pow, one_apply_coe, ← Units.val_pow_eq_pow_val, pow_card_eq_one,
    Units.val_eq_one.mpr rfl, map_one]

/-- A multiplicative character on a commutative monoid with finitely many units
has finite (= positive) order. -/
/-
**MulChar.orderOf_pos** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：orderOf_pos [Finite Mˣ] (χ : MulChar M R) : 0 < orderOf χ
参数：χ : MulChar M R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `IsOfFinOrder.orderOf_pos`：∀ {G : Type u_1} [inst : Monoid G] {x : G}, Is
OfFinOrder x → 0 < orderOf x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `MulChar.pow_card_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M] {R : Typ
e u_2} [inst_1 : CommMonoidWithZero R] [inst_2 : Fintype Mˣ]   (χ : MulChar M R)
, χ ^ Fintype…

--- 原说明 ---
A multiplicative character on a commutative monoid with finitely many units
has finite (= positive) order.
-/
lemma orderOf_pos [Finite Mˣ] (χ : MulChar M R) : 0 < orderOf χ := by
  cases nonempty_fintype Mˣ
  apply IsOfFinOrder.orderOf_pos
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, Fintype.card_pos, χ.pow_card_eq_one⟩

end Finite

section sum

variable {R : Type*} [CommMonoid R] [Fintype R] {R' : Type*} [CommRing R']

/-- The sum over all values of a nontrivial multiplicative character on a finite ring is zero
(when the target is a domain). -/
/-
**MulChar.sum_eq_zero_of_ne_one** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：sum_eq_zero_of_ne_one [IsDomain R'] {χ : MulChar R R'} (hχ : χ != 1) : ∑ a
, χ a = 0
参数：hχ : χ != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `MulChar.ne_one_iff`：ne_one_iff {χ : MulChar R R'} : χ != 1 ↔ exists a : 
Rˣ, χ a != 1
· 使用定理 `eq_zero_of_mul_eq_self_left`：eq_zero_of_mul_eq_self_left [IsRightCancelM
ulZero M₀] (h₁ : b != 1) (h₂ : b * a = a) : a = 0
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `Function.Bijective.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u
_3} [inst : Fintype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   {e : ι 
→ κ}, Function.Bi…
· 使用定理 `Units.mulLeft_bijective`：mulLeft_bijective (a : Mˣ) : Function.Bijective
 ((a * ·) : M -> M)

--- 原说明 ---
The sum over all values of a nontrivial multiplicative character on a finite rin
g is zero
(when the target is a domain).
-/
theorem sum_eq_zero_of_ne_one [IsDomain R'] {χ : MulChar R R'} (hχ : χ ≠ 1) : ∑ a, χ a = 0 := by
  rcases ne_one_iff.mp hχ with ⟨b, hb⟩
  refine eq_zero_of_mul_eq_self_left hb ?_
  simpa only [Finset.mul_sum, ← map_mul] using b.mulLeft_bijective.sum_comp _

/-- The sum over all values of the trivial multiplicative character on a finite ring is
the cardinality of its unit group. -/
/-
**MulChar.sum_one_eq_card_units** 是 Mathlib 中的一个定理，位于命名空间 `MulChar`。
形式化陈述：sum_one_eq_card_units [DecidableEq R] : (∑ a, (1 : MulChar R R') a) = Fint
ype.card Rˣ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s

--- 原说明 ---
The sum over all values of the trivial multiplicative character on a finite ring
 is
the cardinality of its unit group.
-/
theorem sum_one_eq_card_units [DecidableEq R] :
    (∑ a, (1 : MulChar R R') a) = Fintype.card Rˣ := by
  calc
    (∑ a, (1 : MulChar R R') a) = ∑ a : R, if IsUnit a then 1 else 0 :=
      Finset.sum_congr rfl fun a _ => ?_
    _ = ((Finset.univ : Finset R).filter IsUnit).card := Finset.sum_boole _ _
    _ = (Finset.univ.map ⟨((↑) : Rˣ → R), Units.val_injective⟩).card := ?_
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

/-- If `χ` is of odd order, then `χ(-1) = 1` -/
/-
**MulChar.val_neg_one_eq_one_of_odd_order** 是 Mathlib 中的一个引理，位于命名空间 `MulChar`。
形式化陈述：val_neg_one_eq_one_of_odd_order {χ : MulChar R R'} {n : Nat} (hn : Odd n) 
(hχ : χ ^ n = 1) : χ (-1) = 1
参数：hn : Odd n；hχ : χ ^ n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `MulChar.pow_apply'`：pow_apply' (χ : MulChar R R') {n : Nat} (hn : n != 0
) (a : R) : (χ ^ n) a = χ a ^ n
· 使用引理 `Nat.ne_of_odd_add`：ne_of_odd_add (h : Odd (m + n)) : m != n
· 使用定理 `MulChar.one_apply_coe`：one_apply_coe (a : Rˣ) : (1 : MulChar R R') a = 1

--- 原说明 ---
If `χ` is of odd order, then `χ(-1) = 1`
-/
lemma val_neg_one_eq_one_of_odd_order {χ : MulChar R R'} {n : ℕ} (hn : Odd n) (hχ : χ ^ n = 1) :
    χ (-1) = 1 := by
  rw [← hn.neg_one_pow, map_pow, ← χ.pow_apply' (Nat.ne_of_odd_add hn), hχ]
  exact MulChar.one_apply_coe (-1)

end Ring

end MulChar

