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
/-
**DirichletCharacter** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：DirichletCharacter (R : Type*) [CommMonoidWithZero R] (n : Nat)
参数：R : Type*；n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of Dirichlet characters of level `n`.
-/
abbrev DirichletCharacter (R : Type*) [CommMonoidWithZero R] (n : ℕ) := MulChar (ZMod n) R

open MulChar

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)

namespace DirichletCharacter

/-
**DirichletCharacter.toUnitHom_eq_char'** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChar
acter`。
形式化陈述：toUnitHom_eq_char' {a : ZMod n} (ha : IsUnit a) : χ a = χ.toUnitHom ha.uni
t
参数：ha : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.coe_equivToUnitHom`：coe_equivToUnitHom (χ : MulChar R R') (a : R
ˣ) : ↑(equivToUnitHom χ a) = χ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toUnitHom_eq_char' {a : ZMod n} (ha : IsUnit a) : χ a = χ.toUnitHom ha.unit := by simp
/-
**DirichletCharacter.toUnitHom_inj** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter
`。
形式化陈述：toUnitHom_inj (ψ : DirichletCharacter R n) : toUnitHom χ = toUnitHom ψ ↔ χ
 = ψ
参数：ψ : DirichletCharacter R n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toUnitHom_inj (ψ : DirichletCharacter R n) : toUnitHom χ = toUnitHom ψ ↔ χ = ψ := by simp
/-
**DirichletCharacter.eval_modulus_sub** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharac
ter`。
形式化陈述：eval_modulus_sub (x : ZMod n) : χ (n - x) = χ (-x)
参数：x : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma eval_modulus_sub (x : ZMod n) : χ (n - x) = χ (-x) := by simp
/-
**DirichletCharacter.apply_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChara
cter`。
形式化陈述：apply_ne_zero_iff [Nontrivial R] (a : Int) : χ a != 0 ↔ IsCoprime a n
参数：a : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.apply_ne_zero_iff`：apply_ne_zero_iff [Nontrivial R'] {χ : MulCha
r R R'} {a : R} : χ a != 0 ↔ IsUnit a
· 使用定理 `ZMod.coe_int_isUnit_iff_isCoprime`：coe_int_isUnit_iff_isCoprime (n : Int
) (m : Nat) : IsUnit (n : ZMod m) ↔ IsCoprime (m : Int) n
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma apply_ne_zero_iff [Nontrivial R] (a : ℤ) : χ a ≠ 0 ↔ IsCoprime a n := by
  rw [MulChar.apply_ne_zero_iff, ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm]
/-
**DirichletCharacter.apply_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChara
cter`。
形式化陈述：apply_eq_zero_iff [Nontrivial R] (a : Int) : χ a = 0 ↔ ¬ IsCoprime a n
参数：a : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `DirichletCharacter.apply_ne_zero_iff`：apply_ne_zero_iff [Nontrivial R] (
a : Int) : χ a != 0 ↔ IsCoprime a n
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma apply_eq_zero_iff [Nontrivial R] (a : ℤ) : χ a = 0 ↔ ¬ IsCoprime a n := by
  rw [← (apply_ne_zero_iff χ a).not, ne_eq, not_not]

/-!
### Changing levels
-/

/-- A function that modifies the level of a Dirichlet character to some multiple
  of its original level. -/
/-
**DirichletCharacter.changeLevel** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：changeLevel {n m : Nat} (hm : n ∣ m) : DirichletCharacter R n ->* Dirichle
tCharacter R m where toFun ψ
参数：hm : n ∣ m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function that modifies the level of a Dirichlet character to some multiple
  of its original level.
-/
noncomputable def changeLevel {n m : ℕ} (hm : n ∣ m) :
    DirichletCharacter R n →* DirichletCharacter R m where
  toFun ψ := MulChar.ofUnitHom (ψ.toUnitHom.comp (ZMod.unitsMap hm))
  map_one' := by ext; simp
  map_mul' ψ₁ ψ₂ := by ext; simp
/-
**DirichletCharacter.changeLevel_def** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharact
er`。
形式化陈述：changeLevel_def {m : Nat} (hm : n ∣ m) : changeLevel hm χ = MulChar.ofUnit
Hom (χ.toUnitHom.comp (ZMod.unitsMap hm))
参数：hm : n ∣ m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma changeLevel_def {m : ℕ} (hm : n ∣ m) :
    changeLevel hm χ = MulChar.ofUnitHom (χ.toUnitHom.comp (ZMod.unitsMap hm)) := rfl
/-
**DirichletCharacter.changeLevel_toUnitHom** 是 Mathlib 中的一个引理，位于命名空间 `DirichletC
haracter`。
形式化陈述：changeLevel_toUnitHom {m : Nat} (hm : n ∣ m) : (changeLevel hm χ).toUnitHo
m = χ.toUnitHom.comp (ZMod.unitsMap hm)
参数：hm : n ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma changeLevel_toUnitHom {m : ℕ} (hm : n ∣ m) :
    (changeLevel hm χ).toUnitHom = χ.toUnitHom.comp (ZMod.unitsMap hm) := by
  simp [changeLevel]

/-- The `changeLevel` map is injective (except in the degenerate case `m = 0`). -/
/-
**DirichletCharacter.changeLevel_injective** 是 Mathlib 中的一个引理，位于命名空间 `DirichletC
haracter`。
形式化陈述：changeLevel_injective {m : Nat} [NeZero m] (hm : n ∣ m) : Function.Injecti
ve (changeLevel (R
参数：hm : n ∣ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulChar.ext`：ext {χ χ' : MulChar R R'} (h : forall a : Rˣ, χ a = χ' a) :
 χ = χ'
· 使用定理 `ZMod.unitsMap_surjective`：unitsMap_surjective [hm : NeZero m] (h : n ∣ m
) : Function.Surjective (unitsMap h)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MulChar.equivToUnitHom_symm_coe`：equivToUnitHom_symm_coe (f : Rˣ ->* R'ˣ
) (a : Rˣ) : equivToUnitHom.symm f ↑a = f a
· 使用定理 `MulChar.coe_equivToUnitHom`：coe_equivToUnitHom (χ : MulChar R R') (a : R
ˣ) : ↑(equivToUnitHom χ a) = χ a
· 使用定理 `MulChar.ext_iff`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : Type u_2} 
[inst_1 : CommMonoidWithZero R'] {χ χ' : MulChar R R'},   χ = χ' ↔ ∀ (a : Rˣ), χ
 ↑a =…

--- 原说明 ---
The `changeLevel` map is injective (except in the degenerate case `m = 0`).
-/
lemma changeLevel_injective {m : ℕ} [NeZero m] (hm : n ∣ m) :
    Function.Injective (changeLevel (R := R) hm) := by
  intro _ _ h
  ext1 y
  obtain ⟨z, rfl⟩ := ZMod.unitsMap_surjective hm y
  rw [MulChar.ext_iff] at h
  simpa [changeLevel_def] using h z

@[simp]
/-
**DirichletCharacter.changeLevel_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Dirichlet
Character`。
形式化陈述：changeLevel_eq_one_iff {m : Nat} [NeZero m] {χ : DirichletCharacter R n} (
hm : n ∣ m) : changeLevel hm χ = 1 ↔ χ = 1
参数：hm : n ∣ m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_one_iff`：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Functio
n.Injective f) {x : M} : f x = 1 ↔ x = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `DirichletCharacter.changeLevel_injective`：changeLevel_injective {m : Nat
} [NeZero m] (hm : n ∣ m) : Function.Injective (changeLevel (R
-/
lemma changeLevel_eq_one_iff {m : ℕ} [NeZero m] {χ : DirichletCharacter R n} (hm : n ∣ m) :
    changeLevel hm χ = 1 ↔ χ = 1 :=
  map_eq_one_iff _ (changeLevel_injective hm)

@[simp]
/-
**DirichletCharacter.changeLevel_self** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharac
ter`。
形式化陈述：changeLevel_self : changeLevel (dvd_refl n) χ = χ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidHomClass.toMonoidHom.congr_simp`：∀ {M : Type u_4} {N : Type u_5} {
F : Type u_9} [inst : MulOne M] [inst_1 : MulOne N] [inst_2 : FunLike F M N]   [
inst_3 : MonoidHomClass F M…
· 使用引理 `ZMod.castHom_self`：castHom_self : ZMod.castHom dvd_rfl (ZMod n) = RingHo
m.id (ZMod n)
· 使用定理 `Units.map_id`：map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ
· 使用定理 `MonoidHom.CompTriple.comp_eq`：∀ {M : Type u_1} {N : Type u_2} {P : Type 
u_3} {inst : Monoid M} {inst_1 : Monoid N} {inst_2 : Monoid P} {φ : M →* N}   {ψ
 : N →* P} {χ : ou…
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `OneHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : One M] [
inst_1 : One N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_one' 
: toFun 1 …
· 使用定理 `MonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : MulOn
e M] [inst_1 : MulOne N] (toOneHom toOneHom_1 : OneHom M N)   (e_toOneHom : toOn
eHom = toOneH…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma changeLevel_self : changeLevel (dvd_refl n) χ = χ := by
  simp [changeLevel, ZMod.unitsMap]
/-
**DirichletCharacter.changeLevel_self_toUnitHom** 是 Mathlib 中的一个引理，位于命名空间 `Diric
hletCharacter`。
形式化陈述：changeLevel_self_toUnitHom : (changeLevel (dvd_refl n) χ).toUnitHom = χ.to
UnitHom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DirichletCharacter.changeLevel_self`：changeLevel_self : changeLevel (dvd
_refl n) χ = χ
-/
lemma changeLevel_self_toUnitHom : (changeLevel (dvd_refl n) χ).toUnitHom = χ.toUnitHom := by
  rw [changeLevel_self]
/-
**DirichletCharacter.changeLevel_trans** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChara
cter`。
形式化陈述：changeLevel_trans {m d : Nat} (hm : n ∣ m) (hd : m ∣ d) : changeLevel (dvd
_trans hm hd) χ = changeLevel hd (changeLevel hm χ)
参数：hm : n ∣ m；hd : m ∣ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用引理 `ZMod.unitsMap_comp`：unitsMap_comp {d : Nat} (hm : n ∣ m) (hd : m ∣ d) : 
(unitsMap hm).comp (unitsMap hd) = unitsMap (dvd_trans hm hd)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma changeLevel_trans {m d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    changeLevel (dvd_trans hm hd) χ = changeLevel hd (changeLevel hm χ) := by
  simp [changeLevel_def, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
/-
**DirichletCharacter.changeLevel_eq_cast_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Diric
hletCharacter`。
形式化陈述：changeLevel_eq_cast_of_dvd {m : Nat} (hm : n ∣ m) (a : Units (ZMod m)) : (
changeLevel hm χ) a = χ (ZMod.cast (a : ZMod m))
参数：hm : n ∣ m；a : Units (ZMod m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MulChar.equivToUnitHom_symm_coe`：equivToUnitHom_symm_coe (f : Rˣ ->* R'ˣ
) (a : Rˣ) : equivToUnitHom.symm f ↑a = f a
· 使用定理 `MulChar.coe_equivToUnitHom`：coe_equivToUnitHom (χ : MulChar R R') (a : R
ˣ) : ↑(equivToUnitHom χ a) = χ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma changeLevel_eq_cast_of_dvd {m : ℕ} (hm : n ∣ m) (a : Units (ZMod m)) :
    (changeLevel hm χ) a = χ (ZMod.cast (a : ZMod m)) := by
  simp [changeLevel_def, ZMod.unitsMap_val]
/-
**DirichletCharacter.changeLevel_eq_cast_of_dvd'** 是 Mathlib 中的一个引理，位于命名空间 `Diri
chletCharacter`。
形式化陈述：changeLevel_eq_cast_of_dvd' {m : Nat} (hm : n ∣ m) {a : Int} (ha : IsCopri
me a m) : changeLevel hm χ a = χ a
参数：hm : n ∣ m；ha : IsCoprime a m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.coe_unitOfIsCoprime`：coe_unitOfIsCoprime {m : Nat} (n : Int) (h : I
sCoprime n ↑m) : (unitOfIsCoprime n h : ZMod m) = n
· 使用引理 `DirichletCharacter.changeLevel_eq_cast_of_dvd`：changeLevel_eq_cast_of_dv
d {m : Nat} (hm : n ∣ m) (a : Units (ZMod m)) : (changeLevel hm χ) a = χ (ZMod.c
ast (a : ZMod m))
· 使用定理 `ZMod.cast_intCast`：cast_intCast (h : m ∣ n) (k : Int) : (cast (k : ZMod 
n) : R) = k
-/
lemma changeLevel_eq_cast_of_dvd' {m : ℕ} (hm : n ∣ m) {a : ℤ} (ha : IsCoprime a m) :
    changeLevel hm χ a = χ a := by
  rw [← ZMod.coe_unitOfIsCoprime _ ha, changeLevel_eq_cast_of_dvd _ hm, ZMod.coe_unitOfIsCoprime,
    ZMod.cast_intCast hm]

/-- `χ` of level `n` factors through a Dirichlet character `χ₀` of level `d` if `d ∣ n` and
`χ₀ = χ ∘ (ZMod n → ZMod d)`. -/
/-
**DirichletCharacter.FactorsThrough** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacte
r`。
形式化陈述：FactorsThrough (d : Nat) : Prop
参数：d : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`χ` of level `n` factors through a Dirichlet character `χ₀` of level `d` if `d ∣
 n` and
`χ₀ = χ ∘ (ZMod n → ZMod d)`.
-/
def FactorsThrough (d : ℕ) : Prop :=
  ∃ (h : d ∣ n) (χ₀ : DirichletCharacter R d), χ = changeLevel h χ₀
/-
**DirichletCharacter.changeLevel_factorsThrough** 是 Mathlib 中的一个引理，位于命名空间 `Diric
hletCharacter`。
形式化陈述：changeLevel_factorsThrough {m : Nat} (hm : n ∣ m) : FactorsThrough (change
Level hm χ) n
参数：hm : n ∣ m。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma changeLevel_factorsThrough {m : ℕ} (hm : n ∣ m) : FactorsThrough (changeLevel hm χ) n :=
  ⟨hm, χ, rfl⟩

namespace FactorsThrough

variable {χ}

/-- The fact that `d` divides `n` when `χ` factors through a Dirichlet character at level `d` -/
/-
**DirichletCharacter.FactorsThrough.dvd** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChar
acter.FactorsThrough`。
形式化陈述：dvd {d : Nat} (h : FactorsThrough χ d) : d ∣ n
参数：h : FactorsThrough χ d。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fact that `d` divides `n` when `χ` factors through a Dirichlet character at 
level `d`
-/
lemma dvd {d : ℕ} (h : FactorsThrough χ d) : d ∣ n := h.1

/-- The Dirichlet character at level `d` through which `χ` factors -/
noncomputable
/-
**DirichletCharacter.FactorsThrough.** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharact
er.FactorsThrough`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def χ₀ {d : ℕ} (h : FactorsThrough χ d) : DirichletCharacter R d := Classical.choose h.2

/-- The fact that `χ` factors through `χ₀` of level `d` -/
/-
**DirichletCharacter.FactorsThrough.eq_changeLevel** 是 Mathlib 中的一个引理，位于命名空间 `Di
richletCharacter.FactorsThrough`。
形式化陈述：eq_changeLevel {d : Nat} (h : FactorsThrough χ d) : χ = changeLevel h.dvd 
h.χ₀
参数：h : FactorsThrough χ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The fact that `χ` factors through `χ₀` of level `d`
-/
lemma eq_changeLevel {d : ℕ} (h : FactorsThrough χ d) : χ = changeLevel h.dvd h.χ₀ :=
  Classical.choose_spec h.2

/-- The character of level `d` through which `χ` factors is uniquely determined. -/
/-
**DirichletCharacter.FactorsThrough.existsUnique** 是 Mathlib 中的一个引理，位于命名空间 `Diri
chletCharacter.FactorsThrough`。
形式化陈述：existsUnique {d : Nat} [NeZero n] (h : FactorsThrough χ d) : exists! χ' : 
DirichletCharacter R d, χ = changeLevel h.dvd χ'
参数：h : FactorsThrough χ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.FactorsThrough.dvd`：dvd {d : Nat} (h : FactorsThrough
 χ d) : d ∣ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirichletCharacter.changeLevel_injective`：changeLevel_injective {m : Nat
} [NeZero m] (hm : n ∣ m) : Function.Injective (changeLevel (R

--- 原说明 ---
The character of level `d` through which `χ` factors is uniquely determined.
-/
lemma existsUnique {d : ℕ} [NeZero n] (h : FactorsThrough χ d) :
    ∃! χ' : DirichletCharacter R d, χ = changeLevel h.dvd χ' := by
  rcases h with ⟨hd, χ₂, rfl⟩
  exact ⟨χ₂, rfl, fun χ₃ hχ₃ ↦ (changeLevel_injective hd hχ₃).symm⟩

variable (χ) in
/-
**DirichletCharacter.FactorsThrough.same_level** 是 Mathlib 中的一个引理，位于命名空间 `Dirich
letCharacter.FactorsThrough`。
形式化陈述：same_level : FactorsThrough χ n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirichletCharacter.changeLevel_self`：changeLevel_self : changeLevel (dvd
_refl n) χ = χ
-/
lemma same_level : FactorsThrough χ n := ⟨dvd_refl n, χ, (changeLevel_self χ).symm⟩

end FactorsThrough

variable {χ} in
/-- A Dirichlet character `χ` factors through `d | n` iff its associated unit-group hom is trivial
on the kernel of `ZMod.unitsMap`. -/
/-
**DirichletCharacter.factorsThrough_iff_ker_unitsMap** 是 Mathlib 中的一个引理，位于命名空间 `
DirichletCharacter`。
形式化陈述：factorsThrough_iff_ker_unitsMap {d : Nat} [NeZero n] (hd : d ∣ n) : Factor
sThrough χ d ↔ (ZMod.unitsMap hd).ker <= χ.toUnitHom.ker
参数：hd : d ∣ n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用引理 `DirichletCharacter.changeLevel_toUnitHom`：changeLevel_toUnitHom {m : Nat
} (hm : n ∣ m) : (changeLevel hm χ).toUnitHom = χ.toUnitHom.comp (ZMod.unitsMap 
hm)
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `ZMod.unitsMap_surjective`：unitsMap_surjective [hm : NeZero m] (h : n ∣ m
) : Function.Surjective (unitsMap h)
· 使用定理 `MonoidHom.liftOfRightInverse_comp`：liftOfRightInverse_comp (hf : Functio
n.RightInverse f_inv f) (g : { g : G₁ ->* G₃ // f.ker <= g.ker }) : (f.liftOfRig
htInverse f_inv hf g).c…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A Dirichlet character `χ` factors through `d | n` iff its associated unit-group 
hom is trivial
on the kernel of `ZMod.unitsMap`.
-/
lemma factorsThrough_iff_ker_unitsMap {d : ℕ} [NeZero n] (hd : d ∣ n) :
    FactorsThrough χ d ↔ (ZMod.unitsMap hd).ker ≤ χ.toUnitHom.ker := by
  refine ⟨fun ⟨_, ⟨χ₀, hχ₀⟩⟩ x hx ↦ ?_, fun h ↦ ?_⟩
  · rw [MonoidHom.mem_ker, hχ₀, changeLevel_toUnitHom, MonoidHom.comp_apply, hx, map_one]
  · let E := MonoidHom.liftOfSurjective _ (ZMod.unitsMap_surjective hd) ⟨_, h⟩
    have hE : E.comp (ZMod.unitsMap hd) = χ.toUnitHom := MonoidHom.liftOfRightInverse_comp ..
    refine ⟨hd, MulChar.ofUnitHom E, equivToUnitHom.injective (?_ : toUnitHom _ = toUnitHom _)⟩
    simp_rw [changeLevel_toUnitHom, toUnitHom_eq, ofUnitHom_eq, Equiv.apply_symm_apply, hE,
      toUnitHom_eq]

/-- If `χ` factors through `d` and `d ∣ m ∣ n`, then `χ` also factors through `m`. -/
/-
**DirichletCharacter.FactorsThrough.mono** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCha
racter.FactorsThrough`。
形式化陈述：∀ {R : Type u_1} [inst : CommMonoidWithZero R] {n : ℕ} (χ : DirichletChara
cter R n) {d m : ℕ} [NeZero n],   χ.FactorsThrough d → d ∣ m → m ∣ n → χ.Factors
Through m
参数：χ : DirichletCharacter R n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DirichletCharacter.factorsThrough_iff_ker_unitsMap`：factorsThrough_iff_k
er_unitsMap {d : Nat} [NeZero n] (hd : d ∣ n) : FactorsThrough χ d ↔ (ZMod.units
Map hd).ker <= χ.toUnitHom.ker
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `DirichletCharacter.FactorsThrough.dvd`：dvd {d : Nat} (h : FactorsThrough
 χ d) : d ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ZMod.unitsMap_comp`：unitsMap_comp {d : Nat} (hm : n ∣ m) (hd : m ∣ d) : 
(unitsMap hm).comp (unitsMap hd) = unitsMap (dvd_trans hm hd)
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…

--- 原说明 ---
If `χ` factors through `d` and `d ∣ m ∣ n`, then `χ` also factors through `m`.
-/
theorem FactorsThrough.mono {d m : ℕ} [NeZero n] (hχ : FactorsThrough χ d) (hd : d ∣ m)
    (hm : m ∣ n) :
    FactorsThrough χ m := by
  refine (factorsThrough_iff_ker_unitsMap hm).mpr fun x hx ↦ ?_
  apply (factorsThrough_iff_ker_unitsMap hχ.dvd).mp hχ
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [← ZMod.unitsMap_comp hd hm, MonoidHom.comp_apply, hx, map_one]

/--
Let `χ` and `ψ` be Dirichlet characters of level `n` and `m` respectively. Assume that they agree
at level `n * m`. Then `χ` factors through `gcd(n, m)`.
-/
/-
**DirichletCharacter.factorsThrough_gcd** 是 Mathlib 中的一个定理，位于命名空间 `DirichletChar
acter`。
形式化陈述：factorsThrough_gcd {m : Nat} [NeZero n] (ψ : DirichletCharacter R m) (h : 
χ.changeLevel (n.dvd_mul_right m) = ψ.changeLevel (m.dvd_mul_left n)) : χ.Factor
sThrough (n.gcd m)
参数：ψ : DirichletCharacter R m；h : χ.changeLevel (n.dvd_mul_right m) = ψ.changeLe
vel (m.dvd_mul_left n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_mul_right`：∀ (a b : ℕ), a ∣ a * b
· 使用定理 `Nat.dvd_mul_left`：∀ (a b : ℕ), a ∣ b * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用引理 `DirichletCharacter.factorsThrough_iff_ker_unitsMap`：factorsThrough_iff_k
er_unitsMap {d : Nat} [NeZero n] (hd : d ∣ n) : FactorsThrough χ d ↔ (ZMod.units
Map hd).ker <= χ.toUnitHom.ker
· 使用定理 `MonoidHom.mem_ker`：mem_ker {f : G ->* M} {x : G} : x in f.ker ↔ f x = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `MulChar.coe_toUnitHom`：coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.t
oUnitHom a) = χ a
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用引理 `ZMod.unitsMap_val`：unitsMap_val (h : n ∣ m) (a : (ZMod m)ˣ) : ↑(unitsMap
 h a) = ((a : ZMod m).cast : ZMod n)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ZMod.cast_id'`：cast_id' : (ZMod.cast : ZMod n -> ZMod n) = id
· 使用定理 `Nat.Coprime.mul_right`：∀ {k m n : ℕ}, k.Coprime m → k.Coprime n → k.Copr
ime (m * n)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ZMod.isUnit_iff_coprime`：isUnit_iff_coprime (m n : Nat) : IsUnit (m : ZM
od n) ↔ m.Coprime n
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用引理 `DirichletCharacter.changeLevel_eq_cast_of_dvd`：changeLevel_eq_cast_of_dv
d {m : Nat} (hm : n ∣ m) (a : Units (ZMod m)) : (changeLevel hm χ) a = χ (ZMod.c
ast (a : ZMod m))
· 使用定理 `ZMod.cast_natCast`：cast_natCast (h : m ∣ n) (k : Nat) : (cast (k : ZMod 
n) : R) = k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'

--- 原说明 ---
Let `χ` and `ψ` be Dirichlet characters of level `n` and `m` respectively. Assum
e that they agree
at level `n * m`. Then `χ` factors through `gcd(n, m)`.
-/
theorem factorsThrough_gcd {m : ℕ} [NeZero n] (ψ : DirichletCharacter R m)
    (h : χ.changeLevel (n.dvd_mul_right m) = ψ.changeLevel (m.dvd_mul_left n)) :
    χ.FactorsThrough (n.gcd m) := by
  refine (factorsThrough_iff_ker_unitsMap (n.gcd_dvd_left m)).mpr fun x hx ↦
    MonoidHom.mem_ker.mpr ?_
  rw [Units.ext_iff, MulChar.coe_toUnitHom, Units.val_one]
  obtain ⟨z, hz₁, hz₂⟩ : ∃ z : ℕ, z = x.val ∧ (z : ZMod m) = 1 := by
    suffices x.val.val ≡ 1 [MOD n.gcd m] by
      obtain ⟨z, hz₁, hz₂⟩ := Nat.chineseRemainder' this
      refine ⟨z, ?_, ?_⟩
      · simpa [← ZMod.natCast_eq_natCast_iff] using hz₁
      · rwa [← ZMod.natCast_eq_natCast_iff, Nat.cast_one] at hz₂
    rwa [MonoidHom.mem_ker, Units.ext_iff, ZMod.unitsMap_val, ← ZMod.natCast_val,
      Units.val_one, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at hx
  have hz₀ : z.gcd (n * m) = 1 := by
    refine Nat.Coprime.mul_right ?_ ?_
    · exact (ZMod.isUnit_iff_coprime _ _).mp <| hz₁ ▸ x.isUnit
    · exact (ZMod.isUnit_iff_coprime _ _).mp <| hz₂ ▸ isUnit_one
  have := changeLevel_eq_cast_of_dvd χ (n.dvd_mul_right m) (ZMod.unitOfCoprime z hz₀)
  simp only [ZMod.coe_unitOfCoprime, dvd_mul_right, ZMod.cast_natCast] at this
  rw [← hz₁, ← this, h]
  have := changeLevel_eq_cast_of_dvd ψ (m.dvd_mul_left n) (ZMod.unitOfCoprime z hz₀)
  simp only [ZMod.coe_unitOfCoprime, dvd_mul_left, ZMod.cast_natCast] at this
  rw [this, hz₂, map_one]

/-!
### Edge cases
-/

/-
**DirichletCharacter.level_one** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter`。
形式化陈述：level_one (χ : DirichletCharacter R 1) : χ = 1
参数：χ : DirichletCharacter R 1。
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
· 使用定理 `Units.eq_one`：∀ {M : Type u_1} [inst : Monoid M] [Subsingleton Mˣ] (u : 
Mˣ), u = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Edge cases
-/
lemma level_one (χ : DirichletCharacter R 1) : χ = 1 := by
  ext
  simp [Units.eq_one]
/-
**DirichletCharacter.level_one'** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter`。
形式化陈述：level_one' (hn : n = 1) : χ = 1
参数：hn : n = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.level_one`：level_one (χ : DirichletCharacter R 1) : χ
 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma level_one' (hn : n = 1) : χ = 1 := by
  subst hn
  exact level_one _
/-
**DirichletCharacter.** 是 Mathlib 中的一个实例，位于命名空间 `DirichletCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Subsingleton (DirichletCharacter R 1) := by
  refine subsingleton_iff.mpr (fun χ χ' ↦ ?_)
  simp [level_one]
/-
**DirichletCharacter.** 是 Mathlib 中的一个实例，位于命名空间 `DirichletCharacter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Unique (DirichletCharacter R 1) := Unique.mk' (DirichletCharacter R 1)

/-- A Dirichlet character of modulus `≠ 1` maps `0` to `0`. -/
/-
**DirichletCharacter.map_zero'** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter`。
形式化陈述：map_zero' (hn : n != 1) : χ 0 = 0
参数：hn : n != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ZMod.nontrivial_iff`：nontrivial_iff {n : Nat} : Nontrivial (ZMod n) ↔ n 
!= 1
· 使用定理 `MulChar.map_zero`：∀ {R' : Type u_2} [inst : CommMonoidWithZero R'] {R : 
Type u_3} [inst_1 : CommMonoidWithZero R] [Nontrivial R]   (χ : MulChar R R'), χ
 0 = 0

--- 原说明 ---
A Dirichlet character of modulus `≠ 1` maps `0` to `0`.
-/
lemma map_zero' (hn : n ≠ 1) : χ 0 = 0 :=
  have := ZMod.nontrivial_iff.mpr hn; χ.map_zero
/-
**DirichletCharacter.changeLevel_one** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharact
er`。
形式化陈述：changeLevel_one {d : Nat} (h : d ∣ n) : changeLevel h (1 : DirichletCharac
ter R d) = 1
参数：h : d ∣ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma changeLevel_one {d : ℕ} (h : d ∣ n) :
    changeLevel h (1 : DirichletCharacter R d) = 1 := by
  simp
/-
**DirichletCharacter.factorsThrough_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Dirichlet
Character`。
形式化陈述：factorsThrough_one_iff : FactorsThrough χ 1 ↔ χ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DirichletCharacter.changeLevel_one`：changeLevel_one {d : Nat} (h : d ∣ n
) : changeLevel h (1 : DirichletCharacter R d) = 1
· 使用引理 `DirichletCharacter.level_one`：level_one (χ : DirichletCharacter R 1) : χ
 = 1
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
lemma factorsThrough_one_iff : FactorsThrough χ 1 ↔ χ = 1 := by
  refine ⟨fun ⟨_, χ₀, hχ₀⟩ ↦ ?_,
          fun h ↦ ⟨one_dvd n, 1, by rw [h, changeLevel_one]⟩⟩
  rwa [level_one χ₀, changeLevel_one] at hχ₀

/-!
### The conductor
-/

/-- The set of natural numbers `d` such that `χ` factors through a character of level `d`. -/
/-
**DirichletCharacter.conductorSet** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`
。
形式化陈述：conductorSet : Set Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of natural numbers `d` such that `χ` factors through a character of leve
l `d`.
-/
def conductorSet : Set ℕ := {d : ℕ | FactorsThrough χ d}
/-
**DirichletCharacter.mem_conductorSet_iff** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCh
aracter`。
形式化陈述：mem_conductorSet_iff {x : Nat} : x in conductorSet χ ↔ FactorsThrough χ x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.refl`：∀ (a : Prop), a ↔ a
-/
lemma mem_conductorSet_iff {x : ℕ} : x ∈ conductorSet χ ↔ FactorsThrough χ x := Iff.refl _
/-
**DirichletCharacter.level_mem_conductorSet** 是 Mathlib 中的一个引理，位于命名空间 `Dirichlet
Character`。
形式化陈述：level_mem_conductorSet : n in conductorSet χ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.FactorsThrough.same_level`：same_level : FactorsThroug
h χ n
-/
lemma level_mem_conductorSet : n ∈ conductorSet χ := FactorsThrough.same_level χ
/-
**DirichletCharacter.mem_conductorSet_dvd** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCh
aracter`。
形式化陈述：mem_conductorSet_dvd {x : Nat} (hx : x in conductorSet χ) : x ∣ n
参数：hx : x in conductorSet χ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.FactorsThrough.dvd`：dvd {d : Nat} (h : FactorsThrough
 χ d) : d ∣ n
-/
lemma mem_conductorSet_dvd {x : ℕ} (hx : x ∈ conductorSet χ) : x ∣ n := hx.dvd
/-
**DirichletCharacter.zero_ne_mem_conductorSet** 是 Mathlib 中的一个定理，位于命名空间 `Dirichl
etCharacter`。
形式化陈述：zero_ne_mem_conductorSet [NeZero n] : 0 ∉ χ.conductorSet
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.eq_zero_of_zero_dvd`：∀ {a : ℕ}, 0 ∣ a → a = 0
· 使用引理 `DirichletCharacter.FactorsThrough.dvd`：dvd {d : Nat} (h : FactorsThrough
 χ d) : d ∣ n
-/
theorem zero_ne_mem_conductorSet [NeZero n] : 0 ∉ χ.conductorSet :=
  fun h ↦ NeZero.ne n <| Nat.eq_zero_of_zero_dvd <| FactorsThrough.dvd h

/-- The minimum natural number level `n` through which `χ` factors. -/
/-
**DirichletCharacter.conductor** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：conductor : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimum natural number level `n` through which `χ` factors.
-/
noncomputable def conductor : ℕ := sInf (conductorSet χ)
/-
**DirichletCharacter.conductor_mem_conductorSet** 是 Mathlib 中的一个引理，位于命名空间 `Diric
hletCharacter`。
形式化陈述：conductor_mem_conductorSet : conductor χ in conductorSet χ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sInf_mem`：sInf_mem {s : Set Nat} (h : s.Nonempty) : sInf s in s
· 使用定理 `Set.nonempty_of_mem`：nonempty_of_mem {x} (h : x in s) : s.Nonempty
· 使用引理 `DirichletCharacter.level_mem_conductorSet`：level_mem_conductorSet : n in
 conductorSet χ
-/
lemma conductor_mem_conductorSet : conductor χ ∈ conductorSet χ :=
  Nat.sInf_mem (Set.nonempty_of_mem (level_mem_conductorSet χ))
/-
**DirichletCharacter.conductor_dvd_level** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCha
racter`。
形式化陈述：conductor_dvd_level : conductor χ ∣ n
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.FactorsThrough.dvd`：dvd {d : Nat} (h : FactorsThrough
 χ d) : d ∣ n
· 使用引理 `DirichletCharacter.conductor_mem_conductorSet`：conductor_mem_conductorSe
t : conductor χ in conductorSet χ
-/
lemma conductor_dvd_level : conductor χ ∣ n := (conductor_mem_conductorSet χ).dvd
/-
**DirichletCharacter.factorsThrough_conductor** 是 Mathlib 中的一个引理，位于命名空间 `Dirichl
etCharacter`。
形式化陈述：factorsThrough_conductor : FactorsThrough χ (conductor χ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.conductor_mem_conductorSet`：conductor_mem_conductorSe
t : conductor χ in conductorSet χ
-/
lemma factorsThrough_conductor : FactorsThrough χ (conductor χ) := conductor_mem_conductorSet χ
/-
**DirichletCharacter.conductor_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChara
cter`。
形式化陈述：conductor_ne_zero [NeZero n] : conductor χ != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.eq_zero_of_zero_dvd`：∀ {a : ℕ}, 0 ∣ a → a = 0
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
-/
lemma conductor_ne_zero [NeZero n] : conductor χ ≠ 0 :=
  fun h ↦ NeZero.ne n <| Nat.eq_zero_of_zero_dvd <| h ▸ conductor_dvd_level _

/-- The conductor of the trivial character is 1. -/
/-
**DirichletCharacter.conductor_one** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter
`。
形式化陈述：conductor_one [NeZero n] : conductor (1 : DirichletCharacter R n) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DirichletCharacter.factorsThrough_one_iff`：factorsThrough_one_iff : Fact
orsThrough χ 1 ↔ χ = 1
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用引理 `DirichletCharacter.mem_conductorSet_iff`：mem_conductorSet_iff {x : Nat} 
: x in conductorSet χ ↔ FactorsThrough χ x
· 使用定理 `Nat.le_antisymm`：∀ {n m : ℕ}, n ≤ m → m ≤ n → n = m
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用引理 `DirichletCharacter.conductor_ne_zero`：conductor_ne_zero [NeZero n] : con
ductor χ != 0

--- 原说明 ---
The conductor of the trivial character is 1.
-/
lemma conductor_one [NeZero n] : conductor (1 : DirichletCharacter R n) = 1 := by
  suffices FactorsThrough (1 : DirichletCharacter R n) 1 by
    have h : conductor (1 : DirichletCharacter R n) ≤ 1 :=
      Nat.sInf_le <| (mem_conductorSet_iff _).mpr this
    exact Nat.le_antisymm h (Nat.pos_of_ne_zero <| conductor_ne_zero _)
  exact (factorsThrough_one_iff _).mpr rfl

variable {χ}
/-
**DirichletCharacter.eq_one_iff_conductor_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Diri
chletCharacter`。
形式化陈述：eq_one_iff_conductor_eq_one [NeZero n] : χ = 1 ↔ conductor χ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.conductor_one`：conductor_one [NeZero n] : conductor (
1 : DirichletCharacter R n) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirichletCharacter.factorsThrough_conductor`：factorsThrough_conductor : 
FactorsThrough χ (conductor χ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `DirichletCharacter.level_one'`：level_one' (hn : n = 1) : χ = 1
· 使用引理 `DirichletCharacter.changeLevel_one`：changeLevel_one {d : Nat} (h : d ∣ n
) : changeLevel h (1 : DirichletCharacter R d) = 1
-/
lemma eq_one_iff_conductor_eq_one [NeZero n] : χ = 1 ↔ conductor χ = 1 := by
  refine ⟨fun h ↦ h ▸ conductor_one, fun hχ ↦ ?_⟩
  obtain ⟨h', χ₀, h⟩ := factorsThrough_conductor χ
  exact (level_one' χ₀ hχ ▸ h).trans <| changeLevel_one h'
/-
**DirichletCharacter.conductor_eq_zero_iff_level_eq_zero** 是 Mathlib 中的一个引理，位于命名
空间 `DirichletCharacter`。
形式化陈述：conductor_eq_zero_iff_level_eq_zero : conductor χ = 0 ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `DirichletCharacter.conductor_ne_zero`：conductor_ne_zero [NeZero n] : con
ductor χ != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.sInf_eq_zero`：sInf_eq_zero {s : Set Nat} : sInf s = 0 ↔ 0 in s ∨ s =
 ∅
· 使用引理 `DirichletCharacter.level_mem_conductorSet`：level_mem_conductorSet : n in
 conductorSet χ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma conductor_eq_zero_iff_level_eq_zero : conductor χ = 0 ↔ n = 0 := by
  refine ⟨?_, ?_⟩
  · contrapose!
    exact fun h ↦ @conductor_ne_zero _ _ _ χ ⟨h⟩
  · rintro rfl
    exact Nat.sInf_eq_zero.mpr <| Or.inl <| level_mem_conductorSet χ
/-
**DirichletCharacter.conductor_le_conductor_mem_conductorSet** 是 Mathlib 中的一个引理，
位于命名空间 `DirichletCharacter`。
形式化陈述：conductor_le_conductor_mem_conductorSet {d : Nat} (hd : d in conductorSet 
χ) : χ.conductor <= (Classical.choose hd.2).conductor
参数：hd : d in conductorSet χ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DirichletCharacter.mem_conductorSet_iff`：mem_conductorSet_iff {x : Nat} 
: x in conductorSet χ ↔ FactorsThrough χ x
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
· 使用引理 `DirichletCharacter.factorsThrough_conductor`：factorsThrough_conductor : 
FactorsThrough χ (conductor χ)
· 使用引理 `DirichletCharacter.FactorsThrough.dvd`：dvd {d : Nat} (h : FactorsThrough
 χ d) : d ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DirichletCharacter.changeLevel_trans`：changeLevel_trans {m d : Nat} (hm 
: n ∣ m) (hd : m ∣ d) : changeLevel (dvd_trans hm hd) χ = changeLevel hd (change
Level hm χ)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `DirichletCharacter.FactorsThrough.eq_changeLevel`：eq_changeLevel {d : Na
t} (h : FactorsThrough χ d) : χ = changeLevel h.dvd h.χ₀
-/
lemma conductor_le_conductor_mem_conductorSet {d : ℕ} (hd : d ∈ conductorSet χ) :
    χ.conductor ≤ (Classical.choose hd.2).conductor := by
  refine Nat.sInf_le <| (mem_conductorSet_iff χ).mpr <|
    ⟨dvd_trans (conductor_dvd_level _) hd.1,
     (factorsThrough_conductor (Classical.choose hd.2)).2.choose, ?_⟩
  rw [changeLevel_trans _ (conductor_dvd_level _) hd.dvd,
      ← (factorsThrough_conductor (Classical.choose hd.2)).2.choose_spec]
  exact hd.eq_changeLevel

variable (χ)

/-- A character is primitive if its level is equal to its conductor. -/
/-
**DirichletCharacter.IsPrimitive** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：IsPrimitive : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A character is primitive if its level is equal to its conductor.
-/
def IsPrimitive : Prop := conductor χ = n
/-
**DirichletCharacter.isPrimitive_def** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharact
er`。
形式化陈述：isPrimitive_def : IsPrimitive χ ↔ conductor χ = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isPrimitive_def : IsPrimitive χ ↔ conductor χ = n := Iff.rfl
/-
**DirichletCharacter.isPrimitive_one_level_one** 是 Mathlib 中的一个引理，位于命名空间 `Dirich
letCharacter`。
形式化陈述：isPrimitive_one_level_one : IsPrimitive (1 : DirichletCharacter R 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
-/
lemma isPrimitive_one_level_one : IsPrimitive (1 : DirichletCharacter R 1) :=
  Nat.dvd_one.mp (conductor_dvd_level _)
/-
**DirichletCharacter.isPrimitive_one_level_zero** 是 Mathlib 中的一个引理，位于命名空间 `Diric
hletCharacter`。
形式化陈述：isPrimitive_one_level_zero : IsPrimitive (1 : DirichletCharacter R 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DirichletCharacter.conductor_eq_zero_iff_level_eq_zero`：conductor_eq_zer
o_iff_level_eq_zero : conductor χ = 0 ↔ n = 0
-/
lemma isPrimitive_one_level_zero : IsPrimitive (1 : DirichletCharacter R 0) :=
  conductor_eq_zero_iff_level_eq_zero.mpr rfl
/-
**DirichletCharacter.conductor_one_dvd** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChara
cter`。
形式化陈述：conductor_one_dvd (n : Nat) : conductor (1 : DirichletCharacter R 1) ∣ n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `DirichletCharacter.isPrimitive_def`：isPrimitive_def : IsPrimitive χ ↔ co
nductor χ = n
· 使用引理 `DirichletCharacter.isPrimitive_one_level_one`：isPrimitive_one_level_one 
: IsPrimitive (1 : DirichletCharacter R 1)
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
lemma conductor_one_dvd (n : ℕ) : conductor (1 : DirichletCharacter R 1) ∣ n := by
  rw [(isPrimitive_def _).mp isPrimitive_one_level_one]
  apply one_dvd _

/-- The primitive character associated to a Dirichlet character. -/
/-
**DirichletCharacter.primitiveCharacter** 是 Mathlib 中的一个定义，位于命名空间 `DirichletChar
acter`。
形式化陈述：primitiveCharacter : DirichletCharacter R χ.conductor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The primitive character associated to a Dirichlet character.
-/
noncomputable def primitiveCharacter : DirichletCharacter R χ.conductor :=
  Classical.choose (factorsThrough_conductor χ).choose_spec
/-
**DirichletCharacter.changeLevel_primitiveCharacter** 是 Mathlib 中的一个定理，位于命名空间 `D
irichletCharacter`。
形式化陈述：changeLevel_primitiveCharacter : (changeLevel χ.conductor_dvd_level) χ.pri
mitiveCharacter = χ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirichletCharacter.factorsThrough_conductor`：factorsThrough_conductor : 
FactorsThrough χ (conductor χ)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem changeLevel_primitiveCharacter :
    (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ :=
  (factorsThrough_conductor χ).choose_spec.choose_spec.symm
/-
**DirichletCharacter.primitiveCharacter_isPrimitive** 是 Mathlib 中的一个引理，位于命名空间 `D
irichletCharacter`。
形式化陈述：primitiveCharacter_isPrimitive : IsPrimitive (χ.primitiveCharacter)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DirichletCharacter.isPrimitive_def`：isPrimitive_def : IsPrimitive χ ↔ co
nductor χ = n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DirichletCharacter.conductor_eq_zero_iff_level_eq_zero`：conductor_eq_zer
o_iff_level_eq_zero : conductor χ = 0 ↔ n = 0
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
· 使用引理 `DirichletCharacter.conductor_le_conductor_mem_conductorSet`：conductor_le
_conductor_mem_conductorSet {d : Nat} (hd : d in conductorSet χ) : χ.conductor <
= (Classical.choose hd.2).conductor
· 使用引理 `DirichletCharacter.conductor_mem_conductorSet`：conductor_mem_conductorSe
t : conductor χ in conductorSet χ
-/
lemma primitiveCharacter_isPrimitive : IsPrimitive (χ.primitiveCharacter) := by
  by_cases h : χ.conductor = 0
  · rw [isPrimitive_def]
    convert! conductor_eq_zero_iff_level_eq_zero.mpr h
  · exact le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero h) (conductor_dvd_level _)) <|
      conductor_le_conductor_mem_conductorSet <| conductor_mem_conductorSet χ
/-
**DirichletCharacter.primitiveCharacter_one** 是 Mathlib 中的一个引理，位于命名空间 `Dirichlet
Character`。
形式化陈述：primitiveCharacter_one [NeZero n] : (1 : DirichletCharacter R n).primitive
Character = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.one_ne_zero`：1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirichletCharacter.conductor_one`：conductor_one [NeZero n] : conductor (
1 : DirichletCharacter R n) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DirichletCharacter.eq_one_iff_conductor_eq_one`：eq_one_iff_conductor_eq_
one [NeZero n] : χ = 1 ↔ conductor χ = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `DirichletCharacter.isPrimitive_def`：isPrimitive_def : IsPrimitive χ ↔ co
nductor χ = n
· 使用引理 `DirichletCharacter.primitiveCharacter_isPrimitive`：primitiveCharacter_is
Primitive : IsPrimitive (χ.primitiveCharacter)
-/
lemma primitiveCharacter_one [NeZero n] : (1 : DirichletCharacter R n).primitiveCharacter = 1 := by
  have : NeZero (conductor (1 : DirichletCharacter R n)) :=
    ⟨@conductor_one R _ n _ ▸ Nat.one_ne_zero⟩
  rw [eq_one_iff_conductor_eq_one,
    (isPrimitive_def _).1 (1 : DirichletCharacter R n).primitiveCharacter_isPrimitive,
    conductor_one]
/-
**DirichletCharacter.primitiveCharacter_apply_of_isCoprime** 是 Mathlib 中的一个定理，位于
命名空间 `DirichletCharacter`。
形式化陈述：primitiveCharacter_apply_of_isCoprime {a : Int} (ha : IsCoprime a n) : χ.p
rimitiveCharacter a = χ a
参数：ha : IsCoprime a n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirichletCharacter.changeLevel_eq_cast_of_dvd'`：changeLevel_eq_cast_of_d
vd' {m : Nat} (hm : n ∣ m) {a : Int} (ha : IsCoprime a m) : changeLevel hm χ a =
 χ a
· 使用定理 `DirichletCharacter.changeLevel_primitiveCharacter`：changeLevel_primitive
Character : (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ
-/
theorem primitiveCharacter_apply_of_isCoprime {a : ℤ} (ha : IsCoprime a n) :
    χ.primitiveCharacter a = χ a := by
  rw [← changeLevel_eq_cast_of_dvd' χ.primitiveCharacter χ.conductor_dvd_level ha,
    changeLevel_primitiveCharacter]
/-
**DirichletCharacter.conductor_dvd_of_mem_conductorSet** 是 Mathlib 中的一个定理，位于命名空间
 `DirichletCharacter`。
形式化陈述：conductor_dvd_of_mem_conductorSet {d : Nat} [NeZero n] (hd : d in χ.conduc
torSet) : χ.conductor ∣ d
参数：hd : d in χ.conductorSet。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `DirichletCharacter.zero_ne_mem_conductorSet`：zero_ne_mem_conductorSet [N
eZero n] : 0 ∉ χ.conductorSet
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.dvd_mul_right`：∀ (a b : ℕ), a ∣ a * b
· 使用定理 `Nat.dvd_mul_left`：∀ (a b : ℕ), a ∣ b * a
· 使用定理 `Nat.mul_ne_zero`：∀ {n m : ℕ}, n ≠ 0 → m ≠ 0 → n * m ≠ 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `DirichletCharacter.conductor_ne_zero`：conductor_ne_zero [NeZero n] : con
ductor χ != 0
· 使用引理 `DirichletCharacter.changeLevel_injective`：changeLevel_injective {m : Nat
} [NeZero m] (hm : n ∣ m) : Function.Injective (changeLevel (R
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `DirichletCharacter.changeLevel_trans`：changeLevel_trans {m d : Nat} (hm 
: n ∣ m) (hd : m ∣ d) : changeLevel (dvd_trans hm hd) χ = changeLevel hd (change
Level hm χ)
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
· 使用定理 `DirichletCharacter.changeLevel_primitiveCharacter`：changeLevel_primitive
Character : (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ
· 使用定理 `DirichletCharacter.factorsThrough_gcd`：factorsThrough_gcd {m : Nat} [NeZ
ero n] (ψ : DirichletCharacter R m) (h : χ.changeLevel (n.dvd_mul_right m) = ψ.c
hangeLevel (m.dvd_mul_left …
· 使用定理 `Nat.dvd_trans`：∀ {a b c : ℕ}, a ∣ b → b ∣ c → a ∣ c
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Nat.lt_of_le_of_ne`：∀ {n m : ℕ}, n ≤ m → ¬n = m → n < m
· 使用定理 `Nat.gcd_le_right`：∀ {n : ℕ} (m : ℕ), 0 < n → m.gcd n ≤ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.gcd_eq_right_iff_dvd`：∀ {n m : ℕ}, n.gcd m = m ↔ m ∣ n
-/
theorem conductor_dvd_of_mem_conductorSet {d : ℕ} [NeZero n] (hd : d ∈ χ.conductorSet) :
    χ.conductor ∣ d := by
  have : NeZero d := ⟨by
    contrapose hd
    exact hd ▸ zero_ne_mem_conductorSet χ⟩
  suffices d.gcd χ.conductor ∈ χ.conductorSet by
    have : χ.conductor ≤ d.gcd χ.conductor := Nat.sInf_le this
    contrapose! this
    refine Nat.lt_of_le_of_ne ?_ (Nat.gcd_eq_right_iff_dvd.not.mpr this)
    exact Nat.gcd_le_right _ <| Nat.pos_of_ne_zero <| conductor_ne_zero χ
  obtain ⟨hd, χ₀, hχ₀⟩ := hd
  suffices (changeLevel (d.dvd_mul_right χ.conductor)) χ₀ =
      (changeLevel (χ.conductor.dvd_mul_left d)) χ.primitiveCharacter by
    obtain ⟨_, χ₁, hχ₁⟩ := factorsThrough_gcd χ₀ χ.primitiveCharacter this
    refine ⟨Nat.dvd_trans (d.gcd_dvd_left χ.conductor) hd, χ₁, ?_⟩
    rw [changeLevel_trans _ (d.gcd_dvd_left χ.conductor), ← hχ₁, hχ₀]
  have : NeZero (d * χ.conductor * n) :=
    ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne d) χ.conductor_ne_zero) (NeZero.ne n)⟩
  apply changeLevel_injective <| Nat.dvd_mul_right (d * χ.conductor) n
  rw [← changeLevel_trans, ← changeLevel_trans,
    changeLevel_trans _ hd (n.dvd_mul_left (d * χ.conductor)), ← hχ₀,
    changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level, changeLevel_primitiveCharacter]

/-- A divisor `d` of `n` belongs to the conductor set of `χ` if and only if the conductor of `χ`
divides `d`. -/
/-
**DirichletCharacter.mem_conductorSet_iff_conductor_dvd** 是 Mathlib 中的一个定理，位于命名空
间 `DirichletCharacter`。
形式化陈述：mem_conductorSet_iff_conductor_dvd {d : Nat} [NeZero n] (hd : d ∣ n) : d i
n χ.conductorSet ↔ χ.conductor ∣ d
参数：hd : d ∣ n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirichletCharacter.conductor_dvd_of_mem_conductorSet`：conductor_dvd_of_m
em_conductorSet {d : Nat} [NeZero n] (hd : d in χ.conductorSet) : χ.conductor ∣ 
d
· 使用定理 `DirichletCharacter.FactorsThrough.mono`：∀ {R : Type u_1} [inst : CommMon
oidWithZero R] {n : ℕ} (χ : DirichletCharacter R n) {d m : ℕ} [NeZero n],   χ.Fa
ctorsThrough d → d ∣ m → m ∣…
· 使用引理 `DirichletCharacter.factorsThrough_conductor`：factorsThrough_conductor : 
FactorsThrough χ (conductor χ)

--- 原说明 ---
A divisor `d` of `n` belongs to the conductor set of `χ` if and only if the cond
uctor of `χ`
divides `d`.
-/
theorem mem_conductorSet_iff_conductor_dvd {d : ℕ} [NeZero n] (hd : d ∣ n) :
    d ∈ χ.conductorSet ↔ χ.conductor ∣ d :=
  ⟨conductor_dvd_of_mem_conductorSet χ, fun h ↦ χ.factorsThrough_conductor.mono χ h hd⟩

/-- The conductor is invariant under `changeLevel`: lifting a Dirichlet character `χ` of level `n`
to a multiple level `m` does not change its conductor. -/
/-
**DirichletCharacter.conductor_changeLevel** 是 Mathlib 中的一个定理，位于命名空间 `DirichletC
haracter`。
形式化陈述：conductor_changeLevel {m : Nat} [NeZero m] (hm : n ∣ m) : (changeLevel hm 
χ).conductor = χ.conductor
参数：hm : n ∣ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirichletCharacter.conductor_dvd_of_mem_conductorSet`：conductor_dvd_of_m
em_conductorSet {d : Nat} [NeZero n] (hd : d in χ.conductorSet) : χ.conductor ∣ 
d
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用引理 `DirichletCharacter.changeLevel_trans`：changeLevel_trans {m d : Nat} (hm 
: n ∣ m) (hd : m ∣ d) : changeLevel (dvd_trans hm hd) χ = changeLevel hd (change
Level hm χ)
· 使用定理 `DirichletCharacter.changeLevel_primitiveCharacter`：changeLevel_primitive
Character : (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ
· 使用定理 `Dvd.dvd.antisymm`：∀ {α : Type u_1} [inst : CommMonoidWithZero α] [IsCanc
elMulZero α] {a b : α} [Subsingleton αˣ], a ∣ b → b ∣ a → a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `DirichletCharacter.changeLevel_injective`：changeLevel_injective {m : Nat
} [NeZero m] (hm : n ∣ m) : Function.Injective (changeLevel (R

--- 原说明 ---
The conductor is invariant under `changeLevel`: lifting a Dirichlet character `χ
` of level `n`
to a multiple level `m` does not change its conductor.
-/
theorem conductor_changeLevel {m : ℕ} [NeZero m] (hm : n ∣ m) :
    (changeLevel hm χ).conductor = χ.conductor := by
  have : NeZero n := ⟨by aesop⟩
  have h : (changeLevel hm χ).conductor ∣ χ.conductor := by
    refine conductor_dvd_of_mem_conductorSet _
      ⟨χ.conductor_dvd_level.trans hm, χ.primitiveCharacter, ?_⟩
    rw [changeLevel_trans _ χ.conductor_dvd_level, changeLevel_primitiveCharacter]
  refine h.antisymm <| conductor_dvd_of_mem_conductorSet _
    ⟨h.trans χ.conductor_dvd_level, (changeLevel hm χ).primitiveCharacter, ?_⟩
  apply changeLevel_injective hm
  rw [← changeLevel_trans, changeLevel_primitiveCharacter]

/-- The primitive character of `changeLevel hm χ` is equal to the primitive character of `χ`.
This is stated as a pointwise equality because the equality of Dirichlet characters does
not typecheck. -/
/-
**DirichletCharacter.primitiveCharacter_changeLevel_apply** 是 Mathlib 中的一个定理，位于命
名空间 `DirichletCharacter`。
形式化陈述：primitiveCharacter_changeLevel_apply [Nontrivial R] {m : Nat} [NeZero m] (
hm : n ∣ m) (χ : DirichletCharacter R n) (a : Int) : (changeLevel hm χ).primitiv
eCharacter a = χ.primitiveCharacter a
参数：hm : n ∣ m；χ : DirichletCharacter R n；a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_of_eq`：dvd_of_eq (h : a = b) : a ∣ b
· 使用定理 `DirichletCharacter.conductor_changeLevel`：conductor_changeLevel {m : Nat
} [NeZero m] (hm : n ∣ m) : (changeLevel hm χ).conductor = χ.conductor
· 使用引理 `DirichletCharacter.changeLevel_injective`：changeLevel_injective {m : Nat
} [NeZero m] (hm : n ∣ m) : Function.Injective (changeLevel (R
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirichletCharacter.changeLevel_trans`：changeLevel_trans {m d : Nat} (hm 
: n ∣ m) (hd : m ∣ d) : changeLevel (dvd_trans hm hd) χ = changeLevel hd (change
Level hm χ)
· 使用定理 `DirichletCharacter.changeLevel_primitiveCharacter`：changeLevel_primitive
Character : (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `DirichletCharacter.changeLevel_eq_cast_of_dvd'`：changeLevel_eq_cast_of_d
vd' {m : Nat} (hm : n ∣ m) {a : Int} (ha : IsCoprime a m) : changeLevel hm χ a =
 χ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DirichletCharacter.apply_eq_zero_iff`：apply_eq_zero_iff [Nontrivial R] (
a : Int) : χ a = 0 ↔ ¬ IsCoprime a n

--- 原说明 ---
The primitive character of `changeLevel hm χ` is equal to the primitive characte
r of `χ`.
This is stated as a pointwise equality because the equality of Dirichlet charact
ers does
not typecheck.
-/
theorem primitiveCharacter_changeLevel_apply [Nontrivial R] {m : ℕ} [NeZero m] (hm : n ∣ m)
    (χ : DirichletCharacter R n) (a : ℤ) :
    (changeLevel hm χ).primitiveCharacter a = χ.primitiveCharacter a := by
  by_cases ha : IsCoprime a χ.conductor
  · suffices changeLevel (dvd_of_eq <| conductor_changeLevel ..)
        (changeLevel hm χ).primitiveCharacter = χ.primitiveCharacter by
      have := DFunLike.congr_fun this (a : ZMod _)
      rwa [changeLevel_eq_cast_of_dvd' _ _ ha] at this
    apply changeLevel_injective (χ.conductor_dvd_level.trans hm)
    rw [← changeLevel_trans, changeLevel_primitiveCharacter,
      χ.primitiveCharacter.changeLevel_trans χ.conductor_dvd_level, changeLevel_primitiveCharacter]
  · rw [(apply_eq_zero_iff ..).mpr ha, (apply_eq_zero_iff ..).mpr (by rwa [conductor_changeLevel])]
/-
**DirichletCharacter.conductor_zpow_dvd** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChar
acter`。
形式化陈述：conductor_zpow_dvd (χ : DirichletCharacter R n) (m : Int) : conductor (χ ^
 m) ∣ conductor χ
参数：χ : DirichletCharacter R n；m : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DirichletCharacter.conductor_eq_zero_iff_level_eq_zero`：conductor_eq_zer
o_iff_level_eq_zero : conductor χ = 0 ↔ n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirichletCharacter.mem_conductorSet_iff_conductor_dvd`：mem_conductorSet_
iff_conductor_dvd {d : Nat} [NeZero n] (hd : d ∣ n) : d in χ.conductorSet ↔ χ.co
nductor ∣ d
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
· 使用引理 `DirichletCharacter.mem_conductorSet_iff`：mem_conductorSet_iff {x : Nat} 
: x in conductorSet χ ↔ FactorsThrough χ x
· 使用定理 `MonoidHom.map_zpow`：∀ {α : Type u_2} {β : Type u_3} [inst : Group α] [in
st_1 : DivisionMonoid β] (f : α →* β) (g : α) (n : ℤ),   f (g ^ n) = f g ^ n
· 使用定理 `DirichletCharacter.changeLevel_primitiveCharacter`：changeLevel_primitive
Character : (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ
-/
lemma conductor_zpow_dvd (χ : DirichletCharacter R n) (m : ℤ) :
    conductor (χ ^ m) ∣ conductor χ := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr]
  rw [← mem_conductorSet_iff_conductor_dvd _ χ.conductor_dvd_level, mem_conductorSet_iff]
  refine ⟨χ.conductor_dvd_level, χ.primitiveCharacter ^ m, ?_⟩
  rw [MonoidHom.map_zpow, changeLevel_primitiveCharacter]
/-
**DirichletCharacter.conductor_pow_dvd** 是 Mathlib 中的一个引理，位于命名空间 `DirichletChara
cter`。
形式化陈述：conductor_pow_dvd (χ : DirichletCharacter R n) (m : Nat) : conductor (χ ^ 
m) ∣ conductor χ
参数：χ : DirichletCharacter R n；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.conductor_zpow_dvd`：conductor_zpow_dvd (χ : Dirichlet
Character R n) (m : Int) : conductor (χ ^ m) ∣ conductor χ
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
lemma conductor_pow_dvd (χ : DirichletCharacter R n) (m : ℕ) :
    conductor (χ ^ m) ∣ conductor χ :=
  zpow_natCast χ m ▸ conductor_zpow_dvd ..

/-- The conductor of χ⁻¹ equals the conductor of χ. -/
/-
**DirichletCharacter.conductor_inv** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCharacter
`。
形式化陈述：conductor_inv (χ : DirichletCharacter R n) : χ⁻¹.conductor = χ.conductor
参数：χ : DirichletCharacter R n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `zpow_neg_one`：zpow_neg_one (x : G) : x ^ (-1 : Int) = x⁻¹
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `DirichletCharacter.conductor_zpow_dvd`：conductor_zpow_dvd (χ : Dirichlet
Character R n) (m : Int) : conductor (χ ^ m) ∣ conductor χ
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a

--- 原说明 ---
The conductor of χ⁻¹ equals the conductor of χ.
-/
theorem conductor_inv (χ : DirichletCharacter R n) :
    χ⁻¹.conductor = χ.conductor := by
  rw [← zpow_neg_one]
  refine dvd_antisymm (conductor_zpow_dvd ..) ?_
  nth_rewrite 1 [← inv_inv χ, ← zpow_neg_one, ← zpow_neg_one]
  exact conductor_zpow_dvd ..

/-- Dirichlet character associated to multiplication of Dirichlet characters,
after changing both levels to the same -/
/-
**DirichletCharacter.mul** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：mul {m : Nat} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m) 
: DirichletCharacter R (Nat.lcm n m)
参数：χ₁ : DirichletCharacter R n；χ₂ : DirichletCharacter R m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.dvd_lcm_left`：∀ (m n : ℕ), m ∣ m.lcm n
· 使用定理 `Nat.dvd_lcm_right`：∀ (m n : ℕ), n ∣ m.lcm n

--- 原说明 ---
Dirichlet character associated to multiplication of Dirichlet characters,
after changing both levels to the same
-/
noncomputable def mul {m : ℕ} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m) :
    DirichletCharacter R (Nat.lcm n m) :=
  changeLevel (Nat.dvd_lcm_left n m) χ₁ * changeLevel (Nat.dvd_lcm_right n m) χ₂

/-- Primitive character associated to multiplication of Dirichlet characters,
after changing both levels to the same -/
/-
**DirichletCharacter.primitive_mul** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter
`。
形式化陈述：primitive_mul {m : Nat} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletChara
cter R m) : DirichletCharacter R (mul χ₁ χ₂).conductor
参数：χ₁ : DirichletCharacter R n；χ₂ : DirichletCharacter R m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Primitive character associated to multiplication of Dirichlet characters,
after changing both levels to the same
-/
noncomputable def primitive_mul {m : ℕ} (χ₁ : DirichletCharacter R n)
    (χ₂ : DirichletCharacter R m) : DirichletCharacter R (mul χ₁ χ₂).conductor :=
  primitiveCharacter (mul χ₁ χ₂)
/-
**DirichletCharacter.mul_def** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter`。
形式化陈述：mul_def {n m : Nat} {χ : DirichletCharacter R n} {ψ : DirichletCharacter R
 m} : χ.primitive_mul ψ = primitiveCharacter (mul χ ψ)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_def {n m : ℕ} {χ : DirichletCharacter R n} {ψ : DirichletCharacter R m} :
    χ.primitive_mul ψ = primitiveCharacter (mul χ ψ) :=
  rfl
/-
**DirichletCharacter.primitive_mul_isPrimitive** 是 Mathlib 中的一个引理，位于命名空间 `Dirich
letCharacter`。
形式化陈述：primitive_mul_isPrimitive {m : Nat} (ψ : DirichletCharacter R m) : IsPrimi
tive (primitive_mul χ ψ)
参数：ψ : DirichletCharacter R m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirichletCharacter.primitiveCharacter_isPrimitive`：primitiveCharacter_is
Primitive : IsPrimitive (χ.primitiveCharacter)
-/
lemma primitive_mul_isPrimitive {m : ℕ} (ψ : DirichletCharacter R m) :
    IsPrimitive (primitive_mul χ ψ) :=
  primitiveCharacter_isPrimitive _

/-- The conductor of `χ * ψ` divides the lcm of the conductors of `χ` and `ψ`. -/
/-
**DirichletCharacter.conductor_mul_dvd_lcm_conductor** 是 Mathlib 中的一个定理，位于命名空间 `
DirichletCharacter`。
形式化陈述：conductor_mul_dvd_lcm_conductor (χ ψ : DirichletCharacter R n) : (χ * ψ).c
onductor ∣ χ.conductor.lcm ψ.conductor
参数：χ ψ : DirichletCharacter R n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_zero_or_neZero`：eq_zero_or_neZero (a : R) : a = 0 ∨ NeZero a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `DirichletCharacter.conductor_eq_zero_iff_level_eq_zero`：conductor_eq_zer
o_iff_level_eq_zero : conductor χ = 0 ↔ n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.lcm_self`：∀ (m : ℕ), m.lcm m = m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lcm_dvd`：∀ {m n k : ℕ}, m ∣ k → n ∣ k → m.lcm n ∣ k
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
· 使用定理 `DirichletCharacter.mem_conductorSet_iff_conductor_dvd`：mem_conductorSet_
iff_conductor_dvd {d : Nat} [NeZero n] (hd : d ∣ n) : d in χ.conductorSet ↔ χ.co
nductor ∣ d
· 使用引理 `DirichletCharacter.mem_conductorSet_iff`：mem_conductorSet_iff {x : Nat} 
: x in conductorSet χ ↔ FactorsThrough χ x
· 使用定理 `Nat.dvd_lcm_left`：∀ (m n : ℕ), m ∣ m.lcm n
· 使用定理 `Nat.dvd_lcm_right`：∀ (m n : ℕ), n ∣ m.lcm n
· 使用定理 `DirichletCharacter.mul.eq_1`：∀ {R : Type u_1} [inst : CommMonoidWithZero
 R] {n m : ℕ} (χ₁ : DirichletCharacter R n) (χ₂ : DirichletCharacter R m),   χ₁.
mul χ₂ = (Dirichl…
· 使用定理 `MonoidHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N) (a b : M), f (a * b) = f a * f b
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用引理 `DirichletCharacter.changeLevel_trans`：changeLevel_trans {m d : Nat} (hm 
: n ∣ m) (hd : m ∣ d) : changeLevel (dvd_trans hm hd) χ = changeLevel hd (change
Level hm χ)
· 使用定理 `DirichletCharacter.changeLevel_primitiveCharacter`：changeLevel_primitive
Character : (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ

--- 原说明 ---
The conductor of `χ * ψ` divides the lcm of the conductors of `χ` and `ψ`.
-/
theorem conductor_mul_dvd_lcm_conductor (χ ψ : DirichletCharacter R n) :
    (χ * ψ).conductor ∣ χ.conductor.lcm ψ.conductor := by
  obtain rfl | hn := eq_zero_or_neZero n
  · simp [conductor_eq_zero_iff_level_eq_zero.mpr]
  have h := Nat.lcm_dvd χ.conductor_dvd_level ψ.conductor_dvd_level
  rw [← mem_conductorSet_iff_conductor_dvd _ h, mem_conductorSet_iff]
  refine ⟨h, χ.primitiveCharacter.mul ψ.primitiveCharacter, ?_⟩
  rw [mul, MonoidHom.map_mul, ← changeLevel_trans, ← changeLevel_trans,
    changeLevel_primitiveCharacter, changeLevel_primitiveCharacter]

/-!
### Specific subgroups
-/

/-- The subgroup of Dirichlet characters of level `n` whose conductor is coprime to `d`. -/
/-
**DirichletCharacter.subgroupOfCoprimeConductor** 是 Mathlib 中的一个定义，位于命名空间 `Diric
hletCharacter`。
形式化陈述：subgroupOfCoprimeConductor [NeZero n] (d : Nat) : Subgroup (DirichletChara
cter R n) where carrier
参数：d : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup of Dirichlet characters of level `n` whose conductor is coprime to 
`d`.
-/
def subgroupOfCoprimeConductor [NeZero n] (d : ℕ) :
    Subgroup (DirichletCharacter R n) where
  carrier := {χ | d.Coprime χ.conductor}
  mul_mem' hχ hψ := by
    apply Nat.Coprime.of_dvd_right (conductor_mul_dvd_lcm_conductor _ _)
    exact (Nat.Coprime.mul_right hχ hψ).coprime_div_right <| Nat.gcd_dvd_mul _ _
  one_mem' := by simp [conductor_one]
  inv_mem' hχ := by rwa [Set.mem_ofPred, conductor_inv]

@[simp]
/-
**DirichletCharacter.mem_subgroupOfCoprimeConductor** 是 Mathlib 中的一个引理，位于命名空间 `D
irichletCharacter`。
形式化陈述：mem_subgroupOfCoprimeConductor [NeZero n] {d : Nat} {χ : DirichletCharacte
r R n} : χ in subgroupOfCoprimeConductor d ↔ d.Coprime χ.conductor
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_subgroupOfCoprimeConductor [NeZero n] {d : ℕ} {χ : DirichletCharacter R n} :
    χ ∈ subgroupOfCoprimeConductor d ↔ d.Coprime χ.conductor := Iff.rfl

variable (R) in
/-- The annihilator of a set `H` of units mod `n`: the subgroup of Dirichlet characters
of level `n` that send every element of `H` to `1`. -/
/-
**DirichletCharacter.annihilator** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：annihilator (H : Set (ZMod n)ˣ) : Subgroup (DirichletCharacter R n)
参数：H : Set (ZMod n)ˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The annihilator of a set `H` of units mod `n`: the subgroup of Dirichlet charact
ers
of level `n` that send every element of `H` to `1`.
-/
noncomputable def annihilator (H : Set (ZMod n)ˣ) :
    Subgroup (DirichletCharacter R n) :=
  (MulChar.domRestrictHom ((Submonoid.closure H).map (Units.coeHom (ZMod n))) _).ker
/-
**DirichletCharacter.mem_annihilator_iff_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `
DirichletCharacter`。
形式化陈述：mem_annihilator_iff_mem_closure {H : Set (ZMod n)ˣ} {χ : DirichletCharacte
r R n} : χ in annihilator R H ↔ forall x in Submonoid.closure H, χ x = 1
参数：ZMod n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulChar.domRestrictHom_apply`：∀ {R : Type u_1} [inst : CommMonoid R] {S 
: Type u_3} [inst_1 : SetLike S R] [inst_2 : SubmonoidClass S R] (T : S)   (R'' 
: Type u_4) [inst_…
· 使用引理 `Submonoid.mem_units_of_val_mem_inv_val_mem`：mem_units_of_val_mem_inv_val
_mem (S : Submonoid M) {x : Mˣ} (h₁ : (x : M) in S) (h₂ : ((x⁻¹ : Mˣ) : M) in S)
 : x in S.units
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submonoid.mem_map`：mem_map {f : F} {S : Submonoid M} {y : N} : y in S.ma
p f ↔ exists x in S, f x = y
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem mem_annihilator_iff_mem_closure {H : Set (ZMod n)ˣ} {χ : DirichletCharacter R n} :
    χ ∈ annihilator R H ↔ ∀ x ∈ Submonoid.closure H, χ x = 1 := by
  simp only [annihilator, MonoidHom.mem_ker, MulChar.domRestrictHom_apply,
    MulChar.domRestrict_eq_one_iff]
  refine ⟨fun hχ x hx ↦ ?_, fun h u ↦ ?_⟩
  · exact hχ <| (Submonoid.unitsEquivUnitsType _) <|
      ⟨x, Submonoid.mem_units_of_val_mem_inv_val_mem _ ⟨x, hx, rfl⟩
        ⟨x⁻¹, by simpa [← Subgroup.closure_toSubmonoid_of_finite] using hx, rfl⟩⟩
  · obtain ⟨y, hy, hyu⟩ := Submonoid.mem_map.mp u.val.prop
    exact hyu ▸ h _ hy

@[simp]
/-
**DirichletCharacter.mem_annihilator_iff** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCha
racter`。
形式化陈述：mem_annihilator_iff {H : Set (ZMod n)ˣ} {χ : DirichletCharacter R n} : χ i
n annihilator R H ↔ forall a in H, χ a = 1
参数：ZMod n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirichletCharacter.mem_annihilator_iff_mem_closure`：mem_annihilator_iff_
mem_closure {H : Set (ZMod n)ˣ} {χ : DirichletCharacter R n} : χ in annihilator 
R H ↔ forall x in Submonoid.closure H, χ…
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mem_annihilator_iff {H : Set (ZMod n)ˣ} {χ : DirichletCharacter R n} :
    χ ∈ annihilator R H ↔ ∀ a ∈ H, χ a = 1 := by
  rw [mem_annihilator_iff_mem_closure]
  refine ⟨fun h a ha ↦ h a (Submonoid.subset_closure ha), fun h x hx ↦ ?_⟩
  refine Submonoid.closure_induction h (by simp) (fun a b _ _ ha hb ↦ ?_) hx
  simp [map_mul, ha, hb]

variable (R n) in
/-- The subgroup of Dirichlet characters of level `n` whose primitive character sends the prime `p`
to `1`. See `mem_subgroupOfPrimitiveMapToOne_iff` for this characterization.

TODO: Generalize to an arbitrary nonzero integer `d`, replacing the hypothesis `p.Prime` with
a coprimality condition and `n / p ^ n.factorization p` with the largest factor of `n` coprime
to `d`. This would require additional Mathlib API for that construction. -/
/-
**DirichletCharacter.subgroupOfPrimitiveMapToOne** 是 Mathlib 中的一个定义，位于命名空间 `Diri
chletCharacter`。
形式化陈述：subgroupOfPrimitiveMapToOne [NeZero n] (p : Nat) [hp : Fact p.Prime] : Sub
group (DirichletCharacter R n)
参数：p : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.ordCompl_dvd`：ordCompl_dvd (n p : Nat) : ordCompl[p] n ∣ n

--- 原说明 ---
The subgroup of Dirichlet characters of level `n` whose primitive character send
s the prime `p`
to `1`. See `mem_subgroupOfPrimitiveMapToOne_iff` for this characterization.

TODO: Generalize to an arbitrary nonzero integer `d`, replacing the hypothesis `
p.Prime` with
a coprimality condition and `n / p ^ n.factorization p` with the largest factor 
of `n` coprime
to `d`. This would require additional Mathlib API for that construction.
-/
noncomputable def subgroupOfPrimitiveMapToOne [NeZero n] (p : ℕ) [hp : Fact p.Prime] :
    Subgroup (DirichletCharacter R n) :=
  (annihilator R (n := n / p ^ n.factorization p)
    {ZMod.unitOfCoprime p (Nat.coprime_ordCompl hp.out (NeZero.ne n))}).map
      (changeLevel (Nat.ordCompl_dvd n p))

@[simp]
/-
**DirichletCharacter.mem_subgroupOfPrimitiveMapToOne_iff** 是 Mathlib 中的一个定理，位于命名
空间 `DirichletCharacter`。
形式化陈述：mem_subgroupOfPrimitiveMapToOne_iff [NeZero n] [Nontrivial R] (p : Nat) [h
p : Fact p.Prime] : χ in subgroupOfPrimitiveMapToOne R n p ↔ χ.primitiveCharacte
r p = 1
参数：p : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.ordCompl_pos`：ordCompl_pos {n : Nat} (p : Nat) (hn : n != 0) : 0 < o
rdCompl[p] n
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Nat.coprime_ordCompl`：coprime_ordCompl {n p : Nat} (hp : Prime p) (hn : 
n != 0) : Coprime p (ordCompl[p] n)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.ordCompl_dvd`：ordCompl_dvd (n p : Nat) : ordCompl[p] n ∣ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `DirichletCharacter.primitiveCharacter_changeLevel_apply`：primitiveCharac
ter_changeLevel_apply [Nontrivial R] {m : Nat} [NeZero m] (hm : n ∣ m) (χ : Diri
chletCharacter R n) (a : Int) : (changeLevel …
· 使用定理 `DirichletCharacter.primitiveCharacter_apply_of_isCoprime`：primitiveChara
cter_apply_of_isCoprime {a : Int} (ha : IsCoprime a n) : χ.primitiveCharacter a 
= χ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.isCoprime_iff_coprime`：Nat.isCoprime_iff_coprime {m n : Nat} : IsCop
rime (m : Int) n ↔ Nat.Coprime m n
· 使用定理 `Nat.dvd_ordCompl_of_dvd_not_dvd`：dvd_ordCompl_of_dvd_not_dvd {p d n : Na
t} (hdn : d ∣ n) (hpd : ¬p ∣ d) : d ∣ ordCompl[p] n
· 使用引理 `DirichletCharacter.conductor_dvd_level`：conductor_dvd_level : conductor 
χ ∣ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用引理 `DirichletCharacter.apply_ne_zero_iff`：apply_ne_zero_iff [Nontrivial R] (
a : Int) : χ a != 0 ↔ IsCoprime a n
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `DirichletCharacter.changeLevel_eq_cast_of_dvd'`：changeLevel_eq_cast_of_d
vd' {m : Nat} (hm : n ∣ m) {a : Int} (ha : IsCoprime a m) : changeLevel hm χ a =
 χ a
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用引理 `DirichletCharacter.changeLevel_trans`：changeLevel_trans {m d : Nat} (hm 
: n ∣ m) (hd : m ∣ d) : changeLevel (dvd_trans hm hd) χ = changeLevel hd (change
Level hm χ)
· 使用定理 `DirichletCharacter.changeLevel_primitiveCharacter`：changeLevel_primitive
Character : (changeLevel χ.conductor_dvd_level) χ.primitiveCharacter = χ
-/
theorem mem_subgroupOfPrimitiveMapToOne_iff [NeZero n] [Nontrivial R] (p : ℕ) [hp : Fact p.Prime] :
    χ ∈ subgroupOfPrimitiveMapToOne R n p ↔ χ.primitiveCharacter p = 1 := by
  have : NeZero (n / p ^ n.factorization p) := ⟨(Nat.ordCompl_pos p (NeZero.ne n)).ne'⟩
  have hcop := Nat.coprime_ordCompl hp.out (NeZero.ne n)
  simp only [subgroupOfPrimitiveMapToOne, Subgroup.mem_map, mem_annihilator_iff,
    Set.mem_singleton_iff, forall_eq, ZMod.coe_unitOfCoprime]
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨ψ, hψ, rfl⟩
    rw [← Int.cast_natCast] at hψ ⊢
    rw [primitiveCharacter_changeLevel_apply, primitiveCharacter_apply_of_isCoprime, hψ]
    exact Nat.isCoprime_iff_coprime.mpr hcop
  · have hdvd : χ.conductor ∣ n / p ^ n.factorization p := by
      apply Nat.dvd_ordCompl_of_dvd_not_dvd χ.conductor_dvd_level
      simp [← hp.out.coprime_iff_not_dvd, ← Nat.isCoprime_iff_coprime,
        ← apply_ne_zero_iff (χ := χ.primitiveCharacter), h]
    refine ⟨changeLevel hdvd χ.primitiveCharacter, ?_, ?_⟩
    · rw [show (p : ZMod (n / p ^ n.factorization p))
          = ((p : ℤ) : ZMod (n / p ^ n.factorization p)) from (Int.cast_natCast p).symm,
        changeLevel_eq_cast_of_dvd' χ.primitiveCharacter hdvd (Nat.isCoprime_iff_coprime.mpr hcop),
        Int.cast_natCast]
      exact h
    · rw [← changeLevel_trans, changeLevel_primitiveCharacter]

/-
### Even and odd characters
-/

section CommRing

variable {S : Type*} [CommRing S] {m : ℕ} (ψ : DirichletCharacter S m)

/-- A Dirichlet character is odd if its value at -1 is -1. -/
/-
**DirichletCharacter.Odd** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：Odd : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Dirichlet character is odd if its value at -1 is -1.
-/
def Odd : Prop := ψ (-1) = -1

/-- A Dirichlet character is even if its value at -1 is 1. -/
/-
**DirichletCharacter.Even** 是 Mathlib 中的一个定义，位于命名空间 `DirichletCharacter`。
形式化陈述：Even : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Dirichlet character is even if its value at -1 is 1.
-/
def Even : Prop := ψ (-1) = 1
/-
**DirichletCharacter.even_or_odd** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter`。
形式化陈述：even_or_odd [NoZeroDivisors S] : ψ.Even ∨ ψ.Odd
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用引理 `neg_one_sq`：neg_one_sq : (-1 : R) ^ 2 = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sq_eq_one_iff`：∀ {R : Type u} [inst : Ring R] {a : R} [NoZeroDivisors R]
, a ^ 2 = 1 ↔ a = 1 ∨ a = -1
-/
lemma even_or_odd [NoZeroDivisors S] : ψ.Even ∨ ψ.Odd := by
  suffices ψ (-1) ^ 2 = 1 by convert! sq_eq_one_iff.mp this
  rw [← map_pow _, neg_one_sq, map_one]
/-
**DirichletCharacter.not_even_and_odd** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharac
ter`。
形式化陈述：not_even_and_odd [NeZero (2 : S)] : ¬(ψ.Even ∧ ψ.Odd)
参数：2 : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
-/
lemma not_even_and_odd [NeZero (2 : S)] : ¬(ψ.Even ∧ ψ.Odd) := by
  rintro ⟨(h : _ = 1), (h' : _ = -1)⟩
  simp only [h', neg_eq_iff_add_eq_zero, one_add_one_eq_two, two_ne_zero] at h
/-
**DirichletCharacter.Even.not_odd** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCharacter.
Even`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] {m : ℕ} (ψ : DirichletCharacter S m) 
[NeZero 2], ψ.Even → ¬ψ.Odd
参数：ψ : DirichletCharacter S m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用引理 `DirichletCharacter.not_even_and_odd`：not_even_and_odd [NeZero (2 : S)] :
 ¬(ψ.Even ∧ ψ.Odd)
-/
lemma Even.not_odd [NeZero (2 : S)] (hψ : Even ψ) : ¬Odd ψ :=
  not_and.mp ψ.not_even_and_odd hψ
/-
**DirichletCharacter.Odd.not_even** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCharacter.
Odd`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] {m : ℕ} (ψ : DirichletCharacter S m) 
[NeZero 2], ψ.Odd → ¬ψ.Even
参数：ψ : DirichletCharacter S m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and'`：∀ {a b : Prop}, ¬(a ∧ b) ↔ b → ¬a
· 使用引理 `DirichletCharacter.not_even_and_odd`：not_even_and_odd [NeZero (2 : S)] :
 ¬(ψ.Even ∧ ψ.Odd)
-/
lemma Odd.not_even [NeZero (2 : S)] (hψ : Odd ψ) : ¬Even ψ :=
  not_and'.mp ψ.not_even_and_odd hψ
/-
**DirichletCharacter.Odd.toUnitHom_eval_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Diric
hletCharacter.Odd`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] {m : ℕ} (ψ : DirichletCharacter S m),
 ψ.Odd → (MulChar.toUnitHom ψ) (-1) = -1
参数：ψ : DirichletCharacter S m；MulChar.toUnitHom ψ；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `MulChar.coe_toUnitHom`：coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.t
oUnitHom a) = χ a
-/
lemma Odd.toUnitHom_eval_neg_one (hψ : ψ.Odd) : ψ.toUnitHom (-1) = -1 := by
  rw [← Units.val_inj, MulChar.coe_toUnitHom]
  exact hψ
/-
**DirichletCharacter.Even.toUnitHom_eval_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Diri
chletCharacter.Even`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] {m : ℕ} (ψ : DirichletCharacter S m),
 ψ.Even → (MulChar.toUnitHom ψ) (-1) = 1
参数：ψ : DirichletCharacter S m；MulChar.toUnitHom ψ；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.val_inj`：val_inj {a b : αˣ} : (a : α) = b ↔ a = b
· 使用定理 `MulChar.coe_toUnitHom`：coe_toUnitHom (χ : MulChar R R') (a : Rˣ) : ↑(χ.t
oUnitHom a) = χ a
-/
lemma Even.toUnitHom_eval_neg_one (hψ : ψ.Even) : ψ.toUnitHom (-1) = 1 := by
  rw [← Units.val_inj, MulChar.coe_toUnitHom]
  exact hψ
/-
**DirichletCharacter.Odd.eval_neg** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCharacter.
Odd`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] {m : ℕ} (ψ : DirichletCharacter S m) 
(x : ZMod m), ψ.Odd → ψ (-x) = -ψ x
参数：ψ : DirichletCharacter S m；x : ZMod m；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirichletCharacter.Odd.eq_1`：∀ {S : Type u_2} [inst : CommRing S] {m : ℕ
} (ψ : DirichletCharacter S m), ψ.Odd = (ψ (-1) = -1)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Odd.eval_neg (x : ZMod m) (hψ : ψ.Odd) : ψ (-x) = - ψ x := by
  rw [Odd] at hψ
  rw [← neg_one_mul, map_mul]
  simp [hψ]
/-
**DirichletCharacter.Even.eval_neg** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCharacter
.Even`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] {m : ℕ} (ψ : DirichletCharacter S m) 
(x : ZMod m), ψ.Even → ψ (-x) = ψ x
参数：ψ : DirichletCharacter S m；x : ZMod m；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirichletCharacter.Even.eq_1`：∀ {S : Type u_2} [inst : CommRing S] {m : 
ℕ} (ψ : DirichletCharacter S m), ψ.Even = (ψ (-1) = 1)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Even.eval_neg (x : ZMod m) (hψ : ψ.Even) : ψ (-x) = ψ x := by
  rw [Even] at hψ
  rw [← neg_one_mul, map_mul]
  simp [hψ]

/-- An even Dirichlet character is an even function. -/
/-
**DirichletCharacter.Even.to_fun** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCharacter.E
ven`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] {m : ℕ} {χ : DirichletCharacter S m},
 χ.Even → Function.Even ⇑χ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
An even Dirichlet character is an even function.
-/
lemma Even.to_fun {χ : DirichletCharacter S m} (hχ : Even χ) : Function.Even χ :=
  fun _ ↦ by rw [← neg_one_mul, map_mul, hχ, one_mul]

/-- An odd Dirichlet character is an odd function. -/
/-
**DirichletCharacter.Odd.to_fun** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCharacter.Od
d`。
形式化陈述：∀ {S : Type u_2} [inst : CommRing S] {m : ℕ} {χ : DirichletCharacter S m},
 χ.Odd → Function.Odd ⇑χ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'

--- 原说明 ---
An odd Dirichlet character is an odd function.
-/
lemma Odd.to_fun {χ : DirichletCharacter S m} (hχ : Odd χ) : Function.Odd χ :=
  fun _ ↦ by rw [← neg_one_mul, map_mul, hχ, neg_one_mul]

end CommRing

end DirichletCharacter

