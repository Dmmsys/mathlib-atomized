/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Bounds for values of Dirichlet characters

We consider Dirichlet characters `χ` with values in a normed field `F`.

We show that `‖χ a‖ = 1` if `a` is a unit and `‖χ a‖ ≤ 1` in general.
-/

public section

variable {F : Type*} [NormedField F] {n : ℕ} (χ : DirichletCharacter F n)

namespace DirichletCharacter

/-- The value at a unit of a Dirichlet character with target a normed field has norm `1`. -/
/-
**DirichletCharacter.unit_norm_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `DirichletCharac
ter`。
形式化陈述：∀ {F : Type u_1} [inst : NormedField F] {n : ℕ} (χ : DirichletCharacter F 
n) (a : (ZMod n)ˣ), ‖χ ↑a‖ = 1
参数：χ : DirichletCharacter F n；a : (ZMod n)ˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `pow_eq_one_iff_of_nonneg`：pow_eq_one_iff_of_nonneg (ha : 0 <= a) (hn : n
 != 0) : a ^ n = 1 ↔ a = 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用引理 `Units.val_pow_eq_pow_val`：val_pow_eq_pow_val (n : Nat) : ↑(a ^ n) = (a ^
 n : α)
· 使用定理 `pow_card_eq_one'`：pow_card_eq_one' {G : Type*} [Group G] {x : G} : x ^ N
at.card G = 1
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1

--- 原说明 ---
The value at a unit of a Dirichlet character with target a normed field has norm
 `1`.
-/
@[simp] lemma unit_norm_eq_one (a : (ZMod n)ˣ) : ‖χ a‖ = 1 := by
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Nat.card_pos (α := (ZMod n)ˣ)).ne').mp ?_
  rw [← norm_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one,
    norm_one]

/-- The values of a Dirichlet character with target a normed field have norm bounded by `1`. -/
/-
**DirichletCharacter.norm_le_one** 是 Mathlib 中的一个引理，位于命名空间 `DirichletCharacter`。
形式化陈述：norm_le_one (a : ZMod n) : ‖χ a‖ <= 1
参数：a : ZMod n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `DirichletCharacter.unit_norm_eq_one`：∀ {F : Type u_1} [inst : NormedFiel
d F] {n : ℕ} (χ : DirichletCharacter F n) (a : (ZMod n)ˣ), ‖χ ↑a‖ = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulChar.map_nonunit`：map_nonunit (χ : MulChar R R') {a : R} (ha : ¬IsUni
t a) : χ a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1

--- 原说明 ---
The values of a Dirichlet character with target a normed field have norm bounded
 by `1`.
-/
lemma norm_le_one (a : ZMod n) : ‖χ a‖ ≤ 1 := by
  by_cases h : IsUnit a
  · exact (χ.unit_norm_eq_one h.unit).le
  · rw [χ.map_nonunit h, norm_zero]
    exact zero_le_one


end DirichletCharacter

