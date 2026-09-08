/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Ken Lee, Chris Hughes
-/
module

public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.Algebra.Group.Nat.Units
public import Mathlib.Algebra.GroupWithZero.Associated
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Logic.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.Ring

/-!
# Coprime elements of a ring or monoid

## Main definition

* `IsCoprime x y`: that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
  that `a * x + b * y = 1`. Note that elements with no common divisors (`IsRelPrime`) are not
  necessarily coprime, e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.
  The two notions are equivalent in Bézout rings, see `isRelPrime_iff_isCoprime`.

This file also contains lemmas about `IsRelPrime` parallel to `IsCoprime`.

See also `RingTheory.Coprime.Lemmas` for further development of coprime elements.
-/

@[expose] public section


universe u v

section CommSemiring

variable {R : Type u} [CommSemiring R] (x y z w : R)

/-- The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime. -/
@[wikidata Q104752]
/-
**IsCoprime** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCoprime : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that `x` and `y` are coprime, defined to be the existence of `a`
 and `b` such
that `a * x + b * y = 1`. Note that elements with no common divisors are not nec
essarily coprime,
e.g., the multivariate polynomials `x₁` and `x₂` are not coprime.
-/
def IsCoprime : Prop :=
  ∃ a b, a * x + b * y = 1

variable {x y z w}

@[symm]
/-
**IsCoprime.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
参数：H : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x :=
  let ⟨a, b, H⟩ := H
  ⟨b, a, by rw [add_comm, H]⟩
/-
**isCoprime_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
-/
theorem isCoprime_comm : IsCoprime x y ↔ IsCoprime y x :=
  ⟨IsCoprime.symm, IsCoprime.symm⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : @Std.Symm R IsCoprime where
  symm _ _ := .symm
/-
**isCoprime_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_self : IsCoprime x x ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_exists_inv'`：isUnit_iff_exists_inv' [Monoid M] [IsDedekindFin
iteMonoid M] {a : M} : IsUnit a ↔ exists b, b * a = 1
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem isCoprime_self : IsCoprime x x ↔ IsUnit x :=
  ⟨fun ⟨a, b, h⟩ => .of_mul_eq_one (a + b) <| by rwa [mul_comm, add_mul], fun h =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 h
    ⟨b, 0, by rwa [zero_mul, add_zero]⟩⟩
/-
**isCoprime_zero_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_zero_left : IsCoprime 0 x ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_exists_inv'`：isUnit_iff_exists_inv' [Monoid M] [IsDedekindFin
iteMonoid M] {a : M} : IsUnit a ↔ exists b, b * a = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem isCoprime_zero_left : IsCoprime 0 x ↔ IsUnit x :=
  ⟨fun ⟨a, b, H⟩ => .of_mul_eq_one b <| by rwa [mul_zero, zero_add, mul_comm] at H, fun H =>
    let ⟨b, hb⟩ := isUnit_iff_exists_inv'.1 H
    ⟨1, b, by rwa [one_mul, zero_add]⟩⟩
/-
**isCoprime_zero_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `isCoprime_zero_left`：isCoprime_zero_left : IsCoprime 0 x ↔ IsUnit x
-/
theorem isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x :=
  isCoprime_comm.trans isCoprime_zero_left
/-
**not_isCoprime_zero_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isCoprime_zero_zero [Nontrivial R] : ¬IsCoprime (0 : R) 0
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCoprime_zero_right`：isCoprime_zero_right : IsCoprime x 0 ↔ IsUnit x
· 使用定理 `not_isUnit_zero`：not_isUnit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀)
-/
theorem not_isCoprime_zero_zero [Nontrivial R] : ¬IsCoprime (0 : R) 0 :=
  mt isCoprime_zero_right.mp not_isUnit_zero
/-
**IsCoprime.intCast** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCoprime.intCast {R : Type*} [CommRing R] {a b : Int} (h : IsCoprime a b)
 : IsCoprime (a : R) (b : R)
参数：h : IsCoprime a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
-/
lemma IsCoprime.intCast {R : Type*} [CommRing R] {a b : ℤ} (h : IsCoprime a b) :
    IsCoprime (a : R) (b : R) := by
  rcases h with ⟨u, v, H⟩
  use u, v
  rw_mod_cast [H]
  exact Int.cast_one

/-- If a 2-vector `p` satisfies `IsCoprime (p 0) (p 1)`, then `p ≠ 0`. -/
/-
**IsCoprime.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.ne_zero [Nontrivial R] {p : Fin 2 -> R} (h : IsCoprime (p 0) (p 
1)) : p != 0
参数：h : IsCoprime (p 0) (p 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_isCoprime_zero_zero`：not_isCoprime_zero_zero [Nontrivial R] : ¬IsCop
rime (0 : R) 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If a 2-vector `p` satisfies `IsCoprime (p 0) (p 1)`, then `p ≠ 0`.
-/
theorem IsCoprime.ne_zero [Nontrivial R] {p : Fin 2 → R} (h : IsCoprime (p 0) (p 1)) : p ≠ 0 := by
  rintro rfl
  exact not_isCoprime_zero_zero h
/-
**IsCoprime.ne_zero_or_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.ne_zero_or_ne_zero [Nontrivial R] (h : IsCoprime x y) : x != 0 ∨
 y != 0
参数：h : IsCoprime x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_or_of_imp`：not_or_of_imp : (a -> b) -> ¬a ∨ b
· 使用定理 `not_isCoprime_zero_zero`：not_isCoprime_zero_zero [Nontrivial R] : ¬IsCop
rime (0 : R) 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsCoprime.ne_zero_or_ne_zero [Nontrivial R] (h : IsCoprime x y) : x ≠ 0 ∨ y ≠ 0 := by
  apply not_or_of_imp
  rintro rfl rfl
  exact not_isCoprime_zero_zero h
/-
**isCoprime_one_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_one_left : IsCoprime 1 x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem isCoprime_one_left : IsCoprime 1 x :=
  ⟨1, 0, by rw [one_mul, zero_mul, add_zero]⟩
/-
**isCoprime_one_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_one_right : IsCoprime x 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem isCoprime_one_right : IsCoprime x 1 :=
  ⟨0, 1, by rw [one_mul, zero_mul, zero_add]⟩
/-
**IsCoprime.dvd_of_dvd_mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.dvd_of_dvd_mul_right (H1 : IsCoprime x z) (H2 : x ∣ y * z) : x ∣
 y
参数：H1 : IsCoprime x z；H2 : x ∣ y * z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
-/
theorem IsCoprime.dvd_of_dvd_mul_right (H1 : IsCoprime x z) (H2 : x ∣ y * z) : x ∣ y := by
  let ⟨a, b, H⟩ := H1
  rw [← mul_one y, ← H, mul_add, ← mul_assoc, mul_left_comm]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)
/-
**IsCoprime.dvd_of_dvd_mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.dvd_of_dvd_mul_left (H1 : IsCoprime x y) (H2 : x ∣ y * z) : x ∣ 
z
参数：H1 : IsCoprime x y；H2 : x ∣ y * z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
-/
theorem IsCoprime.dvd_of_dvd_mul_left (H1 : IsCoprime x y) (H2 : x ∣ y * z) : x ∣ z := by
  let ⟨a, b, H⟩ := H1
  rw [← one_mul z, ← H, add_mul, mul_right_comm, mul_assoc b]
  exact dvd_add (dvd_mul_left _ _) (H2.mul_left _)
/-
**IsCoprime.mul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCoprime y z) : IsCoprime (
x * y) z
参数：H1 : IsCoprime x z；H2 : IsCoprime y z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCoprime y z) : IsCoprime (x * y) z :=
  let ⟨a, b, h1⟩ := H1
  let ⟨c, d, h2⟩ := H2
  ⟨a * c, a * x * d + b * c * y + b * d * z,
    calc a * c * (x * y) + (a * x * d + b * c * y + b * d * z) * z
      _ = (a * x + b * z) * (c * y + d * z) := by ring
      _ = 1 := by rw [h1, h2, mul_one]
      ⟩
/-
**IsCoprime.mul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.mul_right (H1 : IsCoprime x y) (H2 : IsCoprime x z) : IsCoprime 
x (y * z)
参数：H1 : IsCoprime x y；H2 : IsCoprime x z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `IsCoprime.mul_left`：IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCopr
ime y z) : IsCoprime (x * y) z
-/
theorem IsCoprime.mul_right (H1 : IsCoprime x y) (H2 : IsCoprime x z) : IsCoprime x (y * z) := by
  rw [isCoprime_comm] at H1 H2 ⊢
  exact H1.mul_left H2
/-
**IsCoprime.mul_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ 
z
参数：H : IsCoprime x y；H1 : x ∣ z；H2 : y ∣ z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Dvd.dvd.mul_left`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b : α}, a
 ∣ b → ∀ (c : α), a ∣ c * b
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
· 使用定理 `mul_dvd_mul_right`：mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c
-/
theorem IsCoprime.mul_dvd (H : IsCoprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z := by
  obtain ⟨a, b, h⟩ := H
  rw [← mul_one z, ← h, mul_add]
  apply dvd_add
  · rw [mul_comm z, mul_assoc]
    exact (mul_dvd_mul_left _ H2).mul_left _
  · rw [mul_comm b, ← mul_assoc]
    exact (mul_dvd_mul_right H1 _).mul_right _
/-
**IsCoprime.of_mul_left_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_mul_left_left (H : IsCoprime (x * y) z) : IsCoprime x z
参数：H : IsCoprime (x * y) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem IsCoprime.of_mul_left_left (H : IsCoprime (x * y) z) : IsCoprime x z :=
  let ⟨a, b, h⟩ := H
  ⟨a * y, b, by rwa [mul_right_comm, mul_assoc]⟩
/-
**IsCoprime.of_mul_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_mul_left_right (H : IsCoprime (x * y) z) : IsCoprime y z
参数：H : IsCoprime (x * y) z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_mul_left_left`：IsCoprime.of_mul_left_left (H : IsCoprime (x
 * y) z) : IsCoprime x z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsCoprime.of_mul_left_right (H : IsCoprime (x * y) z) : IsCoprime y z := by
  rw [mul_comm] at H
  exact H.of_mul_left_left
/-
**IsCoprime.of_mul_right_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_mul_right_left (H : IsCoprime x (y * z)) : IsCoprime x y
参数：H : IsCoprime x (y * z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `IsCoprime.of_mul_left_left`：IsCoprime.of_mul_left_left (H : IsCoprime (x
 * y) z) : IsCoprime x z
-/
theorem IsCoprime.of_mul_right_left (H : IsCoprime x (y * z)) : IsCoprime x y := by
  rw [isCoprime_comm] at H ⊢
  exact H.of_mul_left_left
/-
**IsCoprime.of_mul_right_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_mul_right_right (H : IsCoprime x (y * z)) : IsCoprime x z
参数：H : IsCoprime x (y * z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_mul_right_left`：IsCoprime.of_mul_right_left (H : IsCoprime 
x (y * z)) : IsCoprime x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsCoprime.of_mul_right_right (H : IsCoprime x (y * z)) : IsCoprime x z := by
  rw [mul_comm] at H
  exact H.of_mul_right_left
/-
**IsCoprime.mul_left_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.mul_left_iff : IsCoprime (x * y) z ↔ IsCoprime x z ∧ IsCoprime y
 z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_mul_left_left`：IsCoprime.of_mul_left_left (H : IsCoprime (x
 * y) z) : IsCoprime x z
· 使用定理 `IsCoprime.of_mul_left_right`：IsCoprime.of_mul_left_right (H : IsCoprime 
(x * y) z) : IsCoprime y z
· 使用定理 `IsCoprime.mul_left`：IsCoprime.mul_left (H1 : IsCoprime x z) (H2 : IsCopr
ime y z) : IsCoprime (x * y) z
-/
theorem IsCoprime.mul_left_iff : IsCoprime (x * y) z ↔ IsCoprime x z ∧ IsCoprime y z :=
  ⟨fun H => ⟨H.of_mul_left_left, H.of_mul_left_right⟩, fun ⟨H1, H2⟩ => H1.mul_left H2⟩
/-
**IsCoprime.mul_right_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.mul_right_iff : IsCoprime x (y * z) ↔ IsCoprime x y ∧ IsCoprime 
x z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `IsCoprime.mul_left_iff`：IsCoprime.mul_left_iff : IsCoprime (x * y) z ↔ I
sCoprime x z ∧ IsCoprime y z
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsCoprime.mul_right_iff : IsCoprime x (y * z) ↔ IsCoprime x y ∧ IsCoprime x z := by
  rw [isCoprime_comm, IsCoprime.mul_left_iff, isCoprime_comm, @isCoprime_comm _ _ z]
/-
**IsCoprime.of_isCoprime_of_dvd_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_isCoprime_of_dvd_left (h : IsCoprime y z) (hdvd : x ∣ y) : Is
Coprime x z
参数：h : IsCoprime y z；hdvd : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_mul_left_left`：IsCoprime.of_mul_left_left (H : IsCoprime (x
 * y) z) : IsCoprime x z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsCoprime.of_isCoprime_of_dvd_left (h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z := by
  obtain ⟨d, rfl⟩ := hdvd
  exact IsCoprime.of_mul_left_left h
/-
**IsCoprime.of_isCoprime_of_dvd_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_isCoprime_of_dvd_right (h : IsCoprime z y) (hdvd : x ∣ y) : I
sCoprime z x
参数：h : IsCoprime z y；hdvd : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `IsCoprime.of_isCoprime_of_dvd_left`：IsCoprime.of_isCoprime_of_dvd_left (
h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z
-/
theorem IsCoprime.of_isCoprime_of_dvd_right (h : IsCoprime z y) (hdvd : x ∣ y) : IsCoprime z x :=
  (h.symm.of_isCoprime_of_dvd_left hdvd).symm

@[gcongr]
/-
**IsCoprime.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.mono (h₁ : x ∣ y) (h₂ : z ∣ w) (h : IsCoprime y w) : IsCoprime x
 z
参数：h₁ : x ∣ y；h₂ : z ∣ w；h : IsCoprime y w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_isCoprime_of_dvd_right`：IsCoprime.of_isCoprime_of_dvd_right
 (h : IsCoprime z y) (hdvd : x ∣ y) : IsCoprime z x
· 使用定理 `IsCoprime.of_isCoprime_of_dvd_left`：IsCoprime.of_isCoprime_of_dvd_left (
h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z
-/
theorem IsCoprime.mono (h₁ : x ∣ y) (h₂ : z ∣ w) (h : IsCoprime y w) : IsCoprime x z :=
  h.of_isCoprime_of_dvd_left h₁ |>.of_isCoprime_of_dvd_right h₂
/-
**IsCoprime.isUnit_of_dvd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.isUnit_of_dvd (H : IsCoprime x y) (d : x ∣ y) : IsUnit x
参数：H : IsCoprime x y；d : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCoprime_self`：isCoprime_self : IsCoprime x x ↔ IsUnit x
· 使用定理 `IsCoprime.of_mul_right_left`：IsCoprime.of_mul_right_left (H : IsCoprime 
x (y * z)) : IsCoprime x y
-/
theorem IsCoprime.isUnit_of_dvd (H : IsCoprime x y) (d : x ∣ y) : IsUnit x :=
  let ⟨k, hk⟩ := d
  isCoprime_self.1 <| IsCoprime.of_mul_right_left <| show IsCoprime x (x * k) from hk ▸ H
/-
**IsCoprime.isUnit_of_associated** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.isUnit_of_associated {x y : R} (h₁ : IsCoprime x y) (h₂ : Associ
ated x y) : IsUnit x ∧ IsUnit y
参数：h₁ : IsCoprime x y；h₂ : Associated x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.isUnit_of_dvd`：IsCoprime.isUnit_of_dvd (H : IsCoprime x y) (d 
: x ∣ y) : IsUnit x
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `Associated.dvd'`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associate
d a b → b ∣ a
-/
theorem IsCoprime.isUnit_of_associated {x y : R} (h₁ : IsCoprime x y) (h₂ : Associated x y) :
    IsUnit x ∧ IsUnit y :=
  ⟨h₁.isUnit_of_dvd (h₂.dvd), h₁.symm.isUnit_of_dvd (h₂.dvd')⟩
/-
**IsCoprime.isUnit_of_dvd'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.isUnit_of_dvd' {a b x : R} (h : IsCoprime a b) (ha : x ∣ a) (hb 
: x ∣ b) : IsUnit x
参数：h : IsCoprime a b；ha : x ∣ a；hb : x ∣ b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.isUnit_of_dvd`：IsCoprime.isUnit_of_dvd (H : IsCoprime x y) (d 
: x ∣ y) : IsUnit x
· 使用定理 `IsCoprime.of_isCoprime_of_dvd_left`：IsCoprime.of_isCoprime_of_dvd_left (
h : IsCoprime y z) (hdvd : x ∣ y) : IsCoprime x z
-/
theorem IsCoprime.isUnit_of_dvd' {a b x : R} (h : IsCoprime a b) (ha : x ∣ a) (hb : x ∣ b) :
    IsUnit x :=
  (h.of_isCoprime_of_dvd_left ha).isUnit_of_dvd hb
/-
**IsCoprime.isRelPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.isRelPrime {a b : R} (h : IsCoprime a b) : IsRelPrime a b
参数：h : IsCoprime a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.isUnit_of_dvd'`：IsCoprime.isUnit_of_dvd' {a b x : R} (h : IsCo
prime a b) (ha : x ∣ a) (hb : x ∣ b) : IsUnit x
-/
theorem IsCoprime.isRelPrime {a b : R} (h : IsCoprime a b) : IsRelPrime a b :=
  fun _ ↦ h.isUnit_of_dvd'
/-
**IsCoprime.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.map (H : IsCoprime x y) {S : Type v} [CommSemiring S] (f : R ->+
* S) : IsCoprime (f x) (f y)
参数：H : IsCoprime x y；f : R ->+* S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `RingHom.map_add`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a + b) = f a + f b
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
-/
theorem IsCoprime.map (H : IsCoprime x y) {S : Type v} [CommSemiring S] (f : R →+* S) :
    IsCoprime (f x) (f y) :=
  let ⟨a, b, h⟩ := H
  ⟨f a, f b, by rw [← f.map_mul, ← f.map_mul, ← f.map_add, h, f.map_one]⟩
/-
**IsCoprime.of_add_mul_left_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_add_mul_left_left (h : IsCoprime (x + y * z) y) : IsCoprime x
 y
参数：h : IsCoprime (x + y * z) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
-/
theorem IsCoprime.of_add_mul_left_left (h : IsCoprime (x + y * z) y) : IsCoprime x y :=
  let ⟨a, b, H⟩ := h
  ⟨a, a * z + b, by
    simpa only [add_mul, mul_add, add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm,
      mul_left_comm] using H⟩
/-
**IsCoprime.of_add_mul_right_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_add_mul_right_left (h : IsCoprime (x + z * y) y) : IsCoprime 
x y
参数：h : IsCoprime (x + z * y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_left_left`：IsCoprime.of_add_mul_left_left (h : IsCo
prime (x + y * z) y) : IsCoprime x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsCoprime.of_add_mul_right_left (h : IsCoprime (x + z * y) y) : IsCoprime x y := by
  rw [mul_comm] at h
  exact h.of_add_mul_left_left
/-
**IsCoprime.of_add_mul_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_add_mul_left_right (h : IsCoprime x (y + x * z)) : IsCoprime 
x y
参数：h : IsCoprime x (y + x * z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `IsCoprime.of_add_mul_left_left`：IsCoprime.of_add_mul_left_left (h : IsCo
prime (x + y * z) y) : IsCoprime x y
-/
theorem IsCoprime.of_add_mul_left_right (h : IsCoprime x (y + x * z)) : IsCoprime x y := by
  rw [isCoprime_comm] at h ⊢
  exact h.of_add_mul_left_left
/-
**IsCoprime.of_add_mul_right_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_add_mul_right_right (h : IsCoprime x (y + z * x)) : IsCoprime
 x y
参数：h : IsCoprime x (y + z * x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_left_right`：IsCoprime.of_add_mul_left_right (h : Is
Coprime x (y + x * z)) : IsCoprime x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsCoprime.of_add_mul_right_right (h : IsCoprime x (y + z * x)) : IsCoprime x y := by
  rw [mul_comm] at h
  exact h.of_add_mul_left_right
/-
**IsCoprime.of_mul_add_left_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_mul_add_left_left (h : IsCoprime (y * z + x) y) : IsCoprime x
 y
参数：h : IsCoprime (y * z + x) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_left_left`：IsCoprime.of_add_mul_left_left (h : IsCo
prime (x + y * z) y) : IsCoprime x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsCoprime.of_mul_add_left_left (h : IsCoprime (y * z + x) y) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_left_left
/-
**IsCoprime.of_mul_add_right_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_mul_add_right_left (h : IsCoprime (z * y + x) y) : IsCoprime 
x y
参数：h : IsCoprime (z * y + x) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_right_left`：IsCoprime.of_add_mul_right_left (h : Is
Coprime (x + z * y) y) : IsCoprime x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsCoprime.of_mul_add_right_left (h : IsCoprime (z * y + x) y) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_right_left
/-
**IsCoprime.of_mul_add_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_mul_add_left_right (h : IsCoprime x (x * z + y)) : IsCoprime 
x y
参数：h : IsCoprime x (x * z + y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_left_right`：IsCoprime.of_add_mul_left_right (h : Is
Coprime x (y + x * z)) : IsCoprime x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsCoprime.of_mul_add_left_right (h : IsCoprime x (x * z + y)) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_left_right
/-
**IsCoprime.of_mul_add_right_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCoprime.of_mul_add_right_right (h : IsCoprime x (z * x + y)) : IsCoprime
 x y
参数：h : IsCoprime x (z * x + y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_right_right`：IsCoprime.of_add_mul_right_right (h : 
IsCoprime x (y + z * x)) : IsCoprime x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsCoprime.of_mul_add_right_right (h : IsCoprime x (z * x + y)) : IsCoprime x y := by
  rw [add_comm] at h
  exact h.of_add_mul_right_right
/-
**IsRelPrime.of_add_mul_left_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_add_mul_left_left (h : IsRelPrime (x + y * z) y) : IsRelPrim
e x y
参数：h : IsRelPrime (x + y * z) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
-/
theorem IsRelPrime.of_add_mul_left_left (h : IsRelPrime (x + y * z) y) : IsRelPrime x y :=
  fun _ hx hy ↦ h (dvd_add hx <| dvd_mul_of_dvd_left hy z) hy
/-
**IsRelPrime.of_add_mul_right_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_add_mul_right_left (h : IsRelPrime (x + z * y) y) : IsRelPri
me x y
参数：h : IsRelPrime (x + z * y) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_left_left`：IsRelPrime.of_add_mul_left_left (h : Is
RelPrime (x + y * z) y) : IsRelPrime x y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsRelPrime.of_add_mul_right_left (h : IsRelPrime (x + z * y) y) : IsRelPrime x y :=
  (mul_comm z y ▸ h).of_add_mul_left_left
/-
**IsRelPrime.of_add_mul_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_add_mul_left_right (h : IsRelPrime x (y + x * z)) : IsRelPri
me x y
参数：h : IsRelPrime x (y + x * z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isRelPrime_comm`：isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x
· 使用定理 `IsRelPrime.of_add_mul_left_left`：IsRelPrime.of_add_mul_left_left (h : Is
RelPrime (x + y * z) y) : IsRelPrime x y
-/
theorem IsRelPrime.of_add_mul_left_right (h : IsRelPrime x (y + x * z)) : IsRelPrime x y := by
  rw [isRelPrime_comm] at h ⊢
  exact h.of_add_mul_left_left
/-
**IsRelPrime.of_add_mul_right_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_add_mul_right_right (h : IsRelPrime x (y + z * x)) : IsRelPr
ime x y
参数：h : IsRelPrime x (y + z * x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_left_right`：IsRelPrime.of_add_mul_left_right (h : 
IsRelPrime x (y + x * z)) : IsRelPrime x y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem IsRelPrime.of_add_mul_right_right (h : IsRelPrime x (y + z * x)) : IsRelPrime x y :=
  (mul_comm z x ▸ h).of_add_mul_left_right
/-
**IsRelPrime.of_mul_add_left_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_mul_add_left_left (h : IsRelPrime (y * z + x) y) : IsRelPrim
e x y
参数：h : IsRelPrime (y * z + x) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_left_left`：IsRelPrime.of_add_mul_left_left (h : Is
RelPrime (x + y * z) y) : IsRelPrime x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsRelPrime.of_mul_add_left_left (h : IsRelPrime (y * z + x) y) : IsRelPrime x y :=
  (add_comm _ x ▸ h).of_add_mul_left_left
/-
**IsRelPrime.of_mul_add_right_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_mul_add_right_left (h : IsRelPrime (z * y + x) y) : IsRelPri
me x y
参数：h : IsRelPrime (z * y + x) y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_right_left`：IsRelPrime.of_add_mul_right_left (h : 
IsRelPrime (x + z * y) y) : IsRelPrime x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsRelPrime.of_mul_add_right_left (h : IsRelPrime (z * y + x) y) : IsRelPrime x y :=
  (add_comm _ x ▸ h).of_add_mul_right_left
/-
**IsRelPrime.of_mul_add_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_mul_add_left_right (h : IsRelPrime x (x * z + y)) : IsRelPri
me x y
参数：h : IsRelPrime x (x * z + y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_left_right`：IsRelPrime.of_add_mul_left_right (h : 
IsRelPrime x (y + x * z)) : IsRelPrime x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsRelPrime.of_mul_add_left_right (h : IsRelPrime x (x * z + y)) : IsRelPrime x y :=
  (add_comm _ y ▸ h).of_add_mul_left_right
/-
**IsRelPrime.of_mul_add_right_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsRelPrime.of_mul_add_right_right (h : IsRelPrime x (z * x + y)) : IsRelPr
ime x y
参数：h : IsRelPrime x (z * x + y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_right_right`：IsRelPrime.of_add_mul_right_right (h 
: IsRelPrime x (y + z * x)) : IsRelPrime x y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsRelPrime.of_mul_add_right_right (h : IsRelPrime x (z * x + y)) : IsRelPrime x y :=
  (add_comm _ y ▸ h).of_add_mul_right_right

end CommSemiring

section ScalarTower

variable {R G : Type*} [CommSemiring R] [Group G] [MulAction G R] [SMulCommClass G R R]
  [IsScalarTower G R R] (x : G) (y z : R)

/-
**isCoprime_group_smul_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_group_smul_left : IsCoprime (x • y) z ↔ IsCoprime y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_smul_comm`：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsSca
larTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c :
 α) (d :…
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem isCoprime_group_smul_left : IsCoprime (x • y) z ↔ IsCoprime y z :=
  ⟨fun ⟨a, b, h⟩ => ⟨x • a, b, by rwa [smul_mul_assoc, ← mul_smul_comm]⟩, fun ⟨a, b, h⟩ =>
    ⟨x⁻¹ • a, b, by rwa [smul_mul_smul_comm, inv_mul_cancel, one_smul]⟩⟩
/-
**isCoprime_group_smul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_group_smul_right : IsCoprime y (x • z) ↔ IsCoprime y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `isCoprime_group_smul_left`：isCoprime_group_smul_left : IsCoprime (x • y)
 z ↔ IsCoprime y z
-/
theorem isCoprime_group_smul_right : IsCoprime y (x • z) ↔ IsCoprime y z :=
  isCoprime_comm.trans <| (isCoprime_group_smul_left x z y).trans isCoprime_comm
/-
**isCoprime_group_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_group_smul : IsCoprime (x • y) (x • z) ↔ IsCoprime y z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isCoprime_group_smul_left`：isCoprime_group_smul_left : IsCoprime (x • y)
 z ↔ IsCoprime y z
· 使用定理 `isCoprime_group_smul_right`：isCoprime_group_smul_right : IsCoprime y (x 
• z) ↔ IsCoprime y z
-/
theorem isCoprime_group_smul : IsCoprime (x • y) (x • z) ↔ IsCoprime y z :=
  (isCoprime_group_smul_left x y (x • z)).trans (isCoprime_group_smul_right x y z)

end ScalarTower

section CommSemiringUnit

variable {R : Type*} [CommSemiring R] {x u v : R}

/-
**isCoprime_mul_unit_left_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_mul_unit_left_left (hu : IsUnit x) (y z : R) : IsCoprime (x * y)
 z ↔ IsCoprime y z
参数：hu : IsUnit x；y z : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoprime_group_smul_left`：isCoprime_group_smul_left : IsCoprime (x • y)
 z ↔ IsCoprime y z
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
-/
theorem isCoprime_mul_unit_left_left (hu : IsUnit x) (y z : R) :
    IsCoprime (x * y) z ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_left u y z
/-
**isCoprime_mul_unit_left_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_mul_unit_left_right (hu : IsUnit x) (y z : R) : IsCoprime y (x *
 z) ↔ IsCoprime y z
参数：hu : IsUnit x；y z : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoprime_group_smul_right`：isCoprime_group_smul_right : IsCoprime y (x 
• z) ↔ IsCoprime y z
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
-/
theorem isCoprime_mul_unit_left_right (hu : IsUnit x) (y z : R) :
    IsCoprime y (x * z) ↔ IsCoprime y z :=
  let ⟨u, hu⟩ := hu
  hu ▸ isCoprime_group_smul_right u y z
/-
**isCoprime_mul_unit_right_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_mul_unit_right_left (hu : IsUnit x) (y z : R) : IsCoprime (y * x
) z ↔ IsCoprime y z
参数：hu : IsUnit x；y z : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoprime_mul_unit_left_left`：isCoprime_mul_unit_left_left (hu : IsUnit 
x) (y z : R) : IsCoprime (x * y) z ↔ IsCoprime y z
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem isCoprime_mul_unit_right_left (hu : IsUnit x) (y z : R) :
    IsCoprime (y * x) z ↔ IsCoprime y z :=
  mul_comm x y ▸ isCoprime_mul_unit_left_left hu y z
/-
**isCoprime_mul_unit_right_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_mul_unit_right_right (hu : IsUnit x) (y z : R) : IsCoprime y (z 
* x) ↔ IsCoprime y z
参数：hu : IsUnit x；y z : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoprime_mul_unit_left_right`：isCoprime_mul_unit_left_right (hu : IsUni
t x) (y z : R) : IsCoprime y (x * z) ↔ IsCoprime y z
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem isCoprime_mul_unit_right_right (hu : IsUnit x) (y z : R) :
    IsCoprime y (z * x) ↔ IsCoprime y z :=
  mul_comm x z ▸ isCoprime_mul_unit_left_right hu y z
/-
**isCoprime_mul_units_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_mul_units_left (hu : IsUnit u) (hv : IsUnit v) (y z : R) : IsCop
rime (u * y) (v * z) ↔ IsCoprime y z
参数：hu : IsUnit u；hv : IsUnit v；y z : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isCoprime_mul_unit_left_left`：isCoprime_mul_unit_left_left (hu : IsUnit 
x) (y z : R) : IsCoprime (x * y) z ↔ IsCoprime y z
· 使用定理 `isCoprime_mul_unit_left_right`：isCoprime_mul_unit_left_right (hu : IsUni
t x) (y z : R) : IsCoprime y (x * z) ↔ IsCoprime y z
-/
theorem isCoprime_mul_units_left (hu : IsUnit u) (hv : IsUnit v) (y z : R) :
    IsCoprime (u * y) (v * z) ↔ IsCoprime y z :=
  Iff.trans
    (isCoprime_mul_unit_left_left hu _ _)
    (isCoprime_mul_unit_left_right hv _ _)
/-
**isCoprime_mul_units_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_mul_units_right (hu : IsUnit u) (hv : IsUnit v) (y z : R) : IsCo
prime (y * u) (z * v) ↔ IsCoprime y z
参数：hu : IsUnit u；hv : IsUnit v；y z : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isCoprime_mul_unit_right_left`：isCoprime_mul_unit_right_left (hu : IsUni
t x) (y z : R) : IsCoprime (y * x) z ↔ IsCoprime y z
· 使用定理 `isCoprime_mul_unit_right_right`：isCoprime_mul_unit_right_right (hu : IsU
nit x) (y z : R) : IsCoprime y (z * x) ↔ IsCoprime y z
-/
theorem isCoprime_mul_units_right (hu : IsUnit u) (hv : IsUnit v) (y z : R) :
    IsCoprime (y * u) (z * v) ↔ IsCoprime y z :=
  Iff.trans
    (isCoprime_mul_unit_right_left hu _ _)
    (isCoprime_mul_unit_right_right hv _ _)
/-
**isCoprime_mul_unit_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_mul_unit_left (hu : IsUnit x) (y z : R) : IsCoprime (x * y) (x *
 z) ↔ IsCoprime y z
参数：hu : IsUnit x；y z : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoprime_mul_units_left`：isCoprime_mul_units_left (hu : IsUnit u) (hv :
 IsUnit v) (y z : R) : IsCoprime (u * y) (v * z) ↔ IsCoprime y z
-/
theorem isCoprime_mul_unit_left (hu : IsUnit x) (y z : R) :
    IsCoprime (x * y) (x * z) ↔ IsCoprime y z :=
  isCoprime_mul_units_left hu hu _ _
/-
**isCoprime_mul_unit_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoprime_mul_unit_right (hu : IsUnit x) (y z : R) : IsCoprime (y * x) (z 
* x) ↔ IsCoprime y z
参数：hu : IsUnit x；y z : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCoprime_mul_units_right`：isCoprime_mul_units_right (hu : IsUnit u) (hv
 : IsUnit v) (y z : R) : IsCoprime (y * u) (z * v) ↔ IsCoprime y z
-/
theorem isCoprime_mul_unit_right (hu : IsUnit x) (y z : R) :
    IsCoprime (y * x) (z * x) ↔ IsCoprime y z :=
  isCoprime_mul_units_right hu hu _ _

end CommSemiringUnit

namespace IsCoprime

section CommRing

variable {R : Type u} [CommRing R]

/-
**IsCoprime.add_mul_left_left** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：add_mul_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + y
 * z) y
参数：h : IsCoprime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_left_left`：IsCoprime.of_add_mul_left_left (h : IsCo
prime (x + y * z) y) : IsCoprime x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
-/
theorem add_mul_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + y * z) y :=
  @of_add_mul_left_left R _ _ _ (-z) <| by simpa only [mul_neg, add_neg_cancel_right] using h
/-
**IsCoprime.add_mul_right_left** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：add_mul_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + 
z * y) y
参数：h : IsCoprime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsCoprime.add_mul_left_left`：add_mul_left_left {x y : R} (h : IsCoprime 
x y) (z : R) : IsCoprime (x + y * z) y
-/
theorem add_mul_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (x + z * y) y := by
  rw [mul_comm]
  exact h.add_mul_left_left z
/-
**IsCoprime.add_mul_left_right** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：add_mul_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y 
+ x * z)
参数：h : IsCoprime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `IsCoprime.add_mul_left_left`：add_mul_left_left {x y : R} (h : IsCoprime 
x y) (z : R) : IsCoprime (x + y * z) y
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
-/
theorem add_mul_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + x * z) := by
  rw [isCoprime_comm]
  exact h.symm.add_mul_left_left z
/-
**IsCoprime.add_mul_right_right** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：add_mul_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y
 + z * x)
参数：h : IsCoprime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `IsCoprime.add_mul_right_left`：add_mul_right_left {x y : R} (h : IsCoprim
e x y) (z : R) : IsCoprime (x + z * y) y
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
-/
theorem add_mul_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (y + z * x) := by
  rw [isCoprime_comm]
  exact h.symm.add_mul_right_left z
/-
**IsCoprime.mul_add_left_left** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：mul_add_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (y * z
 + x) y
参数：h : IsCoprime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `IsCoprime.add_mul_left_left`：add_mul_left_left {x y : R} (h : IsCoprime 
x y) (z : R) : IsCoprime (x + y * z) y
-/
theorem mul_add_left_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (y * z + x) y := by
  rw [add_comm]
  exact h.add_mul_left_left z
/-
**IsCoprime.mul_add_right_left** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：mul_add_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (z * 
y + x) y
参数：h : IsCoprime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `IsCoprime.add_mul_right_left`：add_mul_right_left {x y : R} (h : IsCoprim
e x y) (z : R) : IsCoprime (x + z * y) y
-/
theorem mul_add_right_left {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime (z * y + x) y := by
  rw [add_comm]
  exact h.add_mul_right_left z
/-
**IsCoprime.mul_add_left_right** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：mul_add_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (x 
* z + y)
参数：h : IsCoprime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `IsCoprime.add_mul_left_right`：add_mul_left_right {x y : R} (h : IsCoprim
e x y) (z : R) : IsCoprime x (y + x * z)
-/
theorem mul_add_left_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (x * z + y) := by
  rw [add_comm]
  exact h.add_mul_left_right z
/-
**IsCoprime.mul_add_right_right** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：mul_add_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (z
 * x + y)
参数：h : IsCoprime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `IsCoprime.add_mul_right_right`：add_mul_right_right {x y : R} (h : IsCopr
ime x y) (z : R) : IsCoprime x (y + z * x)
-/
theorem mul_add_right_right {x y : R} (h : IsCoprime x y) (z : R) : IsCoprime x (z * x + y) := by
  rw [add_comm]
  exact h.add_mul_right_right z
/-
**IsCoprime.add_mul_left_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime (x + y * z) y ↔ 
IsCoprime x y
参数：x + y * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_left_left`：IsCoprime.of_add_mul_left_left (h : IsCo
prime (x + y * z) y) : IsCoprime x y
· 使用定理 `IsCoprime.add_mul_left_left`：add_mul_left_left {x y : R} (h : IsCoprime 
x y) (z : R) : IsCoprime (x + y * z) y
-/
@[simp] theorem add_mul_left_left_iff {x y z : R} : IsCoprime (x + y * z) y ↔ IsCoprime x y :=
  ⟨of_add_mul_left_left, fun h => h.add_mul_left_left z⟩
/-
**IsCoprime.add_mul_right_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime (x + z * y) y ↔ 
IsCoprime x y
参数：x + z * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_right_left`：IsCoprime.of_add_mul_right_left (h : Is
Coprime (x + z * y) y) : IsCoprime x y
· 使用定理 `IsCoprime.add_mul_right_left`：add_mul_right_left {x y : R} (h : IsCoprim
e x y) (z : R) : IsCoprime (x + z * y) y
-/
@[simp] theorem add_mul_right_left_iff {x y z : R} : IsCoprime (x + z * y) y ↔ IsCoprime x y :=
  ⟨of_add_mul_right_left, fun h => h.add_mul_right_left z⟩
/-
**IsCoprime.add_mul_left_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime x (y + x * z) ↔ 
IsCoprime x y
参数：y + x * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_left_right`：IsCoprime.of_add_mul_left_right (h : Is
Coprime x (y + x * z)) : IsCoprime x y
· 使用定理 `IsCoprime.add_mul_left_right`：add_mul_left_right {x y : R} (h : IsCoprim
e x y) (z : R) : IsCoprime x (y + x * z)
-/
@[simp] theorem add_mul_left_right_iff {x y z : R} : IsCoprime x (y + x * z) ↔ IsCoprime x y :=
  ⟨of_add_mul_left_right, fun h => h.add_mul_left_right z⟩
/-
**IsCoprime.add_mul_right_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime x (y + z * x) ↔ 
IsCoprime x y
参数：y + z * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_add_mul_right_right`：IsCoprime.of_add_mul_right_right (h : 
IsCoprime x (y + z * x)) : IsCoprime x y
· 使用定理 `IsCoprime.add_mul_right_right`：add_mul_right_right {x y : R} (h : IsCopr
ime x y) (z : R) : IsCoprime x (y + z * x)
-/
@[simp] theorem add_mul_right_right_iff {x y z : R} : IsCoprime x (y + z * x) ↔ IsCoprime x y :=
  ⟨of_add_mul_right_right, fun h => h.add_mul_right_right z⟩
/-
**IsCoprime.mul_add_left_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime (y * z + x) y ↔ 
IsCoprime x y
参数：y * z + x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_mul_add_left_left`：IsCoprime.of_mul_add_left_left (h : IsCo
prime (y * z + x) y) : IsCoprime x y
· 使用定理 `IsCoprime.mul_add_left_left`：mul_add_left_left {x y : R} (h : IsCoprime 
x y) (z : R) : IsCoprime (y * z + x) y
-/
@[simp] theorem mul_add_left_left_iff {x y z : R} : IsCoprime (y * z + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_left_left, fun h => h.mul_add_left_left z⟩
/-
**IsCoprime.mul_add_right_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime (z * y + x) y ↔ 
IsCoprime x y
参数：z * y + x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_mul_add_right_left`：IsCoprime.of_mul_add_right_left (h : Is
Coprime (z * y + x) y) : IsCoprime x y
· 使用定理 `IsCoprime.mul_add_right_left`：mul_add_right_left {x y : R} (h : IsCoprim
e x y) (z : R) : IsCoprime (z * y + x) y
-/
@[simp] theorem mul_add_right_left_iff {x y z : R} : IsCoprime (z * y + x) y ↔ IsCoprime x y :=
  ⟨of_mul_add_right_left, fun h => h.mul_add_right_left z⟩
/-
**IsCoprime.mul_add_left_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime x (x * z + y) ↔ 
IsCoprime x y
参数：x * z + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_mul_add_left_right`：IsCoprime.of_mul_add_left_right (h : Is
Coprime x (x * z + y)) : IsCoprime x y
· 使用定理 `IsCoprime.mul_add_left_right`：mul_add_left_right {x y : R} (h : IsCoprim
e x y) (z : R) : IsCoprime x (x * z + y)
-/
@[simp] theorem mul_add_left_right_iff {x y z : R} : IsCoprime x (x * z + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_left_right, fun h => h.mul_add_left_right z⟩
/-
**IsCoprime.mul_add_right_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime x (z * x + y) ↔ 
IsCoprime x y
参数：z * x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.of_mul_add_right_right`：IsCoprime.of_mul_add_right_right (h : 
IsCoprime x (z * x + y)) : IsCoprime x y
· 使用定理 `IsCoprime.mul_add_right_right`：mul_add_right_right {x y : R} (h : IsCopr
ime x y) (z : R) : IsCoprime x (z * x + y)
-/
@[simp] theorem mul_add_right_right_iff {x y z : R} : IsCoprime x (z * x + y) ↔ IsCoprime x y :=
  ⟨of_mul_add_right_right, fun h => h.mul_add_right_right z⟩
/-
**IsCoprime.neg_left** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：neg_left {x y : R} (h : IsCoprime x y) : IsCoprime (-x) y
参数：h : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
-/
theorem neg_left {x y : R} (h : IsCoprime x y) : IsCoprime (-x) y := by
  obtain ⟨a, b, h⟩ := h
  use -a, b
  rwa [neg_mul_neg]
/-
**IsCoprime.neg_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCoprime x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.neg_left`：neg_left {x y : R} (h : IsCoprime x y) : IsCoprime (
-x) y
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCoprime x y :=
  ⟨fun h => neg_neg x ▸ h.neg_left, neg_left⟩
/-
**IsCoprime.neg_right** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：neg_right {x y : R} (h : IsCoprime x y) : IsCoprime x (-y)
参数：h : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `IsCoprime.neg_left`：neg_left {x y : R} (h : IsCoprime x y) : IsCoprime (
-x) y
-/
theorem neg_right {x y : R} (h : IsCoprime x y) : IsCoprime x (-y) :=
  h.symm.neg_left.symm
/-
**IsCoprime.neg_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：neg_right_iff (x y : R) : IsCoprime x (-y) ↔ IsCoprime x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.neg_right`：neg_right {x y : R} (h : IsCoprime x y) : IsCoprime
 x (-y)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neg_right_iff (x y : R) : IsCoprime x (-y) ↔ IsCoprime x y :=
  ⟨fun h => neg_neg y ▸ h.neg_right, neg_right⟩
/-
**IsCoprime.neg_neg** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：neg_neg {x y : R} (h : IsCoprime x y) : IsCoprime (-x) (-y)
参数：h : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.neg_right`：neg_right {x y : R} (h : IsCoprime x y) : IsCoprime
 x (-y)
· 使用定理 `IsCoprime.neg_left`：neg_left {x y : R} (h : IsCoprime x y) : IsCoprime (
-x) y
-/
theorem neg_neg {x y : R} (h : IsCoprime x y) : IsCoprime (-x) (-y) :=
  h.neg_left.neg_right
/-
**IsCoprime.neg_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：neg_neg_iff (x y : R) : IsCoprime (-x) (-y) ↔ IsCoprime x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsCoprime.neg_left_iff`：neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCo
prime x y
· 使用定理 `IsCoprime.neg_right_iff`：neg_right_iff (x y : R) : IsCoprime x (-y) ↔ Is
Coprime x y
-/
theorem neg_neg_iff (x y : R) : IsCoprime (-x) (-y) ↔ IsCoprime x y :=
  (neg_left_iff _ _).trans (neg_right_iff _ _)
/-
**IsCoprime.sub_mul_left_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime (x - y * z) y ↔ 
IsCoprime x y
参数：x - y * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `IsCoprime.add_mul_left_left_iff`：∀ {R : Type u} [inst : CommRing R] {x y
 z : R}, IsCoprime (x + y * z) y ↔ IsCoprime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem sub_mul_left_left_iff {x y z : R} : IsCoprime (x - y * z) y ↔ IsCoprime x y := by
  rw [sub_eq_add_neg, ← mul_neg, add_mul_left_left_iff]
/-
**IsCoprime.sub_mul_right_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime (x - z * y) y ↔ 
IsCoprime x y
参数：x - z * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsCoprime.add_mul_right_left_iff`：∀ {R : Type u} [inst : CommRing R] {x 
y z : R}, IsCoprime (x + z * y) y ↔ IsCoprime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem sub_mul_right_left_iff {x y z : R} : IsCoprime (x - z * y) y ↔ IsCoprime x y := by
  rw [sub_eq_add_neg, ← neg_mul, add_mul_right_left_iff]
/-
**IsCoprime.sub_mul_left_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime x (y - x * z) ↔ 
IsCoprime x y
参数：y - x * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `IsCoprime.add_mul_left_right_iff`：∀ {R : Type u} [inst : CommRing R] {x 
y z : R}, IsCoprime x (y + x * z) ↔ IsCoprime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem sub_mul_left_right_iff {x y z : R} : IsCoprime x (y - x * z) ↔ IsCoprime x y := by
  rw [sub_eq_add_neg, ← mul_neg, add_mul_left_right_iff]
/-
**IsCoprime.sub_mul_right_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime x (y - z * x) ↔ 
IsCoprime x y
参数：y - z * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsCoprime.add_mul_right_right_iff`：∀ {R : Type u} [inst : CommRing R] {x
 y z : R}, IsCoprime x (y + z * x) ↔ IsCoprime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem sub_mul_right_right_iff {x y z : R} : IsCoprime x (y - z * x) ↔ IsCoprime x y := by
  rw [sub_eq_add_neg, ← neg_mul, add_mul_right_right_iff]
/-
**IsCoprime.mul_sub_left_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime (y * z - x) y ↔ 
IsCoprime x y
参数：y * z - x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `IsCoprime.add_mul_left_left_iff`：∀ {R : Type u} [inst : CommRing R] {x y
 z : R}, IsCoprime (x + y * z) y ↔ IsCoprime x y
· 使用定理 `IsCoprime.neg_left_iff`：neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCo
prime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mul_sub_left_left_iff {x y z : R} : IsCoprime (y * z - x) y ↔ IsCoprime x y := by
  rw [sub_eq_neg_add, add_mul_left_left_iff, neg_left_iff]
/-
**IsCoprime.mul_sub_right_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime (z * y - x) y ↔ 
IsCoprime x y
参数：z * y - x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `IsCoprime.add_mul_right_left_iff`：∀ {R : Type u} [inst : CommRing R] {x 
y z : R}, IsCoprime (x + z * y) y ↔ IsCoprime x y
· 使用定理 `IsCoprime.neg_left_iff`：neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCo
prime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mul_sub_right_left_iff {x y z : R} : IsCoprime (z * y - x) y ↔ IsCoprime x y := by
  rw [sub_eq_neg_add, add_mul_right_left_iff, neg_left_iff]
/-
**IsCoprime.mul_sub_left_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime x (x * z - y) ↔ 
IsCoprime x y
参数：x * z - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsCoprime.mul_add_left_right_iff`：∀ {R : Type u} [inst : CommRing R] {x 
y z : R}, IsCoprime x (x * z + y) ↔ IsCoprime x y
· 使用定理 `IsCoprime.neg_right_iff`：neg_right_iff (x y : R) : IsCoprime x (-y) ↔ Is
Coprime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mul_sub_left_right_iff {x y z : R} : IsCoprime x (x * z - y) ↔ IsCoprime x y := by
  rw [sub_eq_add_neg, mul_add_left_right_iff, neg_right_iff]
/-
**IsCoprime.mul_sub_right_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {x y z : R}, IsCoprime x (z * x - y) ↔ 
IsCoprime x y
参数：z * x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsCoprime.mul_add_right_right_iff`：∀ {R : Type u} [inst : CommRing R] {x
 y z : R}, IsCoprime x (z * x + y) ↔ IsCoprime x y
· 使用定理 `IsCoprime.neg_right_iff`：neg_right_iff (x y : R) : IsCoprime x (-y) ↔ Is
Coprime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mul_sub_right_right_iff {x y z : R} : IsCoprime x (z * x - y) ↔ IsCoprime x y := by
  rw [sub_eq_add_neg, mul_add_right_right_iff, neg_right_iff]
/-
**IsCoprime.add_one_left_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：add_one_left_of_dvd {x y : R} (h : y ∣ x) : IsCoprime (x + 1) y
参数：h : y ∣ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCoprime.mul_add_left_left_iff`：∀ {R : Type u} [inst : CommRing R] {x y
 z : R}, IsCoprime (y * z + x) y ↔ IsCoprime x y
· 使用定理 `isCoprime_one_left`：isCoprime_one_left : IsCoprime 1 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma add_one_left_of_dvd {x y : R} (h : y ∣ x) : IsCoprime (x + 1) y := by
  obtain ⟨z, rfl⟩ := h
  rw [mul_add_left_left_iff]
  exact isCoprime_one_left
/-
**IsCoprime.add_one_right_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：add_one_right_of_dvd {x y : R} (h : x ∣ y) : IsCoprime x (y + 1)
参数：h : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用引理 `IsCoprime.add_one_left_of_dvd`：add_one_left_of_dvd {x y : R} (h : y ∣ x)
 : IsCoprime (x + 1) y
-/
lemma add_one_right_of_dvd {x y : R} (h : x ∣ y) : IsCoprime x (y + 1) :=
  isCoprime_comm.mp (add_one_left_of_dvd h)
/-
**IsCoprime.sub_one_left_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：sub_one_left_of_dvd {x y : R} (h : y ∣ x) : IsCoprime (x - 1) y
参数：h : y ∣ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `IsCoprime.neg_left_iff`：neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCo
prime x y
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用引理 `IsCoprime.add_one_left_of_dvd`：add_one_left_of_dvd {x y : R} (h : y ∣ x)
 : IsCoprime (x + 1) y
· 使用定理 `Dvd.dvd.neg_right`：∀ {α : Type u_1} [inst : Semigroup α] [inst_1 : HasDi
stribNeg α] {a b : α}, a ∣ b → a ∣ -b
-/
lemma sub_one_left_of_dvd {x y : R} (h : y ∣ x) : IsCoprime (x - 1) y := by
  rw [← neg_sub, neg_left_iff, sub_eq_neg_add]
  exact add_one_left_of_dvd h.neg_right
/-
**IsCoprime.sub_one_right_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：sub_one_right_of_dvd {x y : R} (h : x ∣ y) : IsCoprime x (y - 1)
参数：h : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用引理 `IsCoprime.sub_one_left_of_dvd`：sub_one_left_of_dvd {x y : R} (h : y ∣ x)
 : IsCoprime (x - 1) y
-/
lemma sub_one_right_of_dvd {x y : R} (h : x ∣ y) : IsCoprime x (y - 1) :=
  isCoprime_comm.mp (sub_one_left_of_dvd h)
/-
**IsCoprime.add_one_sub_one_of_two_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：add_one_sub_one_of_two_dvd {x : R} (h : 2 ∣ x) : IsCoprime (x + 1) (x - 1)
参数：h : 2 ∣ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 32 条，此处仅展示前 30 条）
-/
lemma add_one_sub_one_of_two_dvd {x : R} (h : 2 ∣ x) : IsCoprime (x + 1) (x - 1) := by
  simpa [show 2 + (x - 1) = x + 1 by ring] using add_mul_left_left (sub_one_right_of_dvd h) 1

section abs

variable [LinearOrder R] [AddLeftMono R]

/-
**IsCoprime.abs_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：abs_left_iff (x y : R) : IsCoprime |x| y ↔ IsCoprime x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `IsCoprime.neg_left_iff`：neg_left_iff (x y : R) : IsCoprime (-x) y ↔ IsCo
prime x y
-/
lemma abs_left_iff (x y : R) : IsCoprime |x| y ↔ IsCoprime x y := by
  cases le_or_gt 0 x with
  | inl h => rw [abs_of_nonneg h]
  | inr h => rw [abs_of_neg h, IsCoprime.neg_left_iff]
/-
**IsCoprime.abs_left** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [inst_1 : LinearOrder R] [AddLeftMono R
] {x y : R}, IsCoprime x y → IsCoprime |x| y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsCoprime.abs_left_iff`：abs_left_iff (x y : R) : IsCoprime |x| y ↔ IsCop
rime x y
-/
lemma abs_left {x y : R} (h : IsCoprime x y) : IsCoprime |x| y := abs_left_iff _ _ |>.2 h
/-
**IsCoprime.abs_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsCoprime`。
形式化陈述：abs_right_iff (x y : R) : IsCoprime x |y| ↔ IsCoprime x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用引理 `IsCoprime.abs_left_iff`：abs_left_iff (x y : R) : IsCoprime |x| y ↔ IsCop
rime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma abs_right_iff (x y : R) : IsCoprime x |y| ↔ IsCoprime x y := by
  rw [isCoprime_comm, IsCoprime.abs_left_iff, isCoprime_comm]
/-
**IsCoprime.abs_right** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [inst_1 : LinearOrder R] [AddLeftMono R
] {x y : R}, IsCoprime x y → IsCoprime x |y|
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsCoprime.abs_right_iff`：abs_right_iff (x y : R) : IsCoprime x |y| ↔ IsC
oprime x y
-/
lemma abs_right {x y : R} (h : IsCoprime x y) : IsCoprime x |y| := abs_right_iff _ _ |>.2 h
/-
**IsCoprime.abs_abs_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：abs_abs_iff (x y : R) : IsCoprime |x| |y| ↔ IsCoprime x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `IsCoprime.abs_left_iff`：abs_left_iff (x y : R) : IsCoprime |x| y ↔ IsCop
rime x y
· 使用引理 `IsCoprime.abs_right_iff`：abs_right_iff (x y : R) : IsCoprime x |y| ↔ IsC
oprime x y
-/
theorem abs_abs_iff (x y : R) : IsCoprime |x| |y| ↔ IsCoprime x y :=
  (abs_left_iff _ _).trans (abs_right_iff _ _)
/-
**IsCoprime.abs_abs** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：abs_abs {x y : R} (h : IsCoprime x y) : IsCoprime |x| |y|
参数：h : IsCoprime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoprime.abs_right`：∀ {R : Type u} [inst : CommRing R] [inst_1 : Linear
Order R] [AddLeftMono R] {x y : R}, IsCoprime x y → IsCoprime x |y|
· 使用定理 `IsCoprime.abs_left`：∀ {R : Type u} [inst : CommRing R] [inst_1 : LinearO
rder R] [AddLeftMono R] {x y : R}, IsCoprime x y → IsCoprime |x| y
-/
theorem abs_abs {x y : R} (h : IsCoprime x y) : IsCoprime |x| |y| := h.abs_left.abs_right

end abs

end CommRing

/-
**IsCoprime.sq_add_sq_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsCoprime`。
形式化陈述：sq_add_sq_ne_zero {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrdere
dRing R] {a b : R} (h : IsCoprime a b) : a ^ 2 + b ^ 2 != 0
参数：h : IsCoprime a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_eq_zero_iff_of_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [ins
t_1 : PartialOrder α] [AddLeftMono α] [AddRightMono α] {a b : α},   0 ≤ a → 0 ≤ 
b → (a + b = 0 …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `not_isCoprime_zero_zero`：not_isCoprime_zero_zero [Nontrivial R] : ¬IsCop
rime (0 : R) 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
-/
theorem sq_add_sq_ne_zero {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {a b : R} (h : IsCoprime a b) :
    a ^ 2 + b ^ 2 ≠ 0 := by
  intro h'
  obtain ⟨ha, hb⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp h'
  obtain rfl := eq_zero_of_pow_eq_zero ha
  obtain rfl := eq_zero_of_pow_eq_zero hb
  exact not_isCoprime_zero_zero h

end IsCoprime

/-- `IsCoprime` is not a useful definition for `Nat`; consider using `Nat.Coprime` instead. -/
@[simp]
/-
**Nat.isCoprime_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.isCoprime_iff {m n : Nat} : IsCoprime m n ↔ m = 1 ∨ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `isCoprime_one_left`：isCoprime_one_left : IsCoprime 1 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCoprime_one_right`：isCoprime_one_right : IsCoprime x 1

--- 原说明 ---
`IsCoprime` is not a useful definition for `Nat`; consider using `Nat.Coprime` i
nstead.
-/
lemma Nat.isCoprime_iff {m n : ℕ} : IsCoprime m n ↔ m = 1 ∨ n = 1 := by
  refine ⟨fun ⟨a, b, H⟩ => ?_, fun h => ?_⟩
  · simp_rw [Nat.add_eq_one_iff, mul_eq_one, mul_eq_zero] at H
    exact H.symm.imp (·.1.2) (·.2.2)
  · obtain rfl | rfl := h
    · exact isCoprime_one_left
    · exact isCoprime_one_right

/-- `IsCoprime` is not a useful definition for `PNat`; consider using `Nat.Coprime` instead. -/
/-
**PNat.isCoprime_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：PNat.isCoprime_iff {m n : Nat+} : IsCoprime (m : Nat) n ↔ m = 1 ∨ n = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`IsCoprime` is not a useful definition for `PNat`; consider using `Nat.Coprime` 
instead.
-/
lemma PNat.isCoprime_iff {m n : ℕ+} : IsCoprime (m : ℕ) n ↔ m = 1 ∨ n = 1 := by simp

/-- `IsCoprime` is not a useful definition if an inverse is available. -/
@[simp]
/-
**Semifield.isCoprime_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Semifield.isCoprime_iff {R : Type*} [Semifield R] {m n : R} : IsCoprime m 
n ↔ m != 0 ∨ n != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p

--- 原说明 ---
`IsCoprime` is not a useful definition if an inverse is available.
-/
lemma Semifield.isCoprime_iff {R : Type*} [Semifield R] {m n : R} :
    IsCoprime m n ↔ m ≠ 0 ∨ n ≠ 0 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [isCoprime_zero_right]
  suffices IsCoprime m n by simpa [hn]
  refine ⟨0, n⁻¹, ?_⟩
  simp [inv_mul_cancel₀ hn]

namespace IsRelPrime

variable {R} [CommRing R] {x y : R}

/-
**IsRelPrime.add_mul_left_left** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：add_mul_left_left (h : IsRelPrime x y) (z : R) : IsRelPrime (x + y * z) y
参数：h : IsRelPrime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_left_left`：IsRelPrime.of_add_mul_left_left (h : Is
RelPrime (x + y * z) y) : IsRelPrime x y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
-/
theorem add_mul_left_left (h : IsRelPrime x y) (z : R) : IsRelPrime (x + y * z) y :=
  @of_add_mul_left_left R _ _ _ (-z) <| by simpa only [mul_neg, add_neg_cancel_right] using h
/-
**IsRelPrime.add_mul_right_left** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：add_mul_right_left (h : IsRelPrime x y) (z : R) : IsRelPrime (x + z * y) y
参数：h : IsRelPrime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.add_mul_left_left`：add_mul_left_left (h : IsRelPrime x y) (z 
: R) : IsRelPrime (x + y * z) y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem add_mul_right_left (h : IsRelPrime x y) (z : R) : IsRelPrime (x + z * y) y :=
  mul_comm z y ▸ h.add_mul_left_left z
/-
**IsRelPrime.add_mul_left_right** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：add_mul_left_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (y + x * z)
参数：h : IsRelPrime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
· 使用定理 `IsRelPrime.add_mul_left_left`：add_mul_left_left (h : IsRelPrime x y) (z 
: R) : IsRelPrime (x + y * z) y
-/
theorem add_mul_left_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (y + x * z) :=
  (h.symm.add_mul_left_left z).symm
/-
**IsRelPrime.add_mul_right_right** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：add_mul_right_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (y + z * x
)
参数：h : IsRelPrime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
· 使用定理 `IsRelPrime.add_mul_right_left`：add_mul_right_left (h : IsRelPrime x y) (
z : R) : IsRelPrime (x + z * y) y
-/
theorem add_mul_right_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (y + z * x) :=
  (h.symm.add_mul_right_left z).symm
/-
**IsRelPrime.mul_add_left_left** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：mul_add_left_left (h : IsRelPrime x y) (z : R) : IsRelPrime (y * z + x) y
参数：h : IsRelPrime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.add_mul_left_left`：add_mul_left_left (h : IsRelPrime x y) (z 
: R) : IsRelPrime (x + y * z) y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem mul_add_left_left (h : IsRelPrime x y) (z : R) : IsRelPrime (y * z + x) y :=
  add_comm x _ ▸ h.add_mul_left_left z
/-
**IsRelPrime.mul_add_right_left** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：mul_add_right_left (h : IsRelPrime x y) (z : R) : IsRelPrime (z * y + x) y
参数：h : IsRelPrime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.add_mul_right_left`：add_mul_right_left (h : IsRelPrime x y) (
z : R) : IsRelPrime (x + z * y) y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem mul_add_right_left (h : IsRelPrime x y) (z : R) : IsRelPrime (z * y + x) y :=
  add_comm x _ ▸ h.add_mul_right_left z
/-
**IsRelPrime.mul_add_left_right** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：mul_add_left_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (x * z + y)
参数：h : IsRelPrime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.add_mul_left_right`：add_mul_left_right (h : IsRelPrime x y) (
z : R) : IsRelPrime x (y + x * z)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem mul_add_left_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (x * z + y) :=
  add_comm y _ ▸ h.add_mul_left_right z
/-
**IsRelPrime.mul_add_right_right** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：mul_add_right_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (z * x + y
)
参数：h : IsRelPrime x y；z : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.add_mul_right_right`：add_mul_right_right (h : IsRelPrime x y)
 (z : R) : IsRelPrime x (y + z * x)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem mul_add_right_right (h : IsRelPrime x y) (z : R) : IsRelPrime x (z * x + y) :=
  add_comm y _ ▸ h.add_mul_right_right z

variable {z}
/-
**IsRelPrime.add_mul_left_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime (x + y * z) y
 ↔ IsRelPrime x y
参数：x + y * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_left_left`：IsRelPrime.of_add_mul_left_left (h : Is
RelPrime (x + y * z) y) : IsRelPrime x y
· 使用定理 `IsRelPrime.add_mul_left_left`：add_mul_left_left (h : IsRelPrime x y) (z 
: R) : IsRelPrime (x + y * z) y
-/
@[simp] theorem add_mul_left_left_iff : IsRelPrime (x + y * z) y ↔ IsRelPrime x y :=
  ⟨of_add_mul_left_left, fun h ↦ h.add_mul_left_left z⟩
/-
**IsRelPrime.add_mul_right_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime (x + z * y) y
 ↔ IsRelPrime x y
参数：x + z * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_right_left`：IsRelPrime.of_add_mul_right_left (h : 
IsRelPrime (x + z * y) y) : IsRelPrime x y
· 使用定理 `IsRelPrime.add_mul_right_left`：add_mul_right_left (h : IsRelPrime x y) (
z : R) : IsRelPrime (x + z * y) y
-/
@[simp] theorem add_mul_right_left_iff : IsRelPrime (x + z * y) y ↔ IsRelPrime x y :=
  ⟨of_add_mul_right_left, fun h ↦ h.add_mul_right_left z⟩
/-
**IsRelPrime.add_mul_left_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime x (y + x * z)
 ↔ IsRelPrime x y
参数：y + x * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_left_right`：IsRelPrime.of_add_mul_left_right (h : 
IsRelPrime x (y + x * z)) : IsRelPrime x y
· 使用定理 `IsRelPrime.add_mul_left_right`：add_mul_left_right (h : IsRelPrime x y) (
z : R) : IsRelPrime x (y + x * z)
-/
@[simp] theorem add_mul_left_right_iff : IsRelPrime x (y + x * z) ↔ IsRelPrime x y :=
  ⟨of_add_mul_left_right, fun h ↦ h.add_mul_left_right z⟩
/-
**IsRelPrime.add_mul_right_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime x (y + z * x)
 ↔ IsRelPrime x y
参数：y + z * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_add_mul_right_right`：IsRelPrime.of_add_mul_right_right (h 
: IsRelPrime x (y + z * x)) : IsRelPrime x y
· 使用定理 `IsRelPrime.add_mul_right_right`：add_mul_right_right (h : IsRelPrime x y)
 (z : R) : IsRelPrime x (y + z * x)
-/
@[simp] theorem add_mul_right_right_iff : IsRelPrime x (y + z * x) ↔ IsRelPrime x y :=
  ⟨of_add_mul_right_right, fun h ↦ h.add_mul_right_right z⟩
/-
**IsRelPrime.mul_add_left_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime (y * z + x) y
 ↔ IsRelPrime x y
参数：y * z + x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_mul_add_left_left`：IsRelPrime.of_mul_add_left_left (h : Is
RelPrime (y * z + x) y) : IsRelPrime x y
· 使用定理 `IsRelPrime.mul_add_left_left`：mul_add_left_left (h : IsRelPrime x y) (z 
: R) : IsRelPrime (y * z + x) y
-/
@[simp] theorem mul_add_left_left_iff : IsRelPrime (y * z + x) y ↔ IsRelPrime x y :=
  ⟨of_mul_add_left_left, fun h ↦ h.mul_add_left_left z⟩
/-
**IsRelPrime.mul_add_right_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime (z * y + x) y
 ↔ IsRelPrime x y
参数：z * y + x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_mul_add_right_left`：IsRelPrime.of_mul_add_right_left (h : 
IsRelPrime (z * y + x) y) : IsRelPrime x y
· 使用定理 `IsRelPrime.mul_add_right_left`：mul_add_right_left (h : IsRelPrime x y) (
z : R) : IsRelPrime (z * y + x) y
-/
@[simp] theorem mul_add_right_left_iff : IsRelPrime (z * y + x) y ↔ IsRelPrime x y :=
  ⟨of_mul_add_right_left, fun h ↦ h.mul_add_right_left z⟩
/-
**IsRelPrime.mul_add_left_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime x (x * z + y)
 ↔ IsRelPrime x y
参数：x * z + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_mul_add_left_right`：IsRelPrime.of_mul_add_left_right (h : 
IsRelPrime x (x * z + y)) : IsRelPrime x y
· 使用定理 `IsRelPrime.mul_add_left_right`：mul_add_left_right (h : IsRelPrime x y) (
z : R) : IsRelPrime x (x * z + y)
-/
@[simp] theorem mul_add_left_right_iff : IsRelPrime x (x * z + y) ↔ IsRelPrime x y :=
  ⟨of_mul_add_left_right, fun h ↦ h.mul_add_left_right z⟩
/-
**IsRelPrime.mul_add_right_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime x (z * x + y)
 ↔ IsRelPrime x y
参数：z * x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.of_mul_add_right_right`：IsRelPrime.of_mul_add_right_right (h 
: IsRelPrime x (z * x + y)) : IsRelPrime x y
· 使用定理 `IsRelPrime.mul_add_right_right`：mul_add_right_right (h : IsRelPrime x y)
 (z : R) : IsRelPrime x (z * x + y)
-/
@[simp] theorem mul_add_right_right_iff : IsRelPrime x (z * x + y) ↔ IsRelPrime x y :=
  ⟨of_mul_add_right_right, fun h ↦ h.mul_add_right_right z⟩
/-
**IsRelPrime.neg_left** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：neg_left (h : IsRelPrime x y) : IsRelPrime (-x) y
参数：h : IsRelPrime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b
-/
theorem neg_left (h : IsRelPrime x y) : IsRelPrime (-x) y := fun _ ↦ (h <| dvd_neg.mp ·)
/-
**IsRelPrime.neg_right** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：neg_right (h : IsRelPrime x y) : IsRelPrime x (-y)
参数：h : IsRelPrime x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.symm`：∀ {α : Type u_1} [inst : CommMonoid α] {x y : α}, IsRel
Prime x y → IsRelPrime y x
· 使用定理 `IsRelPrime.neg_left`：neg_left (h : IsRelPrime x y) : IsRelPrime (-x) y
-/
theorem neg_right (h : IsRelPrime x y) : IsRelPrime x (-y) := h.symm.neg_left.symm
/-
**IsRelPrime.neg_neg** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y : R}, IsRelPrime x y → IsRelPrim
e (-x) (-y)
参数：-x；-y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.neg_right`：neg_right (h : IsRelPrime x y) : IsRelPrime x (-y)
· 使用定理 `IsRelPrime.neg_left`：neg_left (h : IsRelPrime x y) : IsRelPrime (-x) y
-/
protected theorem neg_neg (h : IsRelPrime x y) : IsRelPrime (-x) (-y) := h.neg_left.neg_right
/-
**IsRelPrime.neg_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：neg_left_iff (x y : R) : IsRelPrime (-x) y ↔ IsRelPrime x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.neg_left`：neg_left (h : IsRelPrime x y) : IsRelPrime (-x) y
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neg_left_iff (x y : R) : IsRelPrime (-x) y ↔ IsRelPrime x y :=
  ⟨fun h ↦ neg_neg x ▸ h.neg_left, neg_left⟩
/-
**IsRelPrime.neg_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：neg_right_iff (x y : R) : IsRelPrime x (-y) ↔ IsRelPrime x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsRelPrime.neg_right`：neg_right (h : IsRelPrime x y) : IsRelPrime x (-y)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem neg_right_iff (x y : R) : IsRelPrime x (-y) ↔ IsRelPrime x y :=
  ⟨fun h ↦ neg_neg y ▸ h.neg_right, neg_right⟩
/-
**IsRelPrime.neg_neg_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：neg_neg_iff (x y : R) : IsRelPrime (-x) (-y) ↔ IsRelPrime x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsRelPrime.neg_left_iff`：neg_left_iff (x y : R) : IsRelPrime (-x) y ↔ Is
RelPrime x y
· 使用定理 `IsRelPrime.neg_right_iff`：neg_right_iff (x y : R) : IsRelPrime x (-y) ↔ 
IsRelPrime x y
-/
theorem neg_neg_iff (x y : R) : IsRelPrime (-x) (-y) ↔ IsRelPrime x y :=
  (neg_left_iff _ _).trans (neg_right_iff _ _)
/-
**IsRelPrime.sub_mul_left_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime (x - y * z) y
 ↔ IsRelPrime x y
参数：x - y * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `IsRelPrime.add_mul_left_left_iff`：∀ {R : Type u_1} [inst : CommRing R] {
x y z : R}, IsRelPrime (x + y * z) y ↔ IsRelPrime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem sub_mul_left_left_iff : IsRelPrime (x - y * z) y ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg, ← mul_neg, add_mul_left_left_iff]
/-
**IsRelPrime.sub_mul_right_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime (x - z * y) y
 ↔ IsRelPrime x y
参数：x - z * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsRelPrime.add_mul_right_left_iff`：∀ {R : Type u_1} [inst : CommRing R] 
{x y z : R}, IsRelPrime (x + z * y) y ↔ IsRelPrime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem sub_mul_right_left_iff : IsRelPrime (x - z * y) y ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg, ← neg_mul, add_mul_right_left_iff]
/-
**IsRelPrime.sub_mul_left_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime x (y - x * z)
 ↔ IsRelPrime x y
参数：y - x * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `IsRelPrime.add_mul_left_right_iff`：∀ {R : Type u_1} [inst : CommRing R] 
{x y z : R}, IsRelPrime x (y + x * z) ↔ IsRelPrime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem sub_mul_left_right_iff : IsRelPrime x (y - x * z) ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg, ← mul_neg, add_mul_left_right_iff]
/-
**IsRelPrime.sub_mul_right_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime x (y - z * x)
 ↔ IsRelPrime x y
参数：y - z * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsRelPrime.add_mul_right_right_iff`：∀ {R : Type u_1} [inst : CommRing R]
 {x y z : R}, IsRelPrime x (y + z * x) ↔ IsRelPrime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem sub_mul_right_right_iff : IsRelPrime x (y - z * x) ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg, ← neg_mul, add_mul_right_right_iff]
/-
**IsRelPrime.mul_sub_left_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime (y * z - x) y
 ↔ IsRelPrime x y
参数：y * z - x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `IsRelPrime.add_mul_left_left_iff`：∀ {R : Type u_1} [inst : CommRing R] {
x y z : R}, IsRelPrime (x + y * z) y ↔ IsRelPrime x y
· 使用定理 `IsRelPrime.neg_left_iff`：neg_left_iff (x y : R) : IsRelPrime (-x) y ↔ Is
RelPrime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mul_sub_left_left_iff : IsRelPrime (y * z - x) y ↔ IsRelPrime x y := by
  rw [sub_eq_neg_add, add_mul_left_left_iff, neg_left_iff]
/-
**IsRelPrime.mul_sub_right_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime (z * y - x) y
 ↔ IsRelPrime x y
参数：z * y - x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `IsRelPrime.add_mul_right_left_iff`：∀ {R : Type u_1} [inst : CommRing R] 
{x y z : R}, IsRelPrime (x + z * y) y ↔ IsRelPrime x y
· 使用定理 `IsRelPrime.neg_left_iff`：neg_left_iff (x y : R) : IsRelPrime (-x) y ↔ Is
RelPrime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mul_sub_right_left_iff : IsRelPrime (z * y - x) y ↔ IsRelPrime x y := by
  rw [sub_eq_neg_add, add_mul_right_left_iff, neg_left_iff]
/-
**IsRelPrime.mul_sub_left_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime x (x * z - y)
 ↔ IsRelPrime x y
参数：x * z - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsRelPrime.mul_add_left_right_iff`：∀ {R : Type u_1} [inst : CommRing R] 
{x y z : R}, IsRelPrime x (x * z + y) ↔ IsRelPrime x y
· 使用定理 `IsRelPrime.neg_right_iff`：neg_right_iff (x y : R) : IsRelPrime x (-y) ↔ 
IsRelPrime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mul_sub_left_right_iff : IsRelPrime x (x * z - y) ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg, mul_add_left_right_iff, neg_right_iff]
/-
**IsRelPrime.mul_sub_right_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsRelPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {x y z : R}, IsRelPrime x (z * x - y)
 ↔ IsRelPrime x y
参数：z * x - y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsRelPrime.mul_add_right_right_iff`：∀ {R : Type u_1} [inst : CommRing R]
 {x y z : R}, IsRelPrime x (z * x + y) ↔ IsRelPrime x y
· 使用定理 `IsRelPrime.neg_right_iff`：neg_right_iff (x y : R) : IsRelPrime x (-y) ↔ 
IsRelPrime x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mul_sub_right_right_iff : IsRelPrime x (z * x - y) ↔ IsRelPrime x y := by
  rw [sub_eq_add_neg, mul_add_right_right_iff, neg_right_iff]
/-
**IsRelPrime.add_one_left_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsRelPrime`。
形式化陈述：add_one_left_of_dvd (h : y ∣ x) : IsRelPrime (x + 1) y
参数：h : y ∣ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRelPrime.mul_add_left_left_iff`：∀ {R : Type u_1} [inst : CommRing R] {
x y z : R}, IsRelPrime (y * z + x) y ↔ IsRelPrime x y
· 使用定理 `isRelPrime_one_left`：isRelPrime_one_left : IsRelPrime 1 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma add_one_left_of_dvd (h : y ∣ x) : IsRelPrime (x + 1) y := by
  obtain ⟨z, rfl⟩ := h
  rw [mul_add_left_left_iff]
  exact isRelPrime_one_left
/-
**IsRelPrime.add_one_right_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsRelPrime`。
形式化陈述：add_one_right_of_dvd (h : x ∣ y) : IsRelPrime x (y + 1)
参数：h : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isRelPrime_comm`：isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x
· 使用引理 `IsRelPrime.add_one_left_of_dvd`：add_one_left_of_dvd (h : y ∣ x) : IsRelP
rime (x + 1) y
-/
lemma add_one_right_of_dvd (h : x ∣ y) : IsRelPrime x (y + 1) :=
  isRelPrime_comm.mp (add_one_left_of_dvd h)
/-
**IsRelPrime.sub_one_left_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsRelPrime`。
形式化陈述：sub_one_left_of_dvd (h : y ∣ x) : IsRelPrime (x - 1) y
参数：h : y ∣ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `IsRelPrime.neg_left_iff`：neg_left_iff (x y : R) : IsRelPrime (-x) y ↔ Is
RelPrime x y
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用引理 `IsRelPrime.add_one_left_of_dvd`：add_one_left_of_dvd (h : y ∣ x) : IsRelP
rime (x + 1) y
· 使用定理 `Dvd.dvd.neg_right`：∀ {α : Type u_1} [inst : Semigroup α] [inst_1 : HasDi
stribNeg α] {a b : α}, a ∣ b → a ∣ -b
-/
lemma sub_one_left_of_dvd (h : y ∣ x) : IsRelPrime (x - 1) y := by
  rw [← neg_sub, neg_left_iff, sub_eq_neg_add]
  exact add_one_left_of_dvd h.neg_right
/-
**IsRelPrime.sub_one_right_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsRelPrime`。
形式化陈述：sub_one_right_of_dvd (h : x ∣ y) : IsRelPrime x (y - 1)
参数：h : x ∣ y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isRelPrime_comm`：isRelPrime_comm : IsRelPrime x y ↔ IsRelPrime y x
· 使用引理 `IsRelPrime.sub_one_left_of_dvd`：sub_one_left_of_dvd (h : y ∣ x) : IsRelP
rime (x - 1) y
-/
lemma sub_one_right_of_dvd (h : x ∣ y) : IsRelPrime x (y - 1) :=
  isRelPrime_comm.mp (sub_one_left_of_dvd h)
/-
**IsRelPrime.add_one_sub_one_of_two_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsRelPrime`。
形式化陈述：add_one_sub_one_of_two_dvd (h : 2 ∣ x) : IsRelPrime (x + 1) (x - 1)
参数：h : 2 ∣ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 32 条，此处仅展示前 30 条）
-/
lemma add_one_sub_one_of_two_dvd (h : 2 ∣ x) : IsRelPrime (x + 1) (x - 1) := by
  simpa [show 2 + (x - 1) = x + 1 by ring] using add_mul_left_left (sub_one_right_of_dvd h) 1

end IsRelPrime

