/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.ZMod.Basic

/-!
# The `ZMod n`-algebra structure on rings whose characteristic divides `n`
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace ZMod

variable (R : Type*) [Ring R]

/-
**ZMod.** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : ℕ) : Subsingleton (Algebra (ZMod p) R) :=
  ⟨fun _ _ => Algebra.algebra_ext _ _ <| RingHom.congr_fun <| Subsingleton.elim _ _⟩

section

variable {n : ℕ} (m : ℕ) [CharP R m]

/-- The `ZMod n`-algebra structure on rings whose characteristic `m` divides `n`.
See note [reducible non-instances]. -/
/-
**ZMod.algebra'** 是 Mathlib 中的一个缩写定义，位于命名空间 `ZMod`。
形式化陈述：algebra' (h : m ∣ n) : Algebra (ZMod n) R where algebraMap
参数：h : m ∣ n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ZMod n`-algebra structure on rings whose characteristic `m` divides `n`.
See note [reducible non-instances].
-/
abbrev algebra' (h : m ∣ n) : Algebra (ZMod n) R where
  algebraMap := ZMod.castHom h R
  smul := fun a r => cast a * r
  commutes' := fun a r =>
    show (cast a * r : R) = r * cast a by
      rcases ZMod.intCast_surjective a with ⟨k, rfl⟩
      change ZMod.castHom h R k * r = r * ZMod.castHom h R k
      rw [map_intCast, Int.cast_comm]
  smul_def' := fun _ _ => rfl

end

/-- The `ZMod p`-algebra structure on a ring of characteristic `p`. This is not an
instance since it creates a diamond with `Algebra.id`.
See note [reducible non-instances]. -/
/-
**ZMod.algebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `ZMod`。
形式化陈述：algebra (p : Nat) [CharP R p] : Algebra (ZMod p) R
参数：p : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a

--- 原说明 ---
The `ZMod p`-algebra structure on a ring of characteristic `p`. This is not an
instance since it creates a diamond with `Algebra.id`.
See note [reducible non-instances].
-/
abbrev algebra (p : ℕ) [CharP R p] : Algebra (ZMod p) R :=
  algebra' R p dvd_rfl

set_option backward.isDefEq.respectTransparency false in
/-- Any ring with a `ZMod p`-module structure can be upgraded to a `ZMod p`-algebra. Not an
/-
**ZMod.because** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance because this is usually not the default way, and this will cause typeclass search loop. -/
@[instance_reducible]
/-
**ZMod.algebraOfModule** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：algebraOfModule (n : Nat) (R : Type*) [Ring R] [Module (ZMod n) R] : Algeb
ra (ZMod n) R
参数：n : Nat；R : Type*；ZMod n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any ring with a `ZMod p`-module structure can be upgraded to a `ZMod p`-algebra.
 Not an
instance because this is usually not the default way, and this will cause typecl
ass search loop.
-/
def algebraOfModule (n : ℕ) (R : Type*) [Ring R] [Module (ZMod n) R] : Algebra (ZMod n) R :=
  Algebra.ofModule' (proof · · |>.1) (proof · · |>.2) where
  proof (r : ZMod n) (x : R) : r • 1 * x = r • x ∧ x * r • 1 = r • x := by
    obtain _ | n := n
    · obtain rfl : ((inferInstance : Module ℤ R)) = ‹_› := Subsingleton.elim _ _
      simp [ZMod, Int.cast_comm]
    · obtain ⟨r, rfl⟩ := ZMod.natCast_zmod_surjective r
      simp [Nat.cast_smul_eq_nsmul, Nat.cast_comm]
/-
**ZMod.instIsScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `ZMod`。
形式化陈述：instIsScalarTower (n : Nat) (R M : Type*) [Ring R] [AddCommGroup M] [Modul
e (ZMod n) R] [m₁ : Module (ZMod n) M] [Module R M] : IsScalarTower (ZMod n) R M
参数：n : Nat；R M : Type*；ZMod n；ZMod n。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance instIsScalarTower (n : ℕ) (R M : Type*) [Ring R] [AddCommGroup M]
    [Module (ZMod n) R] [m₁ : Module (ZMod n) M] [Module R M] :
    IsScalarTower (ZMod n) R M := by
  let := ZMod.algebraOfModule n R
  let m₂ := Module.compHom M (algebraMap (ZMod n) R)
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact ⟨fun x y z ↦ by rw [Algebra.smul_def, mul_smul]; rfl⟩

end ZMod

