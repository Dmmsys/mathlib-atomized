/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Joey van Langen, Casper Putz
-/
module

public import Mathlib.Algebra.CharP.Frobenius

/-!
# Results about characteristic p reduced rings
-/

public section


open Finset

section

variable (R : Type*) [CommRing R] [IsReduced R] (p n : ℕ) [ExpChar R p]

/-
**iterateFrobenius_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterateFrobenius_inj : Function.Injective (iterateFrobenius R p n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `IsReduced.eq_zero`：∀ {R : Type u_5} {inst : Zero R} {inst_1 : Pow R ℕ} [
self : IsReduced R] (x : R), IsNilpotent x → x = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem iterateFrobenius_inj : Function.Injective (iterateFrobenius R p n) := fun x y H ↦ by
  rw [← sub_eq_zero] at H ⊢
  simp_rw [iterateFrobenius_def, ← sub_pow_expChar_pow] at H
  exact IsReduced.eq_zero _ ⟨_, H⟩
/-
**frobenius_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：frobenius_inj : Function.Injective (frobenius R p)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iterateFrobenius_inj`：iterateFrobenius_inj : Function.Injective (iterate
Frobenius R p n)
· 使用引理 `iterateFrobenius_one`：iterateFrobenius_one : iterateFrobenius R p 1 = fr
obenius R p
-/
theorem frobenius_inj : Function.Injective (frobenius R p) :=
  iterateFrobenius_one (R := R) p ▸ iterateFrobenius_inj R p 1

end

/-- If `ringChar R = 2`, where `R` is a finite reduced commutative ring,
then every `a : R` is a square. -/
/-
**isSquare_of_charTwo'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSquare_of_charTwo' {R : Type*} [Finite R] [CommRing R] [IsReduced R] [Ch
arP R 2] (a : R) : IsSquare a
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用定理 `frobenius_inj`：frobenius_inj : Function.Injective (frobenius R p)

--- 原说明 ---
If `ringChar R = 2`, where `R` is a finite reduced commutative ring,
then every `a : R` is a square.
-/
theorem isSquare_of_charTwo' {R : Type*} [Finite R] [CommRing R] [IsReduced R] [CharP R 2]
    (a : R) : IsSquare a := by
  cases nonempty_fintype R
  exact
    Exists.imp (fun b h => pow_two b ▸ Eq.symm h)
      (((Fintype.bijective_iff_injective_and_card _).mpr ⟨frobenius_inj R 2, rfl⟩).surjective a)

variable {R : Type*} [CommRing R] [IsReduced R]

@[simp]
/-
**ExpChar.pow_prime_pow_mul_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ExpChar.pow_prime_pow_mul_eq_one_iff (p k m : Nat) [ExpChar R p] (x : R) :
 x ^ (p ^ k * m) = 1 ↔ x ^ m = 1
参数：p k m : Nat；x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iterateFrobenius_inj`：iterateFrobenius_inj : Function.Injective (iterate
Frobenius R p n)
-/
theorem ExpChar.pow_prime_pow_mul_eq_one_iff (p k m : ℕ) [ExpChar R p] (x : R) :
    x ^ (p ^ k * m) = 1 ↔ x ^ m = 1 := by
  rw [pow_mul']
  convert! ← (iterateFrobenius_inj R p k).eq_iff
  apply map_one
