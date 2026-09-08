/-
Copyright (c) 2020 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Polynomial.Quotient
/-!
# Jacobson radical of polynomial ring

-/

public section

namespace Ideal

section Polynomial

open Polynomial

variable {R : Type*} [CommRing R]

/-
**Ideal.jacobson_bot_polynomial_le_sInf_map_maximal** 是 Mathlib 中的一个定理，位于命名空间 `I
deal`。
形式化陈述：jacobson_bot_polynomial_le_sInf_map_maximal : jacobson (⊥ : Ideal R[X]) <=
 sInf (map (C : R ->+* R[X]) '' { J : Ideal R | J.IsMaximal })
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `exists_imp`：∀ {α : Sort u_1} {p : α → Prop} {b : Prop}, (∃ x, p x) → b ↔
 ∀ (x : α), p x → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.jacobson_mono`：jacobson_mono {I J : Ideal R} : I <= J -> I.jacobso
n <= J.jacobson
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_X_one`：coeff_X_one : coeff (X : R[X]) 1 = 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
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
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
（共 44 条，此处仅展示前 30 条）
-/
theorem jacobson_bot_polynomial_le_sInf_map_maximal :
    jacobson (⊥ : Ideal R[X]) ≤ sInf (map (C : R →+* R[X]) '' { J : Ideal R | J.IsMaximal }) := by
  refine le_sInf fun J => exists_imp.2 fun j hj => ?_
  have : j.IsMaximal := hj.1
  refine Trans.trans (jacobson_mono bot_le) (le_of_eq ?_ : J.jacobson ≤ J)
  suffices t : (⊥ : Ideal (Polynomial (R ⧸ j))).jacobson = ⊥ by
    rw [← hj.2, jacobson_eq_iff_jacobson_quotient_eq_bot]
    replace t := congr_arg (map (polynomialQuotientEquivQuotientPolynomial j).toRingHom) t
    rwa [map_jacobson_of_bijective _, map_bot] at t
    exact RingEquiv.bijective (polynomialQuotientEquivQuotientPolynomial j)
  refine eq_bot_iff.2 fun f hf => ?_
  have r1 : (X : (R ⧸ j)[X]) ≠ 0 := ne_of_apply_ne (coeff · 1) <| by simp
  simpa [r1] using eq_C_of_degree_eq_zero (degree_eq_zero_of_isUnit ((mem_jacobson_bot.1 hf) X))
/-
**Ideal.jacobson_bot_polynomial_of_jacobson_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ideal
`。
形式化陈述：jacobson_bot_polynomial_of_jacobson_bot (h : jacobson (⊥ : Ideal R) = ⊥) :
 jacobson (⊥ : Ideal R[X]) = ⊥
参数：h : jacobson (⊥ : Ideal R) = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Ideal.jacobson_bot_polynomial_le_sInf_map_maximal`：jacobson_bot_polynomi
al_le_sInf_map_maximal : jacobson (⊥ : Ideal R[X]) <= sInf (map (C : R ->+* R[X]
) '' { J : Ideal R | J.IsMaximal })
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_map_C_iff`：mem_map_C_iff {I : Ideal R} {f : R[X]} : f in (Idea
l.map (C : R ->+* R[X]) I : Ideal R[X]) ↔ forall n : Nat, f.coeff n in I
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_zero`：coeff_zero (n : Nat) : coeff (0 : R[X]) n = 0
-/
theorem jacobson_bot_polynomial_of_jacobson_bot (h : jacobson (⊥ : Ideal R) = ⊥) :
    jacobson (⊥ : Ideal R[X]) = ⊥ := by
  refine eq_bot_iff.2 (le_trans jacobson_bot_polynomial_le_sInf_map_maximal ?_)
  refine fun f hf => (Submodule.mem_bot R[X]).2 <| Polynomial.ext fun n =>
    Trans.trans (?_ : coeff f n = 0) (coeff_zero n).symm
  suffices f.coeff n ∈ Ideal.jacobson ⊥ by rwa [h, Submodule.mem_bot] at this
  exact mem_sInf.2 fun j hj => (mem_map_C_iff.1 ((mem_sInf.1 hf) ⟨j, ⟨hj.2, rfl⟩⟩)) n

end Polynomial

end Ideal

