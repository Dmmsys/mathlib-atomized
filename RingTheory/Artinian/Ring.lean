/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Jujian Zhang
-/
module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Artinian rings

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main definitions

* `IsArtinianRing R` is the proposition that `R` is a left Artinian ring.

## Main results

* `IsArtinianRing.localization_surjective`: the canonical homomorphism from a commutative Artinian
  ring to any localization of itself is surjective.

* `IsArtinianRing.isNilpotent_jacobson_bot`: the Jacobson radical of a commutative Artinian ring
  is a nilpotent ideal.

## Implementation Details

The predicate `IsArtinianRing` is defined in `Mathlib/RingTheory/Artinian/Ring.lean` instead,
so that we can apply basic API on Artinian modules to division rings without a heavy import.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Artinian, artinian, Artinian ring, artinian ring

-/

public section

open Set Submodule IsArtinian

namespace IsArtinianRing

@[stacks 00J8]
/-
**IsArtinianRing.isNilpotent_jacobson_bot** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinianR
ing`。
形式化陈述：isNilpotent_jacobson_bot {R} [Ring R] [IsArtinianRing R] : IsNilpotent (Id
eal.jacobson (⊥ : Ideal R))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemiprimaryRing.isNilpotent`：∀ {R : Type u_1} {inst : Ring R} [self : 
IsSemiprimaryRing R], IsNilpotent (Ring.jacobson R)
· 使用定理 `IsArtinianRing.instIsSemiprimaryRing`：∀ {R : Type u_1} [inst : Ring R] [
IsArtinianRing R], IsSemiprimaryRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.jacobson_bot`：jacobson_bot : jacobson (⊥ : Ideal R) = Ring.jacobso
n R
-/
theorem isNilpotent_jacobson_bot {R} [Ring R] [IsArtinianRing R] :
    IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) :=
  Ideal.jacobson_bot (R := R) ▸ IsSemiprimaryRing.isNilpotent

variable {R : Type*} [CommRing R] [IsArtinianRing R]
/-
**IsArtinianRing.jacobson_eq_radical** 是 Mathlib 中的一个引理，位于命名空间 `IsArtinianRing`。
形式化陈述：jacobson_eq_radical (I : Ideal R) : I.jacobson = I.radical
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.radical_eq_sInf`：radical_eq_sInf (I : Ideal R) : radical I = sInf 
{ J : Ideal R | I <= J ∧ IsPrime J }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jacobson_eq_radical (I : Ideal R) : I.jacobson = I.radical := by
  simp_rw [Ideal.jacobson, Ideal.radical_eq_sInf, IsArtinianRing.isPrime_iff_isMaximal]
/-
**IsArtinianRing.isNilpotent_nilradical** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinianRin
g`。
形式化陈述：isNilpotent_nilradical : IsNilpotent (nilradical R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nilradical.eq_1`：∀ (R : Type u_3) [inst : CommSemiring R], nilradical R 
= Ideal.radical 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsArtinianRing.jacobson_eq_radical`：jacobson_eq_radical (I : Ideal R) : 
I.jacobson = I.radical
· 使用定理 `IsArtinianRing.isNilpotent_jacobson_bot`：isNilpotent_jacobson_bot {R} [R
ing R] [IsArtinianRing R] : IsNilpotent (Ideal.jacobson (⊥ : Ideal R))
-/
theorem isNilpotent_nilradical : IsNilpotent (nilradical R) := by
  rw [nilradical, ← jacobson_eq_radical]
  exact isNilpotent_jacobson_bot

variable (R) in
/-- Commutative Artinian reduced local ring is a field. -/
/-
**IsArtinianRing.isField_of_isReduced_of_isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 `
IsArtinianRing`。
形式化陈述：isField_of_isReduced_of_isLocalRing [IsReduced R] [IsLocalRing R] : IsFiel
d R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.isField`：∀ {A : Type u_1} {B : Type u_2} [inst : Semiring A] [i
nst_1 : Semiring B], IsField B → ∀ (e : A ≃* B), IsField A
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R

--- 原说明 ---
Commutative Artinian reduced local ring is a field.
-/
theorem isField_of_isReduced_of_isLocalRing [IsReduced R] [IsLocalRing R] : IsField R :=
  (IsArtinianRing.equivPi R).toRingEquiv.trans (RingEquiv.piUnique _) |>.toMulEquiv.isField
    (Ideal.Quotient.field _).toIsField

section Localization

variable (S : Submonoid R) (L : Type*) [CommSemiring L] [Algebra R L] [IsLocalization S L]
include S

/-- Localizing an Artinian ring can only reduce the amount of elements. -/
/-
**IsArtinianRing.localization_surjective** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinianRi
ng`。
形式化陈述：localization_surjective : Function.Surjective (algebraMap R L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsArtinian.exists_pow_succ_smul_dvd`：exists_pow_succ_smul_dvd (r : R) (x
 : M) : exists (n : Nat) (y : M), r ^ n.succ • y = r ^ n • x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_eq_iff_eq`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submonoid.coe_one`：coe_one : ((1 : S) : M) = 1
· 使用定理 `IsUnit.mul_left_cancel`：∀ {M : Type u_1} [inst : Monoid M] {a b c : M}, 
IsUnit a → a * b = a * c → b = c
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `IsLocalization.mk'_eq_mul_mk'_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…

--- 原说明 ---
Localizing an Artinian ring can only reduce the amount of elements.
-/
theorem localization_surjective : Function.Surjective (algebraMap R L) := by
  intro r'
  obtain ⟨r₁, s, rfl⟩ := IsLocalization.exists_mk'_eq S r'
  rsuffices ⟨r₂, h⟩ : ∃ r : R, IsLocalization.mk' L 1 s = algebraMap R L r
  · exact ⟨r₁ * r₂, by rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, h]⟩
  obtain ⟨n, r, hr⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : R)
  use r
  rw [smul_eq_mul, smul_eq_mul, pow_succ, mul_assoc] at hr
  apply_fun algebraMap R L at hr
  simp only [map_mul] at hr
  rw [← IsLocalization.mk'_one (M := S) L, IsLocalization.mk'_eq_iff_eq, mul_one,
    Submonoid.coe_one, ← (IsLocalization.map_units L (s ^ n)).mul_left_cancel hr, map_mul]
/-
**IsArtinianRing.localization_artinian** 是 Mathlib 中的一个定理，位于命名空间 `IsArtinianRing
`。
形式化陈述：localization_artinian : IsArtinianRing L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.isArtinianRing`：Function.Surjective.isArtinianRing {
R} [Semiring R] {S} [Semiring S] {F} [FunLike F R S] [RingHomClass F R S] {f : F
} (hf : Function.Surject…
· 使用定理 `IsArtinianRing.localization_surjective`：localization_surjective : Functi
on.Surjective (algebraMap R L)
-/
theorem localization_artinian : IsArtinianRing L :=
  (localization_surjective S L).isArtinianRing

/-- `IsArtinianRing.localization_artinian` can't be made an instance, as it would make `S` + `R`
into metavariables. However, this is safe. -/
/-
**IsArtinianRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsArtinianRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsArtinianRing.localization_artinian` can't be made an instance, as it would ma
ke `S` + `R`
into metavariables. However, this is safe.
-/
instance : IsArtinianRing (Localization S) :=
  localization_artinian S _

end Localization

end IsArtinianRing

