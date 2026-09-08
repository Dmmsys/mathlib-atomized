/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.Cyclotomic.Discriminant
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
public import Mathlib.RingTheory.Prime

/-!
# Ring of integers of cyclotomic fields

We gather results about cyclotomic extensions of `ℚ`. In particular, we compute the ring of
integers of a cyclotomic extension of `ℚ`.

## Main results
* `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`: if `K` is a cyclotomic
  extension of `ℚ`, then `adjoin ℤ {ζ}` is the integral closure of `ℤ` in `K`.
* `IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure`: the integral
  closure of `ℤ` inside `CyclotomicField n ℚ` is `CyclotomicRing n ℤ ℚ`.
* `IsCyclotomicExtension.Rat.discr` and related results: the absolute discriminant
  of cyclotomic fields.
-/

@[expose] public section

universe u

open Algebra IsCyclotomicExtension Polynomial NumberField

open scoped Cyclotomic Nat

variable {p k n : ℕ} {K : Type u} [Field K] {ζ : K} [hp : Fact p.Prime]

namespace IsCyclotomicExtension.Rat

variable [CharZero K]

variable (k K) in
/-
**IsCyclotomicExtension.Rat.finrank** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicExten
sion.Rat`。
形式化陈述：finrank [NeZero k] [IsCyclotomicExtension {k} Rat K] : Module.finrank Rat 
K = k.totient
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.finrank`：finrank (hirr : Irreducible (cyclotomic n
 K)) : finrank K L = n.totient
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem finrank [NeZero k] [IsCyclotomicExtension {k} ℚ K] : Module.finrank ℚ K = k.totient :=
  IsCyclotomicExtension.finrank K <| Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)

/-- The discriminant of the power basis given by `ζ - 1`. -/
/-
**IsCyclotomicExtension.Rat.discr_prime_pow_ne_two'** 是 Mathlib 中的一个定理，位于命名空间 `I
sCyclotomicExtension.Rat`。
形式化陈述：discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ : 
IsPrimitiveRoot ζ (p ^ (k + 1))) (hk : p ^ (k + 1) != 2) : discr Rat (hζ.subOneP
owerBasis Rat).basis = (-1) ^ ((p ^ (k + 1)).totient / 2) * p ^ (p ^ k * ((p - 1
) * (k + 1) - 1))
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；hk : p ^ (k + 1) != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCyclotomicExtension.discr_prime_pow_ne_two`：discr_prime_pow_ne_two [Is
CyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact p.Prime] (hζ : IsPrimitiveRoot
 ζ (p ^ (k + 1))) (hirr : Irreduci…
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `IsPrimitiveRoot.discr_zeta_eq_discr_zeta_sub_one`：discr_zeta_eq_discr_ze
ta_sub_one (hζ : IsPrimitiveRoot ζ n) : discr Rat (hζ.powerBasis Rat).basis = di
scr Rat (hζ.subOnePowerBasis Rat).basi…

--- 原说明 ---
The discriminant of the power basis given by `ζ - 1`.
-/
theorem discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hk : p ^ (k + 1) ≠ 2) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis =
      (-1) ^ ((p ^ (k + 1)).totient / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  rw [← discr_prime_pow_ne_two hζ (cyclotomic.irreducible_rat (NeZero.pos _)) hk]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm
/-
**IsCyclotomicExtension.Rat.discr_odd_prime'** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclot
omicExtension.Rat`。
形式化陈述：discr_odd_prime' [IsCyclotomicExtension {p} Rat K] (hζ : IsPrimitiveRoot ζ
 p) (hodd : p != 2) : discr Rat (hζ.subOnePowerBasis Rat).basis = (-1) ^ ((p - 1
) / 2) * p ^ (p - 2)
参数：hζ : IsPrimitiveRoot ζ p；hodd : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCyclotomicExtension.discr_odd_prime`：discr_odd_prime [IsCyclotomicExte
nsion {p} K L] [hp : Fact p.Prime] (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducibl
e (cyclotomic p K)) (hodd :…
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `IsPrimitiveRoot.discr_zeta_eq_discr_zeta_sub_one`：discr_zeta_eq_discr_ze
ta_sub_one (hζ : IsPrimitiveRoot ζ n) : discr Rat (hζ.powerBasis Rat).basis = di
scr Rat (hζ.subOnePowerBasis Rat).basi…
-/
theorem discr_odd_prime' [IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) (hodd : p ≠ 2) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  rw [← discr_odd_prime hζ (cyclotomic.irreducible_rat hp.out.pos) hodd]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

/-- The discriminant of the power basis given by `ζ - 1`. Beware that in the cases `p ^ k = 1` and
`p ^ k = 2` the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to have a uniform
result. See also `IsCyclotomicExtension.Rat.discr_prime_pow_eq_unit_mul_pow'`. -/
/-
**IsCyclotomicExtension.Rat.discr_prime_pow'** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclot
omicExtension.Rat`。
形式化陈述：discr_prime_pow' [IsCyclotomicExtension {p ^ k} Rat K] (hζ : IsPrimitiveRo
ot ζ (p ^ k)) : discr Rat (hζ.subOnePowerBasis Rat).basis = (-1) ^ ((p ^ k).toti
ent / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1))
参数：hζ : IsPrimitiveRoot ζ (p ^ k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCyclotomicExtension.discr_prime_pow`：discr_prime_pow [hcycl : IsCyclot
omicExtension {p ^ k} K L] [hp : Fact p.Prime] (hζ : IsPrimitiveRoot ζ (p ^ k)) 
(hirr : Irreducible (cyclot…
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `IsPrimitiveRoot.discr_zeta_eq_discr_zeta_sub_one`：discr_zeta_eq_discr_ze
ta_sub_one (hζ : IsPrimitiveRoot ζ n) : discr Rat (hζ.powerBasis Rat).basis = di
scr Rat (hζ.subOnePowerBasis Rat).basi…

--- 原说明 ---
The discriminant of the power basis given by `ζ - 1`. Beware that in the cases `
p ^ k = 1` and
`p ^ k = 2` the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to h
ave a uniform
result. See also `IsCyclotomicExtension.Rat.discr_prime_pow_eq_unit_mul_pow'`.
-/
theorem discr_prime_pow' [IsCyclotomicExtension {p ^ k} ℚ K] (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    discr ℚ (hζ.subOnePowerBasis ℚ).basis =
      (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  rw [← discr_prime_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))]
  exact hζ.discr_zeta_eq_discr_zeta_sub_one.symm

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then there are `u : ℤˣ` and
`n : ℕ` such that the discriminant of the power basis given by `ζ - 1` is `u * p ^ n`. Often this is
enough and less cumbersome to use than `IsCyclotomicExtension.Rat.discr_prime_pow'`. -/
/-
**IsCyclotomicExtension.Rat.discr_prime_pow_eq_unit_mul_pow'** 是 Mathlib 中的一个定理，
位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：discr_prime_pow_eq_unit_mul_pow' [IsCyclotomicExtension {p ^ k} Rat K] (hζ
 : IsPrimitiveRoot ζ (p ^ k)) : exists (u : Intˣ) (n : Nat), discr Rat (hζ.subOn
ePowerBasis Rat).basis = u * p ^ n
参数：hζ : IsPrimitiveRoot ζ (p ^ k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.discr_zeta_eq_discr_zeta_sub_one`：discr_zeta_eq_discr_ze
ta_sub_one (hζ : IsPrimitiveRoot ζ n) : discr Rat (hζ.powerBasis Rat).basis = di
scr Rat (hζ.subOnePowerBasis Rat).basi…
· 使用定理 `IsCyclotomicExtension.discr_prime_pow_eq_unit_mul_pow`：discr_prime_pow_e
q_unit_mul_pow [IsCyclotomicExtension {p ^ k} K L] [hp : Fact p.Prime] (hζ : IsP
rimitiveRoot ζ (p ^ k)) (hirr : Irreducible…
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a

--- 原说明 ---
If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then there are `u : ℤ
ˣ` and
`n : ℕ` such that the discriminant of the power basis given by `ζ - 1` is `u * p
 ^ n`. Often this is
enough and less cumbersome to use than `IsCyclotomicExtension.Rat.discr_prime_po
w'`.
-/
theorem discr_prime_pow_eq_unit_mul_pow' [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    ∃ (u : ℤˣ) (n : ℕ), discr ℚ (hζ.subOnePowerBasis ℚ).basis = u * p ^ n := by
  rw [hζ.discr_zeta_eq_discr_zeta_sub_one.symm]
  exact discr_prime_pow_eq_unit_mul_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _))

/-- If `K` is a `p ^ k`-th cyclotomic extension of `ℚ`, then `(adjoin ℤ {ζ})` is the
integral closure of `ℤ` in `K`. -/
/-
**IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow** 是 
Mathlib 中的一个定理，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：isIntegralClosure_adjoin_singleton_of_prime_pow [hcycl : IsCyclotomicExten
sion {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ k)) : IsIntegralClosure (adjoin
 Int ({ζ} : Set K)) Int K
参数：hζ : IsPrimitiveRoot ζ (p ^ k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsIntegral.sub`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `isIntegral_one`：isIntegral_one [Algebra R B] : IsIntegral R (1 : B)
· 使用定理 `IsCyclotomicExtension.finiteDimensional`：finiteDimensional (C : Type z) 
[Finite S] [CommRing C] [Algebra K C] [IsDomain C] [IsCyclotomicExtension S K C]
 : FiniteDimensional K C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.discr_mul_isIntegral_mem_adjoin`：discr_mul_isIntegral_mem_adjoin
 [Algebra.IsSeparable K L] [IsIntegrallyClosed R] [IsFractionRing R K] {B : Powe
rBasis K L} (hint : IsIntegra…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `IsCyclotomicExtension.Rat.discr_prime_pow_eq_unit_mul_pow'`：discr_prime_
pow_eq_unit_mul_pow' [IsCyclotomicExtension {p ^ k} Rat K] (hζ : IsPrimitiveRoot
 ζ (p ^ k)) : exists (u : Intˣ) (n : Nat), discr…
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `IsCyclotomicExtension.singleton_one`：singleton_one [h : IsCyclotomicExte
nsion {1} A B] : (⊥ : Subalgebra A B) = ⊤
· 使用定理 `Algebra.mem_top`：mem_top {x : A} : x in (⊤ : Subalgebra R A)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
· 使用定理 `isIntegral_algebraMap_iff`：isIntegral_algebraMap_iff [Algebra A B] [IsSc
alarTower R A B] {x : A} (hAB : Function.Injective (algebraMap A B)) : IsIntegra
l R (algebraMap…
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
If `K` is a `p ^ k`-th cyclotomic extension of `ℚ`, then `(adjoin ℤ {ζ})` is the
integral closure of `ℤ` in `K`.
-/
theorem isIntegralClosure_adjoin_singleton_of_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : IsIntegralClosure (adjoin ℤ ({ζ} : Set K)) ℤ K := by
  refine ⟨Subtype.val_injective, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  swap
  · rintro ⟨y, rfl⟩
    exact
      IsIntegral.algebraMap
        ((le_integralClosure_iff_isIntegral.1
          (adjoin_le_integralClosure (hζ.isIntegral (NeZero.pos _)))).isIntegral _)
  let B := hζ.subOnePowerBasis ℚ
  have hint : IsIntegral ℤ B.gen := (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one
  -- This can't be a `local instance` because it has metavariables.
  let := IsCyclotomicExtension.finiteDimensional {p ^ k} ℚ K
  have H := discr_mul_isIntegral_mem_adjoin ℚ hint h
  obtain ⟨u, n, hun⟩ := discr_prime_pow_eq_unit_mul_pow' hζ
  rw [hun] at H
  replace H := Subalgebra.smul_mem _ H u.inv
  rw [← smul_assoc, ← smul_mul_assoc, Units.inv_eq_val_inv, zsmul_eq_mul, ← Int.cast_mul,
    Units.inv_mul, Int.cast_one, one_mul, smul_def, map_pow] at H
  cases k
  · have : IsCyclotomicExtension {1} ℚ K := by simpa using hcycl
    have : x ∈ (⊥ : Subalgebra ℚ K) := by
      rw [singleton_one ℚ K]
      exact mem_top
    obtain ⟨y, rfl⟩ := mem_bot.1 this
    replace h := (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).1 h
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hz, ← IsScalarTower.algebraMap_apply]
    exact Subalgebra.algebraMap_mem _ _
  · have hmin : (minpoly ℤ B.gen).IsEisensteinAt (Submodule.span ℤ {(p : ℤ)}) := by
      have h₁ := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
      have h₂ := hζ.minpoly_sub_one_eq_cyclotomic_comp (cyclotomic.irreducible_rat (NeZero.pos _))
      rw [IsPrimitiveRoot.subOnePowerBasis_gen] at h₁
      rw [h₁, ← map_cyclotomic_int, ← algebraMap_int_eq,
        show X + 1 = map (algebraMap ℤ ℚ) (X + 1) by simp, ← map_comp] at h₂
      rw [IsPrimitiveRoot.subOnePowerBasis_gen,
        map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int h₂]
      exact cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt p _
    refine
      adjoin_le ?_
        (mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt (n := n)
          (Nat.prime_iff_prime_int.1 hp.out) hint h (by simpa using H) hmin)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe]
    exact Subalgebra.sub_mem _ (self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)
/-
**IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime** 是 Math
lib 中的一个定理，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：isIntegralClosure_adjoin_singleton_of_prime [hcycl : IsCyclotomicExtension
 {p} Rat K] (hζ : IsPrimitiveRoot ζ p) : IsIntegralClosure (adjoin Int ({ζ} : Se
t K)) Int K
参数：hζ : IsPrimitiveRoot ζ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_po
w`：isIntegralClosure_adjoin_singleton_of_prime_pow [hcycl : IsCyclotomicExtensio
n {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ k)) : IsIntegralC…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem isIntegralClosure_adjoin_singleton_of_prime [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) : IsIntegralClosure (adjoin ℤ ({ζ} : Set K)) ℤ K := by
  rw [← pow_one p] at hζ hcycl
  exact isIntegralClosure_adjoin_singleton_of_prime_pow hζ

set_option backward.isDefEq.respectTransparency false in
/-- The integral closure of `ℤ` inside `CyclotomicField (p ^ k) ℚ` is
`CyclotomicRing (p ^ k) ℤ ℚ`. -/
/-
**IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime_pow** 是 Ma
thlib 中的一个定理，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：cyclotomicRing_isIntegralClosure_of_prime_pow : IsIntegralClosure (Cycloto
micRing (p ^ k) Int Rat) Int (CyclotomicField (p ^ k) Rat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `CyclotomicField.instCharZero`：∀ (n : ℕ) (K : Type w) [inst : Field K] [C
harZero K], CharZero (CyclotomicField n K)
· 使用定理 `CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero`：∀ (n
 : ℕ) (K : Type w) [inst : Field K] [CharZero K], IsCyclotomicExtension {n} K (C
yclotomicField n K)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `CyclotomicRing.instIsFractionRingCyclotomicFieldOfIsDomainOfNeZeroCast`：
∀ (n : ℕ) [NeZero n] (A : Type u) (K : Type w) [inst : CommRing A] [inst_1 : Fie
ld K] [inst_2 : Algebra A K]   [IsFractionRing A K] [IsDomai…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Int.instNeZeroCastOfNat`：∀ {n : ℕ} [NeZero n], NeZero ↑n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_po
w`：isIntegralClosure_adjoin_singleton_of_prime_pow [hcycl : IsCyclotomicExtensio
n {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ k)) : IsIntegralC…
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `IsPrimitiveRoot.pow_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M] {ζ : 
M} {k : ℕ}, IsPrimitiveRoot ζ k → ζ ^ k = 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `IsCyclotomicExtension.integral`：integral [IsCyclotomicExtension S A B] :
 Algebra.IsIntegral A B

--- 原说明 ---
The integral closure of `ℤ` inside `CyclotomicField (p ^ k) ℚ` is
`CyclotomicRing (p ^ k) ℤ ℚ`.
-/
theorem cyclotomicRing_isIntegralClosure_of_prime_pow :
    IsIntegralClosure (CyclotomicRing (p ^ k) ℤ ℚ) ℤ (CyclotomicField (p ^ k) ℚ) := by
  have hζ := zeta_spec (p ^ k) ℚ (CyclotomicField (p ^ k) ℚ)
  refine ⟨IsFractionRing.injective _ _, @fun x => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singleton_subset_iff, Set.mem_ofPred_eq]
    exact hζ.pow_eq_one
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap ((IsCyclotomicExtension.integral {p ^ k} ℤ _).isIntegral _)
/-
**IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime** 是 Mathli
b 中的一个定理，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：cyclotomicRing_isIntegralClosure_of_prime : IsIntegralClosure (CyclotomicR
ing p Int Rat) Int (CyclotomicField p Rat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure_of_prime_pow`
：cyclotomicRing_isIntegralClosure_of_prime_pow : IsIntegralClosure (CyclotomicRi
ng (p ^ k) Int Rat) Int (CyclotomicField (p ^ k) Rat)
-/
theorem cyclotomicRing_isIntegralClosure_of_prime :
    IsIntegralClosure (CyclotomicRing p ℤ ℚ) ℤ (CyclotomicField p ℚ) := by
  rw [← pow_one p]
  exact cyclotomicRing_isIntegralClosure_of_prime_pow

end IsCyclotomicExtension.Rat

section PowerBasis

open IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

section CharZero

variable [CharZero K]

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `p ^ k`-th root of
unity and `K` is a `p ^ k`-th cyclotomic extension of `ℚ`. -/
@[simps!]
/-
**IsPrimitiveRoot._root_.IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow** 是
 Mathlib 中的一个定义，位于命名空间 `IsPrimitiveRoot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `p 
^ k`-th root of
unity and `K` is a `p ^ k`-th cyclotomic extension of `ℚ`.
-/
noncomputable def _root_.IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow
    [IsCyclotomicExtension {p ^ k} ℚ K] (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    adjoin ℤ ({ζ} : Set K) ≃ₐ[ℤ] 𝓞 K :=
  let _ := isIntegralClosure_adjoin_singleton_of_prime_pow hζ
  IsIntegralClosure.equiv ℤ (adjoin ℤ ({ζ} : Set K)) K (𝓞 K)

/-- The ring of integers of a `p ^ k`-th cyclotomic extension of `ℚ` is a cyclotomic extension. -/
/-
**IsPrimitiveRoot.IsCyclotomicExtension.ringOfIntegersOfPrimePow** 是 Mathlib 中的一
个定理，位于命名空间 `IsPrimitiveRoot.IsCyclotomicExtension`。
形式化陈述：∀ {p k : ℕ} {K : Type u} [inst : Field K] [hp : Fact (Nat.Prime p)] [inst_
1 : CharZero K]   [IsCyclotomicExtension {p ^ k} ℚ K], IsCyclotomicExtension {p 
^ k} ℤ (NumberField.RingOfIntegers K)
参数：Nat.Prime p；NumberField.RingOfIntegers K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsPrimitiveRoot.adjoin_isCyclotomicExtension`：∀ (A : Type u) {B : Type v
} [inst : CommRing A] [inst_1 : CommRing B] [inst_2 : Algebra A B] {ζ : B} {n : 
ℕ} [NeZero n],   IsPrimitiveRoot ζ…
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `IsCyclotomicExtension.equiv`：equiv {C : Type*} [CommRing C] [Algebra A C
] [h : IsCyclotomicExtension S A B] (f : B ≃ₐ[A] C) : IsCyclotomicExtension S A 
C

--- 原说明 ---
The ring of integers of a `p ^ k`-th cyclotomic extension of `ℚ` is a cyclotomic
 extension.
-/
instance IsCyclotomicExtension.ringOfIntegersOfPrimePow [IsCyclotomicExtension {p ^ k} ℚ K] :
    IsCyclotomicExtension {p ^ k} ℤ (𝓞 K) :=
  let _ := (zeta_spec (p ^ k) ℚ K).adjoin_isCyclotomicExtension ℤ
  IsCyclotomicExtension.equiv _ ℤ _ (zeta_spec (p ^ k) ℚ K).adjoinEquivRingOfIntegersOfPrimePow

/-- The integral `PowerBasis` of `𝓞 K` given by a primitive root of unity, where `K` is a `p ^ k`
cyclotomic extension of `ℚ`. -/
/-
**IsPrimitiveRoot.integralPowerBasisOfPrimePow** 是 Mathlib 中的一个定义，位于命名空间 `IsPrim
itiveRoot`。
形式化陈述：integralPowerBasisOfPrimePow [IsCyclotomicExtension {p ^ k} Rat K] (hζ : I
sPrimitiveRoot ζ (p ^ k)) : PowerBasis Int (𝓞 K)
参数：hζ : IsPrimitiveRoot ζ (p ^ k)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin.powerBasis'`：Algebra.adjoin.powerBasis'_minpoly_gen [IsDo
main R] [IsDomain S] [IsTorsionFree R S] [IsIntegrallyClosed R] {x : S} (hx' : I
sIntegral R x) :…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ

--- 原说明 ---
The integral `PowerBasis` of `𝓞 K` given by a primitive root of unity, where `K`
 is a `p ^ k`
cyclotomic extension of `ℚ`.
-/
noncomputable def integralPowerBasisOfPrimePow [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : PowerBasis ℤ (𝓞 K) :=
  (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map
    hζ.adjoinEquivRingOfIntegersOfPrimePow

/-- Abbreviation to see a primitive root of unity as a member of the ring of integers. -/
/-
**IsPrimitiveRoot.toInteger** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：toInteger {k : Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : 𝓞 K
参数：hζ : IsPrimitiveRoot ζ k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Abbreviation to see a primitive root of unity as a member of the ring of integer
s.
-/
abbrev toInteger {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : 𝓞 K :=
  ⟨ζ, hζ.isIntegral (NeZero.pos _)⟩

end CharZero

/-
**IsPrimitiveRoot.coe_toInteger** 是 Mathlib 中的一个引理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：coe_toInteger {k : Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : hζ.toInteg
er.1 = ζ
参数：hζ : IsPrimitiveRoot ζ k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toInteger {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : hζ.toInteger.1 = ζ := rfl

@[simp]
/-
**IsPrimitiveRoot.toInteger_coe** 是 Mathlib 中的一个引理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：toInteger_coe {k : Nat} [NeZero k] {x : 𝓞 K} (hx : IsPrimitiveRoot (x : K)
 k) : hx.toInteger = x
参数：hx : IsPrimitiveRoot (x : K) k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toInteger_coe {k : ℕ} [NeZero k] {x : 𝓞 K} (hx : IsPrimitiveRoot (x : K) k) :
    hx.toInteger = x := rfl

/-- `𝓞 K ⧸ Ideal.span {ζ - 1}` is finite. -/
/-
**IsPrimitiveRoot.finite_quotient_toInteger_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `I
sPrimitiveRoot`。
形式化陈述：finite_quotient_toInteger_sub_one [NumberField K] {k : Nat} (hk : 1 < k) (
hζ : IsPrimitiveRoot ζ k) : haveI : NeZero k
参数：hk : 1 < k；hζ : IsPrimitiveRoot ζ k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.finiteQuotientOfFreeOfNeBot`：finiteQuotientOfFreeOfNeBot [Module.F
ree Int S] [Module.Finite Int S] (I : Ideal S) (hI : I != ⊥) : Finite (S ⧸ I)
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NeZero.of_gt`：of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero
 b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `IsPrimitiveRoot.ne_one`：ne_one (h : IsPrimitiveRoot ζ k) (hk : 1 < k) : 
ζ != 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.RingOfIntegers.ext_iff`：∀ {K : Type u_1} [inst : Field K] {x
 y : NumberField.RingOfIntegers K}, x = y ↔ ↑x = ↑y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
`𝓞 K ⧸ Ideal.span {ζ - 1}` is finite.
-/
lemma finite_quotient_toInteger_sub_one [NumberField K] {k : ℕ} (hk : 1 < k)
    (hζ : IsPrimitiveRoot ζ k) :
    haveI : NeZero k := NeZero.of_gt hk
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h ↦ ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero] at h
  exact hζ.ne_one hk (RingOfIntegers.ext_iff.1 h)

/-- We have that `𝓞 K ⧸ Ideal.span {ζ - 1}` has cardinality equal to the norm of `ζ - 1`.

See the results below to compute this norm in various cases. -/
/-
**IsPrimitiveRoot.card_quotient_toInteger_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `IsP
rimitiveRoot`。
形式化陈述：card_quotient_toInteger_sub_one [NumberField K] {k : Nat} [NeZero k] (hζ :
 IsPrimitiveRoot ζ k) : Nat.card (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) = (Algebr
a.norm Int (hζ.toInteger - 1)).natAbs
参数：hζ : IsPrimitiveRoot ζ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.cardQuot_apply`：cardQuot_apply (S : Submodule R M) : cardQuot 
S = Nat.card (M ⧸ S)
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.absNorm_apply`：absNorm_apply (I : Ideal S) : absNorm I = cardQuot 
I
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)

--- 原说明 ---
We have that `𝓞 K ⧸ Ideal.span {ζ - 1}` has cardinality equal to the norm of `ζ 
- 1`.

See the results below to compute this norm in various cases.
-/
lemma card_quotient_toInteger_sub_one [NumberField K] {k : ℕ} [NeZero k]
    (hζ : IsPrimitiveRoot ζ k) :
    Nat.card (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) =
      (Algebra.norm ℤ (hζ.toInteger - 1)).natAbs := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
/-
**IsPrimitiveRoot.toInteger_isPrimitiveRoot** 是 Mathlib 中的一个引理，位于命名空间 `IsPrimiti
veRoot`。
形式化陈述：toInteger_isPrimitiveRoot {k : Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) 
: IsPrimitiveRoot hζ.toInteger k
参数：hζ : IsPrimitiveRoot ζ k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.of_map_of_injective`：of_map_of_injective [MonoidHomClass
 F M N] (h : IsPrimitiveRoot (f ζ) k) (hf : Injective f) : IsPrimitiveRoot ζ k w
here pow_eq_one
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `NumberField.RingOfIntegers.coe_injective`：coe_injective : Function.Injec
tive (algebraMap (𝓞 K) K)
-/
lemma toInteger_isPrimitiveRoot {k : ℕ} [NeZero k] (hζ : IsPrimitiveRoot ζ k) :
    IsPrimitiveRoot hζ.toInteger k :=
  IsPrimitiveRoot.of_map_of_injective (by exact hζ) RingOfIntegers.coe_injective

variable [CharZero K]

@[simp]
/-
**IsPrimitiveRoot.integralPowerBasisOfPrimePow_gen** 是 Mathlib 中的一个定理，位于命名空间 `Is
PrimitiveRoot`。
形式化陈述：integralPowerBasisOfPrimePow_gen [hcycl : IsCyclotomicExtension {p ^ k} Ra
t K] (hζ : IsPrimitiveRoot ζ (p ^ k)) : hζ.integralPowerBasisOfPrimePow.gen = hζ
.toInteger
参数：hζ : IsPrimitiveRoot ζ (p ^ k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Algebra.adjoin.powerBasis'`：Algebra.adjoin.powerBasis'_minpoly_gen [IsDo
main R] [IsDomain S] [IsTorsionFree R S] [IsIntegrallyClosed R] {x : S} (hx' : I
sIntegral R x) :…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.integralPowerBasisOfPrimePow.eq_1`：∀ {p k : ℕ} {K : Type
 u} [inst : Field K] {ζ : K} [hp : Fact (Nat.Prime p)] [inst_1 : CharZero K]   [
inst_2 : IsCyclotomicExtension {p ^ k} …
· 使用定理 `PowerBasis.map_gen`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] 
[inst_1 : Ring S] [inst_2 : Algebra R S] {S' : Type u_7}   [inst_3 : CommRing S'
] [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Algebra.adjoin.powerBasis'_gen`：∀ {R : Type u_1} {S : Type u_2} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : IsDomain R] [inst_3 : Algebra R S]  
 [inst_4 : IsIntegra…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureInt`：∀ {K : Type u_1} [i
nst : Field K], IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
· 使用定理 `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_po
w`：isIntegralClosure_adjoin_singleton_of_prime_pow [hcycl : IsCyclotomicExtensio
n {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ k)) : IsIntegralC…
· 使用定理 `IsPrimitiveRoot.adjoinEquivRingOfIntegersOfPrimePow_apply`：∀ {p k : ℕ} {
K : Type u} [inst : Field K] {ζ : K} [hp : Fact (Nat.Prime p)] [inst_1 : CharZer
o K]   [inst_2 : IsCyclotomicExtension {p ^ k} …
· 使用定理 `IsIntegralClosure.algebraMap_lift`：algebraMap_lift (x : S) : algebraMap 
A B (lift R A B x) = algebraMap S B x
-/
theorem integralPowerBasisOfPrimePow_gen [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    hζ.integralPowerBasisOfPrimePow.gen = hζ.toInteger :=
  Subtype.ext <| show algebraMap _ K hζ.integralPowerBasisOfPrimePow.gen = _ by
    rw [integralPowerBasisOfPrimePow, PowerBasis.map_gen, adjoin.powerBasis'_gen]
    simp only [adjoinEquivRingOfIntegersOfPrimePow_apply, IsIntegralClosure.algebraMap_lift]
    rfl

/- We name `hcycl` so it can be used as a named argument. -/
@[simp]
/-
**IsPrimitiveRoot.integralPowerBasisOfPrimePow_dim** 是 Mathlib 中的一个定理，位于命名空间 `Is
PrimitiveRoot`。
形式化陈述：integralPowerBasisOfPrimePow_dim [hcycl : IsCyclotomicExtension {p ^ k} Ra
t K] (hζ : IsPrimitiveRoot ζ (p ^ k)) : hζ.integralPowerBasisOfPrimePow.dim = φ 
(p ^ k)
参数：hζ : IsPrimitiveRoot ζ (p ^ k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin.powerBasis'`：Algebra.adjoin.powerBasis'_minpoly_gen [IsDo
main R] [IsDomain S] [IsTorsionFree R S] [IsIntegrallyClosed R] {x : S} (hx' : I
sIntegral R x) :…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `PowerBasis.map_dim`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] 
[inst_1 : Ring S] [inst_2 : Algebra R S] {S' : Type u_7}   [inst_3 : CommRing S'
] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.cyclotomic_eq_minpoly`：cyclotomic_eq_minpoly {n : Nat} {K : T
ype*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : 
cyclotomic n Int = min…
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Polynomial.natDegree_cyclotomic`：natDegree_cyclotomic (n : Nat) (R : Typ
e*) [Ring R] [Nontrivial R] : (cyclotomic n R).natDegree = Nat.totient n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We name `hcycl` so it can be used as a named argument.
-/
theorem integralPowerBasisOfPrimePow_dim [hcycl : IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : hζ.integralPowerBasisOfPrimePow.dim = φ (p ^ k) := by
  simp [integralPowerBasisOfPrimePow, ← cyclotomic_eq_minpoly hζ (NeZero.pos _),
    natDegree_cyclotomic]

set_option backward.isDefEq.respectTransparency.types false in
/-- The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p ^ k` cyclotomic
extension of `ℚ`. -/
/-
**IsPrimitiveRoot.subOneIntegralPowerBasisOfPrimePow** 是 Mathlib 中的一个定义，位于命名空间 `
IsPrimitiveRoot`。
形式化陈述：subOneIntegralPowerBasisOfPrimePow [IsCyclotomicExtension {p ^ k} Rat K] (
hζ : IsPrimitiveRoot ζ (p ^ k)) : PowerBasis Int (𝓞 K)
参数：hζ : IsPrimitiveRoot ζ (p ^ k)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)

--- 原说明 ---
The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a `p ^ k` cycl
otomic
extension of `ℚ`.
-/
noncomputable def subOneIntegralPowerBasisOfPrimePow [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) : PowerBasis ℤ (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasisOfPrimePow.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert! Subalgebra.add_mem _ (self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)
    simp [RingOfIntegers.ext_iff, integralPowerBasisOfPrimePow_gen, toInteger])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**IsPrimitiveRoot.subOneIntegralPowerBasisOfPrimePow_gen** 是 Mathlib 中的一个定理，位于命名
空间 `IsPrimitiveRoot`。
形式化陈述：subOneIntegralPowerBasisOfPrimePow_gen [IsCyclotomicExtension {p ^ k} Rat 
K] (hζ : IsPrimitiveRoot ζ (p ^ k)) : hζ.subOneIntegralPowerBasisOfPrimePow.gen 
= ⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (NeZero.pos _)) (Subalgebra.one_me
m _)⟩
参数：hζ : IsPrimitiveRoot ζ (p ^ k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subalgebra.sub_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x y : A},   x ∈ S → y
 ∈ S → x…
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerBasis.ofAdjoinEqTop'_gen`：∀ {R : Type u_1} {S : Type u_2} [inst : C
ommRing R] [inst_1 : CommRing S] [inst_2 : IsDomain R] [inst_3 : Algebra R S]   
[inst_4 : IsIntegra…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subOneIntegralPowerBasisOfPrimePow_gen [IsCyclotomicExtension {p ^ k} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) :
    hζ.subOneIntegralPowerBasisOfPrimePow.gen =
      ⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (NeZero.pos _)) (Subalgebra.one_mem _)⟩ := by
  simp [subOneIntegralPowerBasisOfPrimePow]

set_option backward.isDefEq.respectTransparency.types false in
/-- `ζ - 1` is prime if `p ≠ 2` and `ζ` is a primitive `p ^ (k + 1)`-th root of unity.
  See `zeta_sub_one_prime` for a general statement. -/
/-
**IsPrimitiveRoot.zeta_sub_one_prime_of_ne_two** 是 Mathlib 中的一个定理，位于命名空间 `IsPrim
itiveRoot`。
形式化陈述：zeta_sub_one_prime_of_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K] (
hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) : Prime (hζ.toInteger - 1)
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；hodd : p != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Ideal.prime_of_irreducible_absNorm_span`：prime_of_irreducible_absNorm_sp
an {a : S} (ha : a != 0) (hI : Irreducible (Ideal.absNorm (Ideal.span ({a} : Set
 S)))) : Prime a
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsPrimitiveRoot.pow_ne_one_of_pos_of_lt`：pow_ne_one_of_pos_of_lt (h : Is
PrimitiveRoot ζ k) (h0 : l != 0) (hl : l < k) : ζ ^ l != 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_lt_pow₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 < a → ∀ {n : ℕ}, n ≠ 
0…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
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
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
`ζ - 1` is prime if `p ≠ 2` and `ζ` is a primitive `p ^ (k + 1)`-th root of unit
y.
  See `zeta_sub_one_prime` for a general statement.
-/
theorem zeta_sub_one_prime_of_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (hζ.toInteger - 1) := by
  let := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h ↦ ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt one_ne_zero (one_lt_pow₀ hp.out.one_lt (by simp))
    rw [sub_eq_zero] at h
    simpa using congrArg (algebraMap _ K) h
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  convert! Nat.prime_iff_prime_int.1 hp.out
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ)]
  simp only [algebraMap_int_eq, map_natCast]
  exact hζ.norm_sub_one_of_prime_ne_two (Polynomial.cyclotomic.irreducible_rat (NeZero.pos _)) hodd

set_option backward.isDefEq.respectTransparency.types false in
/-- `ζ - 1` is prime if `ζ` is a primitive `2 ^ (k + 1)`-th root of unity.
  See `zeta_sub_one_prime` for a general statement. -/
/-
**IsPrimitiveRoot.zeta_sub_one_prime_of_two_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsPri
mitiveRoot`。
形式化陈述：zeta_sub_one_prime_of_two_pow [IsCyclotomicExtension {2 ^ (k + 1)} Rat K] 
(hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) : Prime (hζ.toInteger - 1)
参数：k + 1；hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Ideal.prime_of_irreducible_absNorm_span`：prime_of_irreducible_absNorm_sp
an {a : S} (ha : a != 0) (hI : Irreducible (Ideal.absNorm (Ideal.span ({a} : Set
 S)))) : Prime a
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPrimitiveRoot.pow_ne_one_of_pos_of_lt`：pow_ne_one_of_pos_of_lt (h : Is
PrimitiveRoot ζ k) (h0 : l != 0) (hl : l < k) : ζ ^ l != 1
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `one_lt_pow₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 < a → ∀ {n : ℕ}, n ≠ 
0…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
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
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Nat.irreducible_iff_prime`：irreducible_iff_prime {p : Nat} : Irreducible
 p ↔ _root_.Prime p
· 使用定理 `Ideal.absNorm_span_singleton`：absNorm_span_singleton (r : S) : absNorm (
span ({r} : Set S)) = (Algebra.norm Int r).natAbs
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
`ζ - 1` is prime if `ζ` is a primitive `2 ^ (k + 1)`-th root of unity.
  See `zeta_sub_one_prime` for a general statement.
-/
theorem zeta_sub_one_prime_of_two_pow [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    Prime (hζ.toInteger - 1) := by
  have := IsCyclotomicExtension.numberField {2 ^ (k + 1)} ℚ K
  refine Ideal.prime_of_irreducible_absNorm_span (fun h ↦ ?_) ?_
  · apply hζ.pow_ne_one_of_pos_of_lt one_ne_zero (one_lt_pow₀ (by decide) (by simp))
    rw [sub_eq_zero] at h
    simpa using! congrArg (algebraMap _ K) h
  rw [Nat.irreducible_iff_prime, Ideal.absNorm_span_singleton, ← Nat.prime_iff,
    ← Int.prime_iff_natAbs_prime]
  cases k
  · convert! Prime.neg Int.prime_two
    apply RingHom.injective_int (algebraMap ℤ ℚ)
    rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ)]
    simp only [algebraMap_int_eq, map_neg, map_ofNat]
    simpa only [zero_add, pow_one, AddSubgroupClass.coe_sub, OneMemClass.coe_one,
        pow_zero]
      using! hζ.norm_pow_sub_one_two (cyclotomic.irreducible_rat
        (by simp only [zero_add, pow_one, Nat.ofNat_pos]))
  convert! Int.prime_two
  apply RingHom.injective_int (algebraMap ℤ ℚ)
  rw [← Algebra.norm_localization (Sₘ := K) ℤ (nonZeroDivisors ℤ), algebraMap_int_eq]
  exact hζ.norm_sub_one_two Nat.AtLeastTwo.prop (cyclotomic.irreducible_rat (by simp))

/-- `ζ - 1` is prime if `ζ` is a primitive `p ^ (k + 1)`-th root of unity. -/
/-
**IsPrimitiveRoot.zeta_sub_one_prime** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`
。
形式化陈述：zeta_sub_one_prime [IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ : IsPri
mitiveRoot ζ (p ^ (k + 1))) : Prime (hζ.toInteger - 1)
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsPrimitiveRoot.zeta_sub_one_prime_of_two_pow`：zeta_sub_one_prime_of_two
_pow [IsCyclotomicExtension {2 ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (2 ^ (k
 + 1))) : Prime (hζ.toInteger - 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.zeta_sub_one_prime_of_ne_two`：zeta_sub_one_prime_of_ne_t
wo [IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k +
 1))) (hodd : p != 2) : Prime (hζ.…

--- 原说明 ---
`ζ - 1` is prime if `ζ` is a primitive `p ^ (k + 1)`-th root of unity.
-/
theorem zeta_sub_one_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : Prime (hζ.toInteger - 1) := by
  by_cases htwo : p = 2
  · subst htwo
    apply hζ.zeta_sub_one_prime_of_two_pow
  · apply hζ.zeta_sub_one_prime_of_ne_two htwo

/-- `ζ - 1` is prime if `ζ` is a primitive `p`-th root of unity. -/
/-
**IsPrimitiveRoot.zeta_sub_one_prime'** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot
`。
形式化陈述：zeta_sub_one_prime' [h : IsCyclotomicExtension {p} Rat K] (hζ : IsPrimitiv
eRoot ζ p) : Prime ((hζ.toInteger - 1))
参数：hζ : IsPrimitiveRoot ζ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `IsPrimitiveRoot.zeta_sub_one_prime`：zeta_sub_one_prime [IsCyclotomicExte
nsion {p ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : Prime (hζ.to
Integer - 1)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
`ζ - 1` is prime if `ζ` is a primitive `p`-th root of unity.
-/
theorem zeta_sub_one_prime' [h : IsCyclotomicExtension {p} ℚ K] (hζ : IsPrimitiveRoot ζ p) :
    Prime ((hζ.toInteger - 1)) := by
  convert! zeta_sub_one_prime (k := 0) (by simpa only [zero_add, pow_one])
  simpa only [zero_add, pow_one]
/-
**IsPrimitiveRoot.subOneIntegralPowerBasisOfPrimePow_gen_prime** 是 Mathlib 中的一个定
理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：subOneIntegralPowerBasisOfPrimePow_gen_prime [IsCyclotomicExtension {p ^ (
k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : Prime hζ.subOneIntegralP
owerBasisOfPrimePow.gen
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.sub_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x y : A},   x ∈ S → y
 ∈ S → x…
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.subOneIntegralPowerBasisOfPrimePow_gen`：subOneIntegralPo
werBasisOfPrimePow_gen [IsCyclotomicExtension {p ^ k} Rat K] (hζ : IsPrimitiveRo
ot ζ (p ^ k)) : hζ.subOneIntegralPowerBasisO…
· 使用定理 `IsPrimitiveRoot.zeta_sub_one_prime`：zeta_sub_one_prime [IsCyclotomicExte
nsion {p ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : Prime (hζ.to
Integer - 1)
-/
theorem subOneIntegralPowerBasisOfPrimePow_gen_prime [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    Prime hζ.subOneIntegralPowerBasisOfPrimePow.gen := by
  simpa only [subOneIntegralPowerBasisOfPrimePow_gen] using! hζ.zeta_sub_one_prime

set_option backward.isDefEq.respectTransparency.types false in
/--
The norm, relative to `ℤ`, of `ζ - 1` in an `n`-th cyclotomic extension of `ℚ` where `n` is not a
power of a prime number is `1`.
-/
/-
**IsPrimitiveRoot.norm_toInteger_sub_one_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `IsPri
mitiveRoot`。
形式化陈述：norm_toInteger_sub_one_eq_one {n : Nat} [IsCyclotomicExtension {n} Rat K] 
(hζ : IsPrimitiveRoot ζ n) (h₁ : 2 < n) (h₂ : forall {p : Nat}, Nat.Prime p -> f
orall (k : Nat), p ^ k != n) : have : NeZero n
参数：hζ : IsPrimitiveRoot ζ n；h₁ : 2 < n；h₂ : forall {p : Nat}, Nat.Prime p -> for
all (k : Nat), p ^ k != n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `NeZero.of_gt`：of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero
 b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.norm_eq_iff`：Algebra.norm_eq_iff [Module.Free R S] [Module.Finit
e R S] {a : S} {b : R} (hM : M <= nonZeroDivisors R) : Algebra.norm R a = b ↔ (A
lgebra.no…
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `NumberField.RingOfIntegers.map_mk`：∀ {K : Type u_1} [inst : Field K] (x 
: K) (hx : x ∈ integralClosure ℤ K),   (algebraMap (NumberField.RingOfIntegers K
) K) ⟨x, hx⟩ = x
· 使用定理 `IsPrimitiveRoot.sub_one_norm_eq_eval_cyclotomic`：sub_one_norm_eq_eval_cy
clotomic [IsCyclotomicExtension {n} K L] (h : 2 < n) (hirr : Irreducible (cyclot
omic n K)) : norm K (ζ - 1) = ↑(eval …
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `Polynomial.eval_one_cyclotomic_not_prime_pow`：eval_one_cyclotomic_not_pr
ime_pow {R : Type*} [Ring R] {n : Nat} (h : forall {p : Nat}, p.Prime -> forall 
k : Nat, p ^ k != n) : eval 1 (cyc…
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ - 1` in an `n`-th cyclotomic extension of `ℚ` w
here `n` is not a
power of a prime number is `1`.
-/
theorem norm_toInteger_sub_one_eq_one {n : ℕ} [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) (h₁ : 2 < n) (h₂ : ∀ {p : ℕ}, Nat.Prime p → ∀ (k : ℕ), p ^ k ≠ n) :
    have : NeZero n := NeZero.of_gt h₁
    norm ℤ (hζ.toInteger - 1) = 1 := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  have : NeZero n := NeZero.of_gt h₁
  dsimp only
  rw [norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) le_rfl, map_sub, map_one, map_one, RingOfIntegers.map_mk,
    sub_one_norm_eq_eval_cyclotomic hζ h₁ (cyclotomic.irreducible_rat (NeZero.pos _)),
    eval_one_cyclotomic_not_prime_pow h₂, Int.cast_one]

set_option backward.isDefEq.respectTransparency.types false in
/-- The norm, relative to `ℤ`, of `ζ ^ p ^ s - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ`
is `p ^ p ^ s` if `s ≤ k` and `p ^ (k - s + 1) ≠ 2`. -/
/-
**IsPrimitiveRoot.norm_toInteger_pow_sub_one_of_prime_pow_ne_two** 是 Mathlib 中的一
个引理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：norm_toInteger_pow_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p ^
 (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : Nat} (hs : s <= k) 
(htwo : p ^ (k - s + 1) != 2) : Algebra.norm Int (hζ.toInteger ^ p ^ s - 1) = p 
^ p ^ s
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；hs : s <= k；htwo : p ^ (k - s + 1)
 != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.norm_eq_iff`：Algebra.norm_eq_iff [Module.Free R S] [Module.Finit
e R S] {a : S} {b : R} (hM : M <= nonZeroDivisors R) : Algebra.norm R a = b ↔ (A
lgebra.no…
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsPrimitiveRoot.norm_pow_sub_one_of_prime_pow_ne_two`：norm_pow_sub_one_o
f_prime_pow_ne_two {k s : Nat} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) [hpri : Fa
ct p.Prime] [IsCyclotomicExtension {p ^ (k…
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ ^ p ^ s - 1` in a `p ^ (k + 1)`-th cyclotomic e
xtension of `ℚ`
is `p ^ p ^ s` if `s ≤ k` and `p ^ (k - s + 1) ≠ 2`.
-/
lemma norm_toInteger_pow_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : ℕ} (hs : s ≤ k) (htwo : p ^ (k - s + 1) ≠ 2) :
    Algebra.norm ℤ (hζ.toInteger ^ p ^ s - 1) = p ^ p ^ s := by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) le_rfl]
  simp [hζ.norm_pow_sub_one_of_prime_pow_ne_two (cyclotomic.irreducible_rat (NeZero.pos _)) hs htwo]

set_option backward.isDefEq.respectTransparency.types false in
/-- The norm, relative to `ℤ`, of `ζ ^ 2 ^ k - 1` in a `2 ^ (k + 1)`-th cyclotomic extension of `ℚ`
is `(-2) ^ 2 ^ k`. -/
/-
**IsPrimitiveRoot.norm_toInteger_pow_sub_one_of_two** 是 Mathlib 中的一个引理，位于命名空间 `I
sPrimitiveRoot`。
形式化陈述：norm_toInteger_pow_sub_one_of_two [IsCyclotomicExtension {2 ^ (k + 1)} Rat
 K] (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) : Algebra.norm Int (hζ.toInteger ^ 2 
^ k - 1) = (-2) ^ 2 ^ k
参数：k + 1；hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.norm_eq_iff`：Algebra.norm_eq_iff [Module.Free R S] [Module.Finit
e R S] {a : S} {b : R} (hM : M <= nonZeroDivisors R) : Algebra.norm R a = b ↔ (A
lgebra.no…
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsPrimitiveRoot.norm_pow_sub_one_two`：norm_pow_sub_one_two {k : Nat} (hζ
 : IsPrimitiveRoot ζ (2 ^ (k + 1))) [IsCyclotomicExtension {2 ^ (k + 1)} K L] (h
irr : Irreducible (cycloto…
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ ^ 2 ^ k - 1` in a `2 ^ (k + 1)`-th cyclotomic e
xtension of `ℚ`
is `(-2) ^ 2 ^ k`.
-/
lemma norm_toInteger_pow_sub_one_of_two [IsCyclotomicExtension {2 ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 1))) :
    Algebra.norm ℤ (hζ.toInteger ^ 2 ^ k - 1) = (-2) ^ 2 ^ k := by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 1)} ℚ K
  rw [Algebra.norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) le_rfl]
  simp [hζ.norm_pow_sub_one_two (cyclotomic.irreducible_rat (pow_pos (by decide) _))]

/-- The norm, relative to `ℤ`, of `ζ ^ p ^ s - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ`
is `p ^ p ^ s` if `s ≤ k` and `p ≠ 2`. -/
/-
**IsPrimitiveRoot.norm_toInteger_pow_sub_one_of_prime_ne_two** 是 Mathlib 中的一个引理，
位于命名空间 `IsPrimitiveRoot`。
形式化陈述：norm_toInteger_pow_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k 
+ 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : Nat} (hs : s <= k) (hod
d : p != 2) : Algebra.norm Int (hζ.toInteger ^ p ^ s - 1) = p ^ p ^ s
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；hs : s <= k；hodd : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsPrimitiveRoot.norm_toInteger_pow_sub_one_of_prime_pow_ne_two`：norm_toI
nteger_pow_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat 
K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : Nat} …
· 使用定理 `eq_of_prime_pow_eq`：eq_of_prime_pow_eq (hp₁ : Prime p₁) (hp₂ : Prime p₂)
 (hk₁ : 0 < k₁) (h : p₁ ^ k₁ = p₂ ^ k₂) : p₁ = p₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ ^ p ^ s - 1` in a `p ^ (k + 1)`-th cyclotomic e
xtension of `ℚ`
is `p ^ p ^ s` if `s ≤ k` and `p ≠ 2`.
-/
lemma norm_toInteger_pow_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : ℕ} (hs : s ≤ k) (hodd : p ≠ 2) :
    Algebra.norm ℤ (hζ.toInteger ^ p ^ s - 1) = p ^ p ^ s := by
  refine hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two hs (fun h ↦ hodd ?_)
  apply eq_of_prime_pow_eq hp.out.prime Nat.prime_two.prime (k - s).succ_pos
  rwa [pow_one]

set_option backward.isDefEq.respectTransparency.types false in
/--
The norm, relative to `ℤ`, of `ζ - 1` in a `2 ^ (k + 2)`-th cyclotomic extension of `ℚ` is `2`.
-/
/-
**IsPrimitiveRoot.norm_toInteger_sub_one_of_eq_two_pow** 是 Mathlib 中的一个定理，位于命名空间
 `IsPrimitiveRoot`。
形式化陈述：norm_toInteger_sub_one_of_eq_two_pow {k : Nat} {K : Type*} [Field K] {ζ : 
K} [CharZero K] [IsCyclotomicExtension {2 ^ (k + 2)} Rat K] (hζ : IsPrimitiveRoo
t ζ (2 ^ (k + 2))) : norm Int (hζ.toInteger - 1) = 2
参数：k + 2；hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.norm_eq_iff`：Algebra.norm_eq_iff [Module.Free R S] [Module.Finit
e R S] {a : S} {b : R} (hM : M <= nonZeroDivisors R) : Algebra.norm R a = b ↔ (A
lgebra.no…
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `NumberField.RingOfIntegers.map_mk`：∀ {K : Type u_1} [inst : Field K] (x 
: K) (hx : x ∈ integralClosure ℤ K),   (algebraMap (NumberField.RingOfIntegers K
) K) ⟨x, hx⟩ = x
· 使用定理 `IsPrimitiveRoot.norm_sub_one_two`：norm_sub_one_two {k : Nat} (hζ : IsPri
mitiveRoot ζ (2 ^ k)) (hk : 2 <= k) [H : IsCyclotomicExtension {2 ^ k} K L] (hir
r : Irreducible (cyclo…
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Polynomial.cyclotomic.irreducible_rat`：∀ {n : ℕ}, 0 < n → Irreducible (P
olynomial.cyclotomic n ℚ)
· 使用定理 `Nat.two_pow_pos`：∀ (w : ℕ), 0 < 2 ^ w

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ - 1` in a `2 ^ (k + 2)`-th cyclotomic extension
 of `ℚ` is `2`.
-/
theorem norm_toInteger_sub_one_of_eq_two_pow {k : ℕ} {K : Type*} [Field K]
    {ζ : K} [CharZero K] [IsCyclotomicExtension {2 ^ (k + 2)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (2 ^ (k + 2))) :
    norm ℤ (hζ.toInteger - 1) = 2 := by
  have : NumberField K := IsCyclotomicExtension.numberField {2 ^ (k + 2)} ℚ K
  rw [norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) le_rfl, map_sub, map_one, eq_intCast, Int.cast_ofNat,
    RingOfIntegers.map_mk, hζ.norm_sub_one_two (Nat.le_add_left 2 k)
    (Polynomial.cyclotomic.irreducible_rat (Nat.two_pow_pos _))]

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ` is
`p` if `p ≠ 2`. -/
/-
**IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two** 是 Mathlib 中的一个引理，位于命名
空间 `IsPrimitiveRoot`。
形式化陈述：norm_toInteger_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)
} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) : Algebra.norm I
nt (hζ.toInteger - 1) = p
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；hodd : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `IsPrimitiveRoot.norm_toInteger_pow_sub_one_of_prime_ne_two`：norm_toInteg
er_pow_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ :
 IsPrimitiveRoot ζ (p ^ (k + 1))) {s : Nat} (hs …
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension
 of `ℚ` is
`p` if `p ≠ 2`.
-/
lemma norm_toInteger_sub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    Algebra.norm ℤ (hζ.toInteger - 1) = p := by
  simpa only [pow_zero, pow_one] using
    hζ.norm_toInteger_pow_sub_one_of_prime_ne_two (Nat.zero_le _) hodd

/--
The norm, relative to `ℤ`, of `ζ - 1` in a `2`-th cyclotomic extension of `ℚ` is `-2`.
-/
/-
**IsPrimitiveRoot.norm_toInteger_sub_one_of_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Is
PrimitiveRoot`。
形式化陈述：norm_toInteger_sub_one_of_eq_two [IsCyclotomicExtension {2} Rat K] (hζ : I
sPrimitiveRoot ζ 2) : norm Int (hζ.toInteger - 1) = -2
参数：hζ : IsPrimitiveRoot ζ 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNat_pow`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → ℕ → α} {a : α} {b a' b' c : ℕ},   f = HPow.hPow →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.natPow_one`：natPow_one : Nat.pow a (nat_lit 1) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsPrimitiveRoot.toInteger.congr_simp`：∀ {K : Type u} [inst : Field K] {ζ
 ζ_1 : K} (e_ζ : ζ = ζ_1) {k k_1 : ℕ} (e_k : k = k_1) [inst_1 : NeZero k]   (hζ 
: IsPrimitiveRoot ζ k), hζ…
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `IsPrimitiveRoot.norm_toInteger_pow_sub_one_of_two`：norm_toInteger_pow_su
b_one_of_two [IsCyclotomicExtension {2 ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ
 (2 ^ (k + 1))) : Algebra.norm Int (hζ.…

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ - 1` in a `2`-th cyclotomic extension of `ℚ` is
 `-2`.
-/
theorem norm_toInteger_sub_one_of_eq_two [IsCyclotomicExtension {2} ℚ K]
    (hζ : IsPrimitiveRoot ζ 2) :
    norm ℤ (hζ.toInteger - 1) = -2 := by
  rw [show 2 = (2 ^ (0 + 1)) by norm_num] at hζ
  simpa using hζ.norm_toInteger_pow_sub_one_of_two

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p`-th cyclotomic extension of `ℚ` is `p` if
`p ≠ 2`. -/
/-
**IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two'** 是 Mathlib 中的一个引理，位于命
名空间 `IsPrimitiveRoot`。
形式化陈述：norm_toInteger_sub_one_of_prime_ne_two' [hcycl : IsCyclotomicExtension {p}
 Rat K] (hζ : IsPrimitiveRoot ζ p) (h : p != 2) : Algebra.norm Int (hζ.toInteger
 - 1) = p
参数：hζ : IsPrimitiveRoot ζ p；h : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two`：norm_toInteger_s
ub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ : IsPrimi
tiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) : …

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ - 1` in a `p`-th cyclotomic extension of `ℚ` is
 `p` if
`p ≠ 2`.
-/
lemma norm_toInteger_sub_one_of_prime_ne_two' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) (h : p ≠ 2) : Algebra.norm ℤ (hζ.toInteger - 1) = p := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.norm_toInteger_sub_one_of_prime_ne_two h

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ` is
a prime if `p ^ (k  + 1) ≠ 2`. -/
/-
**IsPrimitiveRoot.prime_norm_toInteger_sub_one_of_prime_pow_ne_two** 是 Mathlib 中
的一个引理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：prime_norm_toInteger_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p
 ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (htwo : p ^ (k + 1) !=
 2) : Prime (Algebra.norm Int (hζ.toInteger - 1))
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；htwo : p ^ (k + 1) != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用引理 `IsPrimitiveRoot.norm_toInteger_pow_sub_one_of_prime_pow_ne_two`：norm_toI
nteger_pow_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat 
K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) {s : Nat} …
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension
 of `ℚ` is
a prime if `p ^ (k  + 1) ≠ 2`.
-/
lemma prime_norm_toInteger_sub_one_of_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (htwo : p ^ (k + 1) ≠ 2) :
    Prime (Algebra.norm ℤ (hζ.toInteger - 1)) := by
  have := hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two zero_le htwo
  simp only [pow_zero, pow_one] at this
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension of `ℚ` is
a prime if `p ≠ 2`. -/
/-
**IsPrimitiveRoot.prime_norm_toInteger_sub_one_of_prime_ne_two** 是 Mathlib 中的一个引
理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：prime_norm_toInteger_sub_one_of_prime_ne_two [hcycl : IsCyclotomicExtensio
n {p ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) : 
Prime (Algebra.norm Int (hζ.toInteger - 1))
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；hodd : p != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用引理 `IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two`：norm_toInteger_s
ub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ : IsPrimi
tiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ - 1` in a `p ^ (k + 1)`-th cyclotomic extension
 of `ℚ` is
a prime if `p ≠ 2`.
-/
lemma prime_norm_toInteger_sub_one_of_prime_ne_two [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    Prime (Algebra.norm ℤ (hζ.toInteger - 1)) := by
  have := hζ.norm_toInteger_sub_one_of_prime_ne_two hodd
  rw [this]
  exact Nat.prime_iff_prime_int.1 hp.out

/-- The norm, relative to `ℤ`, of `ζ - 1` in a `p`-th cyclotomic extension of `ℚ` is a prime if
`p ≠ 2`. -/
/-
**IsPrimitiveRoot.prime_norm_toInteger_sub_one_of_prime_ne_two'** 是 Mathlib 中的一个
引理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：prime_norm_toInteger_sub_one_of_prime_ne_two' [hcycl : IsCyclotomicExtensi
on {p} Rat K] (hζ : IsPrimitiveRoot ζ p) (hodd : p != 2) : Prime (Algebra.norm I
nt (hζ.toInteger - 1))
参数：hζ : IsPrimitiveRoot ζ p；hodd : p != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `IsPrimitiveRoot.prime_norm_toInteger_sub_one_of_prime_ne_two`：prime_norm
_toInteger_sub_one_of_prime_ne_two [hcycl : IsCyclotomicExtension {p ^ (k + 1)} 
Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hod…

--- 原说明 ---
The norm, relative to `ℤ`, of `ζ - 1` in a `p`-th cyclotomic extension of `ℚ` is
 a prime if
`p ≠ 2`.
-/
lemma prime_norm_toInteger_sub_one_of_prime_ne_two' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) (hodd : p ≠ 2) :
    Prime (Algebra.norm ℤ (hζ.toInteger - 1)) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.prime_norm_toInteger_sub_one_of_prime_ne_two hodd

/-- In a `p ^ (k + 1)`-th cyclotomic extension of `ℚ `, we have that `ζ` is not congruent to an
  integer modulo `p` if `p ^ (k  + 1) ≠ 2`. -/
/-
**IsPrimitiveRoot.not_exists_int_prime_dvd_sub_of_prime_pow_ne_two** 是 Mathlib 中
的一个定理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：not_exists_int_prime_dvd_sub_of_prime_pow_ne_two [hcycl : IsCyclotomicExte
nsion {p ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (htwo : p ^ (k
 + 1) != 2) : ¬(exists n : Int, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K))
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；htwo : p ^ (k + 1) != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.integralPowerBasisOfPrimePow_dim`：integralPowerBasisOfPr
imePow_dim [hcycl : IsCyclotomicExtension {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ
 (p ^ k)) : hζ.integralPowerBasisOfPri…
· 使用定理 `Nat.totient_prime_pow`：totient_prime_pow {p : Nat} (hp : p.Prime) {n : N
at} (hn : 0 < n) : φ (p ^ n) = p ^ (n - 1) * (p - 1)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.one_lt_iff_ne_zero_and_ne_one`：∀ {n : ℕ}, 1 < n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
In a `p ^ (k + 1)`-th cyclotomic extension of `ℚ `, we have that `ζ` is not cong
ruent to an
  integer modulo `p` if `p ^ (k  + 1) ≠ 2`.
-/
theorem not_exists_int_prime_dvd_sub_of_prime_pow_ne_two
    [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (htwo : p ^ (k + 1) ≠ 2) :
    ¬(∃ n : ℤ, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K)) := by
  intro ⟨n, x, h⟩
  -- Let `pB` be the power basis of `𝓞 K` given by powers of `ζ`.
  let pB := hζ.integralPowerBasisOfPrimePow
  have hdim : pB.dim = p ^ k * (↑p - 1) := by
    simp [integralPowerBasisOfPrimePow_dim, pB, Nat.totient_prime_pow hp.1 (Nat.zero_lt_succ k)]
  replace hdim : 1 < pB.dim := by
    rw [Nat.one_lt_iff_ne_zero_and_ne_one, hdim]
    refine ⟨by simp only [ne_eq, mul_eq_zero, NeZero.ne _, Nat.sub_eq_zero_iff_le, false_or,
      not_le, Nat.Prime.one_lt hp.out], ne_of_gt ?_⟩
    by_cases hk : k = 0
    · simp only [hk, zero_add, pow_one, pow_zero, one_mul, Nat.lt_sub_iff_add_lt,
        Nat.reduceAdd] at htwo ⊢
      exact htwo.symm.lt_of_le hp.1.two_le
    · exact one_lt_mul_of_lt_of_le (one_lt_pow₀ hp.1.one_lt hk)
        (have := Nat.Prime.two_le hp.out; by lia)
  rw [sub_eq_iff_eq_add] at h
  -- We are assuming that `ζ = n + p * x` for some integer `n` and `x : 𝓞 K`. Looking at the
  -- coordinates in the base `pB`, we obtain that `1` is a multiple of `p`, contradiction.
  replace h := pB.basis.ext_elem_iff.1 h ⟨1, hdim⟩
  have := pB.basis_eq_pow ⟨1, hdim⟩
  rw [hζ.integralPowerBasisOfPrimePow_gen] at this
  simp only [PowerBasis.coe_basis, pow_one] at this
  rw [← this, show pB.gen = pB.gen ^ (⟨1, hdim⟩ : Fin pB.dim).1 by simp, ← pB.basis_eq_pow,
    pB.basis.repr_self_apply] at h
  simp only [↓reduceIte, map_add, Finsupp.coe_add, Pi.add_apply] at h
  rw [show (p : 𝓞 K) * x = (p : ℤ) • x by simp, ← pB.basis.coord_apply,
    map_smul, ← zsmul_one, ← pB.basis.coord_apply, map_smul,
    show 1 = pB.gen ^ (⟨0, by lia⟩ : Fin pB.dim).1 by simp, ← pB.basis_eq_pow,
    pB.basis.coord_apply, pB.basis.coord_apply, pB.basis.repr_self_apply] at h
  simp only [smul_eq_mul, Fin.mk.injEq, zero_ne_one, ↓reduceIte, mul_zero, add_zero] at h
  exact (Int.prime_iff_natAbs_prime.2 (by simp [hp.1])).not_dvd_one ⟨_, h⟩

/-- In a `p ^ (k + 1)`-th cyclotomic extension of `ℚ `, we have that `ζ` is not congruent to an
  integer modulo `p` if `p ≠ 2`. -/
/-
**IsPrimitiveRoot.not_exists_int_prime_dvd_sub_of_prime_ne_two** 是 Mathlib 中的一个定
理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：not_exists_int_prime_dvd_sub_of_prime_ne_two [hcycl : IsCyclotomicExtensio
n {p ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) : 
¬(exists n : Int, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K))
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；hodd : p != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.not_exists_int_prime_dvd_sub_of_prime_pow_ne_two`：not_ex
ists_int_prime_dvd_sub_of_prime_pow_ne_two [hcycl : IsCyclotomicExtension {p ^ (
k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.pow_eq_iff`：∀ {p a k : ℕ}, Nat.Prime p → (a ^ k = p ↔ a = p ∧ 
k = 1)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False

--- 原说明 ---
In a `p ^ (k + 1)`-th cyclotomic extension of `ℚ `, we have that `ζ` is not cong
ruent to an
  integer modulo `p` if `p ≠ 2`.
-/
theorem not_exists_int_prime_dvd_sub_of_prime_ne_two
    [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) :
    ¬(∃ n : ℤ, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K)) := by
  refine not_exists_int_prime_dvd_sub_of_prime_pow_ne_two hζ (fun h ↦ ?_)
  simp_all only [(@Nat.Prime.pow_eq_iff 2 p (k + 1) Nat.prime_two).mp (by assumption_mod_cast),
    pow_one, ne_eq]

/-- In a `p`-th cyclotomic extension of `ℚ `, we have that `ζ` is not congruent to an
  integer modulo `p` if `p ≠ 2`. -/
/-
**IsPrimitiveRoot.not_exists_int_prime_dvd_sub_of_prime_ne_two'** 是 Mathlib 中的一个
定理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：not_exists_int_prime_dvd_sub_of_prime_ne_two' [hcycl : IsCyclotomicExtensi
on {p} Rat K] (hζ : IsPrimitiveRoot ζ p) (hodd : p != 2) : ¬(exists n : Int, (p 
: 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K))
参数：hζ : IsPrimitiveRoot ζ p；hodd : p != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `IsPrimitiveRoot.not_exists_int_prime_dvd_sub_of_prime_ne_two`：not_exists
_int_prime_dvd_sub_of_prime_ne_two [hcycl : IsCyclotomicExtension {p ^ (k + 1)} 
Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hod…

--- 原说明 ---
In a `p`-th cyclotomic extension of `ℚ `, we have that `ζ` is not congruent to a
n
  integer modulo `p` if `p ≠ 2`.
-/
theorem not_exists_int_prime_dvd_sub_of_prime_ne_two'
    [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) (hodd : p ≠ 2) :
    ¬(∃ n : ℤ, (p : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K)) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact not_exists_int_prime_dvd_sub_of_prime_ne_two hζ hodd
/-
**IsPrimitiveRoot.finite_quotient_span_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `IsPrim
itiveRoot`。
形式化陈述：finite_quotient_span_sub_one [hcycl : IsCyclotomicExtension {p ^ (k + 1)} 
Rat K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : Finite (𝓞 K ⧸ Ideal.span {hζ.toI
nteger - 1})
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Ideal.finiteQuotientOfFreeOfNeBot`：finiteQuotientOfFreeOfNeBot [Module.F
ree Int S] [Module.Finite Int S] (I : Ideal S) (hI : I != ⊥) : Finite (S ⧸ I)
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsPrimitiveRoot.ne_one`：ne_one (h : IsPrimitiveRoot ζ k) (hk : 1 < k) : 
ζ != 1
· 使用定理 `one_lt_pow₀`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preo
rder M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   1 < a → ∀ {n : ℕ}, n ≠ 
0…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.zero_ne_add_one`：∀ (n : ℕ), 0 ≠ n + 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.RingOfIntegers.ext_iff`：∀ {K : Type u_1} [inst : Field K] {x
 y : NumberField.RingOfIntegers K}, x = y ↔ ↑x = ↑y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem finite_quotient_span_sub_one [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  refine Ideal.finiteQuotientOfFreeOfNeBot _ (fun h ↦ ?_)
  simp only [Ideal.span_singleton_eq_bot, sub_eq_zero] at h
  exact hζ.ne_one (one_lt_pow₀ hp.1.one_lt (Nat.zero_ne_add_one k).symm)
    (RingOfIntegers.ext_iff.1 h)
/-
**IsPrimitiveRoot.finite_quotient_span_sub_one'** 是 Mathlib 中的一个定理，位于命名空间 `IsPri
mitiveRoot`。
形式化陈述：finite_quotient_span_sub_one' [hcycl : IsCyclotomicExtension {p} Rat K] (h
ζ : IsPrimitiveRoot ζ p) : Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1})
参数：hζ : IsPrimitiveRoot ζ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `IsPrimitiveRoot.finite_quotient_span_sub_one`：finite_quotient_span_sub_o
ne [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (
p ^ (k + 1))) : Finite (𝓞 K ⧸ Idea…
-/
theorem finite_quotient_span_sub_one' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) :
    Finite (𝓞 K ⧸ Ideal.span {hζ.toInteger - 1}) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact hζ.finite_quotient_span_sub_one

/-- In a `p ^ (k + 1)`-th cyclotomic extension of `ℚ`, we have that
  `ζ - 1` divides `p` in `𝓞 K`. -/
/-
**IsPrimitiveRoot.toInteger_sub_one_dvd_prime** 是 Mathlib 中的一个引理，位于命名空间 `IsPrimi
tiveRoot`。
形式化陈述：toInteger_sub_one_dvd_prime [hcycl : IsCyclotomicExtension {p ^ (k + 1)} R
at K] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : ((hζ.toInteger - 1)) ∣ p
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.pow_eq_iff`：∀ {p a k : ℕ}, Nat.Prime p → (a ^ k = p ↔ a = p ∧ 
k = 1)
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `IsPrimitiveRoot.eq_neg_one_of_two_right`：eq_neg_one_of_two_right [NoZero
Divisors R] {ζ : R} (h : IsPrimitiveRoot ζ 2) : ζ = -1
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `NumberField.RingOfIntegers.ext`：∀ {K : Type u_1} [inst : Field K] {x y :
 NumberField.RingOfIntegers K}, ↑x = ↑y → x = y
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 63 条，此处仅展示前 30 条）

--- 原说明 ---
In a `p ^ (k + 1)`-th cyclotomic extension of `ℚ`, we have that
  `ζ - 1` divides `p` in `𝓞 K`.
-/
lemma toInteger_sub_one_dvd_prime [hcycl : IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : ((hζ.toInteger - 1)) ∣ p := by
  by_cases htwo : p ^ (k + 1) = 2
  · have ⟨hp2, hk⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).1 htwo
    simp only [add_eq_right] at hk
    have hζ' : ζ = -1 := by
      refine IsPrimitiveRoot.eq_neg_one_of_two_right ?_
      rwa [hk, zero_add, pow_one, hp2] at hζ
    replace hζ' : hζ.toInteger = -1 := by
      ext
      exact hζ'
    rw [hζ', hp2]
    exact ⟨-1, by ring⟩
  suffices (hζ.toInteger - 1) ∣ (p : ℤ) by simpa
  have := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  have H := hζ.norm_toInteger_pow_sub_one_of_prime_pow_ne_two zero_le htwo
  rw [pow_zero, pow_one] at H
  rw [← Ideal.norm_dvd_iff, H]
  · simp
  · exact prime_norm_toInteger_sub_one_of_prime_pow_ne_two hζ htwo

/-- In a `p`-th cyclotomic extension of `ℚ`, we have that `ζ - 1` divides `p` in `𝓞 K`. -/
/-
**IsPrimitiveRoot.toInteger_sub_one_dvd_prime'** 是 Mathlib 中的一个引理，位于命名空间 `IsPrim
itiveRoot`。
形式化陈述：toInteger_sub_one_dvd_prime' [hcycl : IsCyclotomicExtension {p} Rat K] (hζ
 : IsPrimitiveRoot ζ p) : hζ.toInteger - 1 ∣ p
参数：hζ : IsPrimitiveRoot ζ p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `IsPrimitiveRoot.toInteger_sub_one_dvd_prime`：toInteger_sub_one_dvd_prime
 [hcycl : IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ : IsPrimitiveRoot ζ (p 
^ (k + 1))) : ((hζ.toInteger - 1)…

--- 原说明 ---
In a `p`-th cyclotomic extension of `ℚ`, we have that `ζ - 1` divides `p` in `𝓞 
K`.
-/
lemma toInteger_sub_one_dvd_prime' [hcycl : IsCyclotomicExtension {p} ℚ K]
    (hζ : IsPrimitiveRoot ζ p) : hζ.toInteger - 1 ∣ p := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by simpa using hcycl
  replace hζ : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  exact toInteger_sub_one_dvd_prime hζ

/-- We have that `hζ.toInteger - 1` does not divide `2`. -/
/-
**IsPrimitiveRoot.toInteger_sub_one_not_dvd_two** 是 Mathlib 中的一个引理，位于命名空间 `IsPri
mitiveRoot`。
形式化陈述：toInteger_sub_one_not_dvd_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K] 
(hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) : ¬ hζ.toInteger - 1 ∣ 2
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；hodd : p != 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {M : Type*} [CommMonoidWi
thZero M] [IsCancelMulZero M] [Subsingleton Mˣ] {p q : M} (pp : Prime p) (qp : P
rime q) : p …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.prime_iff`：prime_iff {p : Nat} : p.Prime ↔ _root_.Prime p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.prime_two`：prime_two : Prime 2
· 使用定理 `Int.ofNat_dvd`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用引理 `IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two`：norm_toInteger_s
ub_one_of_prime_ne_two [IsCyclotomicExtension {p ^ (k + 1)} Rat K] (hζ : IsPrimi
tiveRoot ζ (p ^ (k + 1))) (hodd : p != 2) : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.norm_dvd_iff`：norm_dvd_iff {x : S} (hx : Prime (Algebra.norm Int x
)) {y : Int} : Algebra.norm Int x ∣ y ↔ x ∣ y
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)

--- 原说明 ---
We have that `hζ.toInteger - 1` does not divide `2`.
-/
lemma toInteger_sub_one_not_dvd_two [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hodd : p ≠ 2) : ¬ hζ.toInteger - 1 ∣ 2 := fun h ↦ by
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  replace h : hζ.toInteger - 1 ∣ (2 : ℤ) := by simp [h]
  rw [← Ideal.norm_dvd_iff, hζ.norm_toInteger_sub_one_of_prime_ne_two hodd] at h
  · refine hodd <| (prime_dvd_prime_iff_eq ?_ ?_).1 ?_
    · exact Nat.prime_iff.1 hp.1
    · exact Nat.prime_iff.1 Nat.prime_two
    · exact Int.ofNat_dvd.mp h
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two hodd]
    exact Nat.prime_iff_prime_int.1 hp.1

set_option backward.isDefEq.respectTransparency.types false in
open IntermediateField in
/--
Let `ζ` be a primitive root of unity of order `n` with `2 ≤ n`. Any prime number that divides the
norm, relative to `ℤ`, of `ζ - 1` divides also `n`.
-/
/-
**IsPrimitiveRoot.prime_dvd_of_dvd_norm_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `IsPri
mitiveRoot`。
形式化陈述：prime_dvd_of_dvd_norm_sub_one {n : Nat} (hn : 2 <= n) {K : Type*} [Field K
] [NumberField K] {ζ : K} {p : Nat} [hF : Fact (Nat.Prime p)] (hζ : IsPrimitiveR
oot ζ n) (hp : haveI : NeZero n
参数：hn : 2 <= n；Nat.Prime p；hζ : IsPrimitiveRoot ζ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt`：of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero
 b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`：∀ (K : T
ype w) {L : Type z} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [
Algebra.IsIntegral K L] {n : ℕ}   [NeZero n] {ζ : L}…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsPrimitiveRoot.coe_submonoidClass_iff`：coe_submonoidClass_iff {M B : Ty
pe*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {N : B} {ζ : N} : IsPrimi
tiveRoot (ζ : M) k ↔ IsPrimi…
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.norm_eq_iff`：Algebra.norm_eq_iff [Module.Free R S] [Module.Finit
e R S] {a : S} {b : R} (hM : M <= nonZeroDivisors R) : Algebra.norm R a = b ↔ (A
lgebra.no…
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
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
· 使用定理 `NumberField.RingOfIntegers.map_mk`：∀ {K : Type u_1} [inst : Field K] (x 
: K) (hx : x ∈ integralClosure ℤ K),   (algebraMap (NumberField.RingOfIntegers K
) K) ⟨x, hx⟩ = x
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
（共 94 条，此处仅展示前 30 条）

--- 原说明 ---
Let `ζ` be a primitive root of unity of order `n` with `2 ≤ n`. Any prime number
 that divides the
norm, relative to `ℤ`, of `ζ - 1` divides also `n`.
-/
theorem prime_dvd_of_dvd_norm_sub_one {n : ℕ} (hn : 2 ≤ n) {K : Type*}
    [Field K] [NumberField K] {ζ : K} {p : ℕ} [hF : Fact (Nat.Prime p)] (hζ : IsPrimitiveRoot ζ n)
    (hp : haveI : NeZero n := NeZero.of_gt hn; (p : ℤ) ∣ norm ℤ (hζ.toInteger - 1)) :
    p ∣ n := by
  have : NeZero n := NeZero.of_gt hn
  obtain ⟨μ, hC, hμ, h⟩ :
      ∃ μ : ℚ⟮ζ⟯, ∃ (_ : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯), ∃ (hμ : IsPrimitiveRoot μ n),
      norm ℤ (hζ.toInteger - 1) = norm ℤ (hμ.toInteger - 1) ^ Module.finrank ℚ⟮ζ⟯ K := by
    refine ⟨IntermediateField.AdjoinSimple.gen ℚ ζ,
      intermediateField_adjoin_isCyclotomicExtension ℚ hζ, coe_submonoidClass_iff.mp hζ, ?_⟩
    have : NumberField ℚ⟮ζ⟯ := of_intermediateField _
    rw [norm_eq_iff ℤ (Sₘ := K) (Rₘ := ℚ) le_rfl, map_sub, map_one, RingOfIntegers.map_mk,
      show ζ - 1 = algebraMap ℚ⟮ζ⟯ K (IntermediateField.AdjoinSimple.gen ℚ ζ - 1) by rfl,
      ← norm_norm (S := ℚ⟮ζ⟯), Algebra.norm_algebraMap, map_pow, map_pow, ← norm_localization ℤ
      (nonZeroDivisors ℤ) (Sₘ := ℚ⟮ζ⟯), map_sub (algebraMap _ _), RingOfIntegers.map_mk, map_one]
  rw [h] at hp
  rsuffices ⟨q, hq, t, s, ht₁, ht₂, hs⟩ :
      ∃ q, q.Prime ∧ ∃ t s, t ≠ 0 ∧ n = q ^ t ∧ (p : ℤ) ∣ (q : ℤ) ^ s := by
    obtain hn | hn := lt_or_eq_of_le hn
    · by_cases! h : ∃ q, q.Prime ∧ ∃ t, q ^ t = n
      · obtain ⟨q, hq, t, hn'⟩ := h
        have : Fact (Nat.Prime q) := ⟨hq⟩
        cases t with
        | zero => simp [← hn'] at hn
        | succ r =>
          rw [← hn'] at hC hμ
          refine ⟨q, hq, r + 1, Module.finrank (ℚ⟮ζ⟯) K, r.add_one_ne_zero, hn'.symm, ?_⟩
          by_cases hq' : q = 2
          · cases r with
            | zero =>
                rw [← hn', hq', zero_add, pow_one] at hn
                exact hn.false.elim
            | succ k =>
                rw [hq'] at hC hμ ⊢
                rwa [hμ.norm_toInteger_sub_one_of_eq_two_pow] at hp
          · rwa [hμ.norm_toInteger_sub_one_of_prime_ne_two hq'] at hp
      · rw [IsPrimitiveRoot.norm_toInteger_sub_one_eq_one hμ hn, one_pow,
          Int.natCast_dvd_ofNat, Nat.dvd_one] at hp
        · exact (Nat.Prime.ne_one hF.out hp).elim
        · exact fun {p} a k ↦ h p a k
    · rw [← hn] at hμ hC ⊢
      refine ⟨2, Nat.prime_two, 1, Module.finrank ℚ⟮ζ⟯ K, one_ne_zero, by rw [pow_one], ?_⟩
      rwa [hμ.norm_toInteger_sub_one_of_eq_two, neg_eq_neg_one_mul, mul_pow, IsUnit.dvd_mul_left
        ((isUnit_pow_iff Module.finrank_pos.ne').mpr isUnit_neg_one)] at hp
  have : p = q := by
    rw [← Int.natCast_pow, Int.natCast_dvd_natCast] at hs
    exact (Nat.prime_dvd_prime_iff_eq hF.out hq).mp (hF.out.dvd_of_dvd_pow hs)
  rw [ht₂, this]
  exact dvd_pow_self _ ht₁

end IsPrimitiveRoot

section discr

namespace IsCyclotomicExtension.Rat

open nonZeroDivisors IsPrimitiveRoot

variable (K p k)
variable [CharZero K]

set_option backward.defeqAttrib.useBackward true in
/-- We compute the absolute discriminant of a `p ^ k`-th cyclotomic field.
  Beware that in the cases `p ^ k = 1` and `p ^ k = 2` the formula uses `1 / 2 = 0` and `0 - 1 = 0`.
  See also the results below. -/
/-
**IsCyclotomicExtension.Rat.discr_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsCycloto
micExtension.Rat`。
形式化陈述：discr_prime_pow [IsCyclotomicExtension {p ^ k} Rat K] : haveI : NumberFiel
d K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `RingHom.injective_int`：RingHom.injective_int {α : Type*} [NonAssocRing α
] (f : Int ->+* α) [CharZero α] : Function.Injective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.discr_eq_discr`：discr_eq_discr {ι : Type*} [Fintype ι] [Deci
dableEq ι] (b : Basis ι Int (𝓞 K)) : Algebra.discr Int b = discr K
· 使用定理 `NumberField.RingOfIntegers.instIsLocalizationAlgebraMapSubmonoidIntNonZe
roDivisors`：∀ (K : Type u_1) [inst : Field K] [NumberField K],   IsLocalization 
(Algebra.algebraMapSubmonoid (NumberField.RingOfIntegers K) (nonZeroDivi…
· 使用定理 `Algebra.discr_localizationLocalization`：Algebra.discr_localizationLocali
zation (b : Basis ι R S) : Algebra.discr Rₘ (b.localizationLocalization Rₘ M Sₘ)
 = algebraMap R Rₘ (Algebra.…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `PowerBasis.finrank`：finrank [StrongRankCondition R] (pb : PowerBasis R S
) : Module.finrank R S = pb.dim
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.RingOfIntegers.rank`：∀ (K : Type u_1) [inst : Field K] [inst
_1 : NumberField K],   Module.finrank ℤ (NumberField.RingOfIntegers K) = Module.
finrank ℚ K
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Algebra.discr_reindex`：discr_reindex (b : Basis ι A B) (f : ι ≃ ι') : di
scr A (b ∘ ⇑f.symm) = discr A b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.localizationLocalization_apply`：localizationLocalization_ap
ply {ι : Type*} (b : Basis ι R A) (i) : b.localizationLocalization Rₛ S Aₛ i = a
lgebraMap A Aₛ (b i)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerBasis.coe_basis`：coe_basis (pb : PowerBasis R S) : ⇑pb.basis = fun 
i : Fin pb.dim => pb.gen ^ (i : Nat)
· 使用定理 `IsPrimitiveRoot.integralPowerBasisOfPrimePow_gen`：integralPowerBasisOfPr
imePow_gen [hcycl : IsCyclotomicExtension {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ
 (p ^ k)) : hζ.integralPowerBasisOfPri…
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
We compute the absolute discriminant of a `p ^ k`-th cyclotomic field.
  Beware that in the cases `p ^ k = 1` and `p ^ k = 2` the formula uses `1 / 2 =
 0` and `0 - 1 = 0`.
  See also the results below.
-/
theorem discr_prime_pow [IsCyclotomicExtension {p ^ k} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p ^ k} ℚ K
    NumberField.discr K =
    (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  have hζ := IsCyclotomicExtension.zeta_spec (p ^ k) ℚ K
  have : NumberField K := IsCyclotomicExtension.numberField {p ^ k} ℚ K
  let pB₁ := integralPowerBasisOfPrimePow hζ
  apply (algebraMap ℤ ℚ).injective_int
  rw [← NumberField.discr_eq_discr _ pB₁.basis, ← Algebra.discr_localizationLocalization ℤ ℤ⁰ K]
  convert!
    IsCyclotomicExtension.discr_prime_pow hζ (cyclotomic.irreducible_rat (NeZero.pos _)) using 1
  · have : pB₁.dim = (IsPrimitiveRoot.powerBasis ℚ hζ).dim := by
      rw [← PowerBasis.finrank, ← PowerBasis.finrank]
      exact RingOfIntegers.rank K
    rw [← Algebra.discr_reindex _ _ (finCongr this)]
    congr 1
    ext i
    simp_rw [Function.comp_apply, Module.Basis.localizationLocalization_apply, powerBasis_dim,
      PowerBasis.coe_basis, pB₁, integralPowerBasisOfPrimePow_gen]
    convert! ← ((IsPrimitiveRoot.powerBasis ℚ hζ).basis_eq_pow i).symm using 1
  · simp_rw [algebraMap_int_eq, map_mul, map_pow, map_neg, map_one, map_natCast]

open Nat in
/-- We compute the absolute discriminant of a `p ^ (k + 1)`-th cyclotomic field.
  Beware that in the case `p ^ k = 2` the formula uses `1 / 2 = 0`. See also the results below. -/
/-
**IsCyclotomicExtension.Rat.discr_prime_pow_succ** 是 Mathlib 中的一个定理，位于命名空间 `IsCy
clotomicExtension.Rat`。
形式化陈述：discr_prime_pow_succ [IsCyclotomicExtension {p ^ (k + 1)} Rat K] : haveI :
 NumberField K
参数：k + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.totient_prime_pow`：totient_prime_pow {p : Nat} (hp : p.Prime) {n : N
at} (hn : 0 < n) : φ (p ^ n) = p ^ (n - 1) * (p - 1)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsCyclotomicExtension.Rat.discr_prime_pow`：discr_prime_pow [IsCyclotomic
Extension {p ^ k} Rat K] : haveI : NumberField K

--- 原说明 ---
We compute the absolute discriminant of a `p ^ (k + 1)`-th cyclotomic field.
  Beware that in the case `p ^ k = 2` the formula uses `1 / 2 = 0`. See also the
 results below.
-/
theorem discr_prime_pow_succ [IsCyclotomicExtension {p ^ (k + 1)} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
    NumberField.discr K =
    (-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  simpa [totient_prime_pow hp.out (succ_pos k)] using discr_prime_pow p (k + 1) K

/-- We compute the absolute discriminant of a `p`-th cyclotomic field where `p` is prime. -/
/-
**IsCyclotomicExtension.Rat.discr_prime** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicE
xtension.Rat`。
形式化陈述：discr_prime [IsCyclotomicExtension {p} Rat K] : haveI : NumberField K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsCyclotomicExtension.Rat.discr_prime_pow_succ`：discr_prime_pow_succ [Is
CyclotomicExtension {p ^ (k + 1)} Rat K] : haveI : NumberField K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.sub_sub`：∀ (n m k : ℕ), n - m - k = n - (m + k)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
We compute the absolute discriminant of a `p`-th cyclotomic field where `p` is p
rime.
-/
theorem discr_prime [IsCyclotomicExtension {p} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {p} ℚ K
    NumberField.discr K = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    rw [zero_add, pow_one]
    infer_instance
  rw [discr_prime_pow_succ p 0 K]
  simp [Nat.sub_sub]

variable (n) [hn : NeZero n]

set_option backward.isDefEq.respectTransparency false in
open Algebra IntermediateField Nat in
/--
Computes the absolute discriminant of the `n`-th cyclotomic field.
-/
/-
**IsCyclotomicExtension.Rat.discr** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicExtensi
on.Rat`。
形式化陈述：discr [hK : IsCyclotomicExtension {n} Rat K] : haveI : NumberField K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.sign_mul_natAbs`：∀ (a : ℤ), a.sign * ↑a.natAbs = a
· 使用定理 `NumberField.sign_discr`：sign_discr : (discr K).sign = (-1) ^ nrComplexPl
aces K
· 使用定理 `IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two`：nrComplexP
laces_eq_totient_div_two [h : IsCyclotomicExtension {n} Rat K] : haveI
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neZero_zero_iff_false`：∀ {α : Type u_1} [inst : Zero α], NeZero 0 ↔ Fals
e
· 使用定理 `IsCyclotomicExtension.Rat.discr_prime_pow`：discr_prime_pow [IsCyclotomic
Extension {p ^ k} Rat K] : haveI : NumberField K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Int.natAbs_of_isUnit`：∀ {u : ℤ}, IsUnit u → u.natAbs = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Nat.primeFactors_one`：Nat.primeFactors 1 = ∅
· 使用定理 `Nat.div_self`：∀ {n : ℕ}, 0 < n → n / n = 1
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
Computes the absolute discriminant of the `n`-th cyclotomic field.
-/
theorem discr [hK : IsCyclotomicExtension {n} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
    discr K = (-1) ^ (φ n / 2) * (n ^ φ n / ∏ p ∈ n.primeFactors, p ^ (φ n / (p - 1))) := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  rw [← Int.sign_mul_natAbs (NumberField.discr K), sign_discr, nrComplexPlaces_eq_totient_div_two n]
  congr
  induction n using Nat.recOnPrimeCoprime generalizing K hn with
  | zero => exact (neZero_zero_iff_false.mp hn).elim
  | prime_pow p k hp =>
    have : Fact (Nat.Prime p) := ⟨hp⟩
    rw [discr_prime_pow p k K]
    cases k with
    | zero => simp
    | succ k =>
      simpa only [Int.reduceNeg, add_tsub_cancel_right, Int.natAbs_mul, Int.natAbs_pow,
        IsUnit.neg_iff, isUnit_one, Int.natAbs_of_isUnit, one_pow, Int.natAbs_natCast, one_mul]
        using! (Nat.prime_pow_pow_totient_ediv_prod hp k.zero_lt_succ).symm
  | coprime n₁ n₂ hn₁ hn₂ h hK₁ hK₂ =>
    have : NeZero n₁ := NeZero.of_gt hn₁
    have : NeZero n₂ := NeZero.of_gt hn₂
    let ζ := zeta (n₁ * n₂) ℚ K
    have hζ := zeta_spec (n₁ * n₂) ℚ K
    have hζ₁ := hζ.pow (NeZero.pos _) (a := n₂) (b := n₁) (by rw [mul_comm])
    have := hζ₁.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hζ₁' : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₂)) n₁ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₁
    replace hK₁ := @hK₁ ℚ⟮ζ ^ n₂⟯ _ _ _ _ (of_intermediateField _)
    have hζ₂ := hζ.pow (NeZero.pos _) (a := n₁) (b := n₂) rfl
    have := hζ₂.intermediateField_adjoin_isCyclotomicExtension ℚ
    have hζ₂' : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₁)) n₂ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₂
    replace hK₂ := @hK₂ ℚ⟮ζ ^ n₁⟯ _ _ _ _ (of_intermediateField _)
    have : IsGalois ℚ ℚ⟮ζ ^ n₂⟯ := isGalois {n₁} ℚ _
    have h_top : ℚ⟮ζ ^ n₂⟯ ⊔ ℚ⟮ζ ^ n₁⟯ = ⊤ := by
      have : IsCyclotomicExtension {n₁ * n₂} ℚ (⊤ : IntermediateField ℚ K) :=
          hK.equiv _ _ _ topEquiv.symm
      have : IsCyclotomicExtension {n₁ * n₂} ℚ ↥(ℚ⟮ζ ^ n₂⟯ ⊔ ℚ⟮ζ ^ n₁⟯) := by
        rw [← Nat.Coprime.lcm_eq_mul h]
        exact isCyclotomicExtension_lcm_sup ℚ K n₁ n₂ ℚ⟮ζ ^ n₂⟯ ℚ⟮ζ ^ n₁⟯
      exact isCyclotomicExtension_eq {n₁ * n₂} ℚ K _ _
    have h_cpr : IsCoprime (discr ℚ⟮ζ ^ n₂⟯) (discr ℚ⟮ζ ^ n₁⟯) := by
      rw [Int.isCoprime_iff_nat_coprime, hK₁, hK₂]
      refine Coprime.coprime_div_left ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
      refine Coprime.coprime_div_right ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
      exact Coprime.pow_left _ (Coprime.pow_right _ h)
    have h_dsj : ℚ⟮ζ ^ n₂⟯.LinearDisjoint ℚ⟮ζ ^ n₁⟯ :=
      linearDisjoint_of_isGalois_isCoprime_discr _ _ _ h_cpr
    have h_div₁ := prod_primeFactors_pow_totient_ediv_dvd n₁.pos_of_neZero
    have h_div₂ := prod_primeFactors_pow_totient_ediv_dvd n₂.pos_of_neZero
    rw [natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow K ℚ⟮ζ ^ n₂⟯ ℚ⟮ζ ^ n₁⟯ h_dsj h_top
      (isCoprime_differentIdeal_of_isCoprime_discr _ h_cpr), hK₁, hK₂,
      finrank n₁ ℚ⟮ζ ^ n₂⟯, finrank n₂ ℚ⟮ζ ^ n₁⟯, Nat.div_pow h_div₁, Nat.div_pow h_div₂,
      ← Nat.mul_div_mul_comm (pow_dvd_pow_of_dvd h_div₁ n₂.totient)
      (pow_dvd_pow_of_dvd h_div₂ n₁.totient), primeFactors_mul (NeZero.ne _) (NeZero.ne _),
      Finset.prod_union h.disjoint_primeFactors, ← Finset.prod_pow, ← Finset.prod_pow]
    have {n p : ℕ} (hp : p ∈ n.primeFactors) : p - 1 ∣ n.totient :=
      p.totient_prime (prime_of_mem_primeFactors hp) ▸ totient_dvd_of_dvd (b := n)
        <| dvd_of_mem_primeFactors hp
    simp_rw +contextual [← pow_mul, Nat.div_mul_right_comm (this _), Nat.totient_mul h]
    rw [mul_pow, mul_comm n₂.totient]
/-
**IsCyclotomicExtension.Rat.natAbs_discr** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomic
Extension.Rat`。
形式化陈述：natAbs_discr [hK : IsCyclotomicExtension {n} Rat K] : haveI : NumberField 
K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsCyclotomicExtension.Rat.discr`：discr [hK : IsCyclotomicExtension {n} R
at K] : haveI : NumberField K
· 使用定理 `Int.natAbs_mul`：∀ (a b : ℤ), (a * b).natAbs = a.natAbs * b.natAbs
· 使用定理 `Int.natAbs_pow`：∀ (n : ℤ) (k : ℕ), (n ^ k).natAbs = n.natAbs ^ k
· 使用定理 `Int.natAbs_neg`：∀ (a : ℤ), (-a).natAbs = a.natAbs
· 使用定理 `Int.natAbs_one`：Int.natAbs 1 = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Int.natAbs_ediv_of_dvd`：∀ {a b : ℤ}, b ∣ a → (a / b).natAbs = a.natAbs /
 b.natAbs
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Nat.prod_primeFactors_pow_totient_ediv_dvd`：prod_primeFactors_pow_totien
t_ediv_dvd {n : Nat} (hn : 0 < n) : ∏ p in n.primeFactors, p ^ (φ n / (p - 1)) ∣
 n ^ φ n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Int.natAbs_natCast`：∀ (n : ℕ), (↑n).natAbs = n
-/
theorem natAbs_discr [hK : IsCyclotomicExtension {n} ℚ K] :
    haveI : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
    (NumberField.discr K).natAbs = n ^ φ n / ∏ p ∈ n.primeFactors, p ^ (φ n / (p - 1)) := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  rw [discr n K, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one, one_pow, one_mul,
    Int.natAbs_ediv_of_dvd, Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_natCast]
  rw [← Nat.cast_pow, Int.natCast_dvd_natCast]
  exact Nat.prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _)

open IntermediateField Algebra Nat in
/-
**IsCyclotomicExtension.Rat.adjoin_singleton_eq_top_aux** 是 Mathlib 中的一个定理，位于命名空
间 `IsCyclotomicExtension.Rat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem adjoin_singleton_eq_top_aux [NumberField K] (F₁ F₂ : IntermediateField ℚ K)
    {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂] [IsCyclotomicExtension {n₁} ℚ F₁]
    [IsCyclotomicExtension {n₂} ℚ F₂] {ζ₁ : F₁} (hζ₁ : IsPrimitiveRoot ζ₁ n₁)
    (h₁ : ℤ[hζ₁.toInteger] = ⊤) {ζ₂ : F₂} (hζ₂ : IsPrimitiveRoot ζ₂ n₂)
    (h₂ : ℤ[hζ₂.toInteger] = ⊤) (h : n₁.Coprime n₂) (htop : F₁ ⊔ F₂ = ⊤)
    {ζ : K} (hζ : IsPrimitiveRoot ζ (n₁ * n₂)) :
    ℤ[hζ.toInteger] = ⊤ := by
  have h_cpr : IsCoprime (NumberField.discr F₁) (NumberField.discr F₂) := by
    rw [Int.isCoprime_iff_nat_coprime, natAbs_discr n₁ F₁, natAbs_discr n₂ F₂]
    refine Coprime.coprime_div_left ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
    refine Coprime.coprime_div_right ?_ (prod_primeFactors_pow_totient_ediv_dvd (NeZero.pos _))
    exact Coprime.pow_left _ (Coprime.pow_right _ h)
  have h_disj : F₁.LinearDisjoint F₂ := by
    have : IsGalois ℚ F₁ := IsCyclotomicExtension.isGalois {n₁} ℚ F₁
    apply linearDisjoint_of_isGalois_isCoprime_discr
    exact h_cpr
  replace hζ₁ : IsPrimitiveRoot hζ₁.toInteger n₁ := hζ₁.toInteger_isPrimitiveRoot
  replace hζ₁ := hζ₁.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F₁) (𝓞 K))
  replace hζ₂ : IsPrimitiveRoot hζ₂.toInteger n₂ := hζ₂.toInteger_isPrimitiveRoot
  replace hζ₂ := hζ₂.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F₂) (𝓞 K))
  rw [← IsDedekindDomain.adjoin_union_eq_top_of_isCoprime_differentialIdeal ℤ (𝓞 K) (𝓞 F₁)
    (𝓞 F₂) h_disj _ _ h₁ h₂, Set.image_singleton, Set.image_singleton, Set.singleton_union]
  · refine (IsPrimitiveRoot.adjoin_pair_eq ℤ hζ₁ hζ₂ (NeZero.ne _) (NeZero.ne _) ?_).symm
    rw [Nat.Coprime.lcm_eq_mul h]
    exact toInteger_isPrimitiveRoot hζ
  · simp [← sup_toSubalgebra_of_left, htop]
  · exact isCoprime_differentIdeal_of_isCoprime_discr _ h_cpr

variable {n K}

set_option backward.isDefEq.respectTransparency false in
open IntermediateField Algebra in
/-
**IsCyclotomicExtension.Rat.adjoin_singleton_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `I
sCyclotomicExtension.Rat`。
形式化陈述：adjoin_singleton_eq_top [hK : IsCyclotomicExtension {n} Rat K] {ζ : K} (hζ
 : IsPrimitiveRoot ζ n) : Int[hζ.toInteger] = ⊤
参数：hζ : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `neZero_zero_iff_false`：∀ {α : Type u_1} [inst : Zero α], NeZero 0 ↔ Fals
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PowerBasis.adjoin_gen_eq_top`：adjoin_gen_eq_top (B : PowerBasis R S) : a
djoin R ({B.gen} : Set S) = ⊤
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `IsPrimitiveRoot.integralPowerBasisOfPrimePow_gen`：integralPowerBasisOfPr
imePow_gen [hcycl : IsCyclotomicExtension {p ^ k} Rat K] (hζ : IsPrimitiveRoot ζ
 (p ^ k)) : hζ.integralPowerBasisOfPri…
· 使用定理 `NeZero.of_gt`：of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero
 b
· 使用定理 `IsPrimitiveRoot.pow`：pow {n : Nat} {a b : Nat} (hn : 0 < n) (h : IsPrimi
tiveRoot ζ n) (hprod : n = a * b) : IsPrimitiveRoot (ζ ^ a) b
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsPrimitiveRoot.intermediateField_adjoin_isCyclotomicExtension`：∀ (K : T
ype w) {L : Type z} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [
Algebra.IsIntegral K L] {n : ℕ}   [NeZero n] {ζ : L}…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsPrimitiveRoot.coe_submonoidClass_iff`：coe_submonoidClass_iff {M B : Ty
pe*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {N : B} {ζ : N} : IsPrimi
tiveRoot (ζ : M) k ↔ IsPrimi…
· 使用定理 `IsCyclotomicExtension.equiv`：equiv {C : Type*} [CommRing C] [Algebra A C
] [h : IsCyclotomicExtension S A B] (f : B ≃ₐ[A] C) : IsCyclotomicExtension S A 
C
· 使用定理 `Nat.Coprime.lcm_eq_mul`：∀ {m n : ℕ}, m.Coprime n → m.lcm n = m * n
· 使用定理 `IntermediateField.isCyclotomicExtension_lcm_sup`：IntermediateField.isCyc
lotomicExtension_lcm_sup [NeZero n₁] [NeZero n₂] : IsCyclotomicExtension {n₁.lcm
 n₂} K (F₁ ⊔ F₂ : IntermediateField K…
· 使用定理 `IntermediateField.isCyclotomicExtension_eq`：IntermediateField.isCyclotom
icExtension_eq (F₁ F₂ : IntermediateField K L) [h₁ : IsCyclotomicExtension S K F
₁] [h₂ : IsCyclotomicExtension S…
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.Cyclotomic.Basic.0.IsCyclotomi
cExtension.Rat.adjoin_singleton_eq_top_aux`：∀ (K : Type u) [inst : Field K] [ins
t_1 : CharZero K] [NumberField K] (F₁ F₂ : IntermediateField ℚ K) {n₁ n₂ : ℕ}   
[inst_3 : NeZero n₁] [in…
-/
theorem adjoin_singleton_eq_top [hK : IsCyclotomicExtension {n} ℚ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    ℤ[hζ.toInteger] = ⊤ := by
  have : NumberField K := IsCyclotomicExtension.numberField {n} ℚ K
  induction n using Nat.recOnPrimeCoprime generalizing K hn with
  | zero => exact (neZero_zero_iff_false.mp hn).elim
  | prime_pow p k hp =>
    have : Fact (p.Prime) := ⟨hp⟩
    rw [← hζ.integralPowerBasisOfPrimePow.adjoin_gen_eq_top, hζ.integralPowerBasisOfPrimePow_gen]
  | coprime n₁ n₂ hn₁ hn₂ h hK₁ hK₂ =>
    have : NeZero n₁ := NeZero.of_gt hn₁
    have : NeZero n₂ := NeZero.of_gt hn₂
    have hζ₁ := hζ.pow (NeZero.pos _) (a := n₂) (b := n₁) (by rw [mul_comm])
    have := hζ₁.intermediateField_adjoin_isCyclotomicExtension ℚ
    replace hζ₁ : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₂)) n₁ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₁
    replace hK₁ := @hK₁ ℚ⟮ζ ^ n₂⟯ _ _ _ _ (AdjoinSimple.gen _ _) hζ₁ (of_intermediateField _)
    have hζ₂ := hζ.pow (NeZero.pos _) (a := n₁) (b := n₂) rfl
    have := hζ₂.intermediateField_adjoin_isCyclotomicExtension ℚ
    replace hζ₂ : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ n₁)) n₂ :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₂
    replace hK₂ := @hK₂ ℚ⟮ζ ^ n₁⟯ _ _ _ _ (AdjoinSimple.gen _ _) hζ₂ (of_intermediateField _)
    have h_top : ℚ⟮ζ ^ n₂⟯ ⊔ ℚ⟮ζ ^ n₁⟯ = ⊤ := by
      have : IsCyclotomicExtension {n₁ * n₂} ℚ (⊤ : IntermediateField ℚ K) :=
          hK.equiv _ _ _ topEquiv.symm
      have : IsCyclotomicExtension {n₁ * n₂} ℚ ↥(ℚ⟮ζ ^ n₂⟯ ⊔ ℚ⟮ζ ^ n₁⟯) := by
        rw [← Nat.Coprime.lcm_eq_mul h]
        exact isCyclotomicExtension_lcm_sup ℚ K n₁ n₂ ℚ⟮ζ ^ n₂⟯ ℚ⟮ζ ^ n₁⟯
      exact isCyclotomicExtension_eq {n₁ * n₂} ℚ K _ _
    exact adjoin_singleton_eq_top_aux K ℚ⟮ζ ^ n₂⟯ ℚ⟮ζ ^ n₁⟯ hζ₁ hK₁ hζ₂ hK₂ h h_top hζ

set_option backward.isDefEq.respectTransparency.types false in
open Algebra in
/-
**IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton** 是 Mathlib 中的一个定
理，位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：isIntegralClosure_adjoin_singleton {ζ : K} [hcycl : IsCyclotomicExtension 
{n} Rat K] (hζ : IsPrimitiveRoot ζ n) : IsIntegralClosure (Int[ζ]) Int K
参数：hζ : IsPrimitiveRoot ζ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Subalgebra.instFaithfulSMulSubtypeMem`：∀ {R : Type u} {A : Type v} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_1}  
 [inst_3 : SMul A α] [Faith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsPurelyInseparable.isIntegral`：∀ {F : Type u_1} {E : Type u_2} {inst : 
CommRing F} {inst_1 : Ring E} {inst_2 : Algebra F E}   [self : IsPurelyInseparab
le F E], Algebra.IsI…
· 使用定理 `instFaithfulSMul_1`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] [IsSimpleRing R]   [Nontrivial A], 
Faithful…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsCyclotomicExtension.Rat.adjoin_singleton_eq_top`：adjoin_singleton_eq_t
op [hK : IsCyclotomicExtension {n} Rat K] {ζ : K} (hζ : IsPrimitiveRoot ζ n) : I
nt[hζ.toInteger] = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureInt`：∀ {K : Type u_1} [i
nst : Field K], IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHom.map_adjoin_singleton`：map_adjoin_singleton (e : A ->ₐ[R] B) (x : 
A) : (R[x]).map e = R[e x]
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `AlgHom.coe_range`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_3 : Semiring B] 
[inst_…
（共 31 条，此处仅展示前 30 条）
-/
theorem isIntegralClosure_adjoin_singleton {ζ : K} [hcycl : IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) :
    IsIntegralClosure (ℤ[ζ]) ℤ K := by
  constructor
  · exact FaithfulSMul.algebraMap_injective _ K
  · intro _
    have := congr_arg (Subalgebra.map (IsScalarTower.toAlgHom ℤ (𝓞 K) K))
      (adjoin_singleton_eq_top hζ)
    simp only [AlgHom.map_adjoin_singleton, IsScalarTower.coe_toAlgHom', RingOfIntegers.map_mk,
      Algebra.map_top] at this
    simp [IsIntegralClosure.isIntegral_iff (A := 𝓞 K), this, ← SetLike.mem_coe]

variable (n)

set_option backward.isDefEq.respectTransparency false in
/-- The integral closure of `ℤ` inside `CyclotomicField n ℚ` is `CyclotomicRing n ℤ ℚ`. -/
/-
**IsCyclotomicExtension.Rat.cyclotomicRing_isIntegralClosure** 是 Mathlib 中的一个定理，
位于命名空间 `IsCyclotomicExtension.Rat`。
形式化陈述：cyclotomicRing_isIntegralClosure : IsIntegralClosure (CyclotomicRing n Int
 Rat) Int (CyclotomicField n Rat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CyclotomicField.instCharZero`：∀ (n : ℕ) (K : Type w) [inst : Field K] [C
harZero K], CharZero (CyclotomicField n K)
· 使用定理 `CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero`：∀ (n
 : ℕ) (K : Type w) [inst : Field K] [CharZero K], IsCyclotomicExtension {n} K (C
yclotomicField n K)
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `CyclotomicRing.instIsFractionRingCyclotomicFieldOfIsDomainOfNeZeroCast`：
∀ (n : ℕ) [NeZero n] (A : Type u) (K : Type w) [inst : CommRing A] [inst_1 : Fie
ld K] [inst_2 : Algebra A K]   [IsFractionRing A K] [IsDomai…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Int.instNeZeroCastOfNat`：∀ {n : ℕ} [NeZero n], NeZero ↑n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegralClosure.isIntegral_iff`：∀ {A : Type u_1} {R : Type u_2} {B : T
ype u_3} {inst : CommRing R} {inst_1 : CommSemiring A} {inst_2 : CommRing B}   {
inst_3 : Algebra R B} …
· 使用定理 `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`：isIntegral
Closure_adjoin_singleton {ζ : K} [hcycl : IsCyclotomicExtension {n} Rat K] (hζ :
 IsPrimitiveRoot ζ n) : IsIntegralClosure (Int[ζ])…
· 使用定理 `Algebra.adjoin_mono`：adjoin_mono (H : s subseteq t) : adjoin R s <= adjo
in R t
· 使用定理 `IsPrimitiveRoot.pow_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M] {ζ : 
M} {k : ℕ}, IsPrimitiveRoot ζ k → ζ ^ k = 1
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `IsCyclotomicExtension.integral`：integral [IsCyclotomicExtension S A B] :
 Algebra.IsIntegral A B

--- 原说明 ---
The integral closure of `ℤ` inside `CyclotomicField n ℚ` is `CyclotomicRing n ℤ 
ℚ`.
-/
theorem cyclotomicRing_isIntegralClosure :
    IsIntegralClosure (CyclotomicRing n ℤ ℚ) ℤ (CyclotomicField n ℚ) := by
  have hζ := zeta_spec n ℚ (CyclotomicField n ℚ)
  refine ⟨IsFractionRing.injective _ _, fun {x} => ⟨fun h => ⟨⟨x, ?_⟩, rfl⟩, ?_⟩⟩
  · obtain ⟨y, rfl⟩ := (isIntegralClosure_adjoin_singleton hζ).isIntegral_iff.1 h
    refine adjoin_mono ?_ y.2
    simp only [Set.singleton_subset_iff, Set.mem_ofPred_eq]
    exact hζ.pow_eq_one
  · rintro ⟨y, rfl⟩
    exact IsIntegral.algebraMap ((IsCyclotomicExtension.integral {n} ℤ _).isIntegral _)

end IsCyclotomicExtension.Rat

namespace IsPrimitiveRoot

variable [NeZero n] [CharZero K]

/-- The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `n`-th root of
unity and `K` is an `n`-th cyclotomic extension of `ℚ`. -/
@[simps!]
/-
**IsPrimitiveRoot.adjoinEquivRingOfIntegers** 是 Mathlib 中的一个定义，位于命名空间 `IsPrimiti
veRoot`。
形式化陈述：adjoinEquivRingOfIntegers [IsCyclotomicExtension {n} Rat K] (hζ : IsPrimit
iveRoot ζ n) : adjoin Int ({ζ} : Set K) ≃ₐ[Int] 𝓞 K
参数：hζ : IsPrimitiveRoot ζ n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`：isIntegral
Closure_adjoin_singleton {ζ : K} [hcycl : IsCyclotomicExtension {n} Rat K] (hζ :
 IsPrimitiveRoot ζ n) : IsIntegralClosure (Int[ζ])…
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureInt`：∀ {K : Type u_1} [i
nst : Field K], IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K

--- 原说明 ---
The algebra isomorphism `adjoin ℤ {ζ} ≃ₐ[ℤ] (𝓞 K)`, where `ζ` is a primitive `n`
-th root of
unity and `K` is an `n`-th cyclotomic extension of `ℚ`.
-/
noncomputable def adjoinEquivRingOfIntegers [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) :
    adjoin ℤ ({ζ} : Set K) ≃ₐ[ℤ] 𝓞 K :=
  let _ := isIntegralClosure_adjoin_singleton hζ
  IsIntegralClosure.equiv ℤ (adjoin ℤ ({ζ} : Set K)) K (𝓞 K)

/-- The ring of integers of an `n`-th cyclotomic extension of `ℚ` is a cyclotomic extension. -/
/-
**IsPrimitiveRoot._root_.IsCyclotomicExtension.ringOfIntegers** 是 Mathlib 中的一个实例
，位于命名空间 `IsPrimitiveRoot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring of integers of an `n`-th cyclotomic extension of `ℚ` is a cyclotomic ex
tension.
-/
instance _root_.IsCyclotomicExtension.ringOfIntegers [IsCyclotomicExtension {n} ℚ K] :
    IsCyclotomicExtension {n} ℤ (𝓞 K) :=
  let _ := (zeta_spec n ℚ K).adjoin_isCyclotomicExtension ℤ
  IsCyclotomicExtension.equiv _ ℤ _ (zeta_spec n ℚ K).adjoinEquivRingOfIntegers

/-- The integral `PowerBasis` of `𝓞 K` given by a primitive root of unity, where `K` is an `n`-th
cyclotomic extension of `ℚ`. -/
/-
**IsPrimitiveRoot.integralPowerBasis** 是 Mathlib 中的一个定义，位于命名空间 `IsPrimitiveRoot`
。
形式化陈述：integralPowerBasis [IsCyclotomicExtension {n} Rat K] (hζ : IsPrimitiveRoot
 ζ n) : PowerBasis Int (𝓞 K)
参数：hζ : IsPrimitiveRoot ζ n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.adjoin.powerBasis'`：Algebra.adjoin.powerBasis'_minpoly_gen [IsDo
main R] [IsDomain S] [IsTorsionFree R S] [IsIntegrallyClosed R] {x : S} (hx' : I
sIntegral R x) :…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ

--- 原说明 ---
The integral `PowerBasis` of `𝓞 K` given by a primitive root of unity, where `K`
 is an `n`-th
cyclotomic extension of `ℚ`.
-/
noncomputable def integralPowerBasis [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) : PowerBasis ℤ (𝓞 K) :=
  (Algebra.adjoin.powerBasis' (hζ.isIntegral (NeZero.pos _))).map hζ.adjoinEquivRingOfIntegers

@[simp]
/-
**IsPrimitiveRoot.integralPowerBasis_gen** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveR
oot`。
形式化陈述：integralPowerBasis_gen [hcycl : IsCyclotomicExtension {n} Rat K] (hζ : IsP
rimitiveRoot ζ n) : hζ.integralPowerBasis.gen = hζ.toInteger
参数：hζ : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Algebra.adjoin.powerBasis'`：Algebra.adjoin.powerBasis'_minpoly_gen [IsDo
main R] [IsDomain S] [IsTorsionFree R S] [IsIntegrallyClosed R] {x : S} (hx' : I
sIntegral R x) :…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsPrimitiveRoot.integralPowerBasis.eq_1`：∀ {n : ℕ} {K : Type u} [inst : 
Field K] {ζ : K} [inst_1 : NeZero n] [inst_2 : CharZero K]   [inst_3 : IsCycloto
micExtension {n} ℚ K] (hζ : I…
· 使用定理 `PowerBasis.map_gen`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] 
[inst_1 : Ring S] [inst_2 : Algebra R S] {S' : Type u_7}   [inst_3 : CommRing S'
] [inst_…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `Algebra.adjoin.powerBasis'_gen`：∀ {R : Type u_1} {S : Type u_2} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : IsDomain R] [inst_3 : Algebra R S]  
 [inst_4 : IsIntegra…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureInt`：∀ {K : Type u_1} [i
nst : Field K], IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K
· 使用定理 `IsIntegralClosure.isIntegral_algebra`：isIntegral_algebra [Algebra R A] [
IsScalarTower R A B] : Algebra.IsIntegral R A
· 使用定理 `IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton`：isIntegral
Closure_adjoin_singleton {ζ : K} [hcycl : IsCyclotomicExtension {n} Rat K] (hζ :
 IsPrimitiveRoot ζ n) : IsIntegralClosure (Int[ζ])…
· 使用定理 `IsPrimitiveRoot.adjoinEquivRingOfIntegers_apply`：∀ {n : ℕ} {K : Type u} 
[inst : Field K] {ζ : K} [inst_1 : NeZero n] [inst_2 : CharZero K]   [inst_3 : I
sCyclotomicExtension {n} ℚ K] (hζ : I…
· 使用定理 `IsIntegralClosure.algebraMap_lift`：algebraMap_lift (x : S) : algebraMap 
A B (lift R A B x) = algebraMap S B x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integralPowerBasis_gen [hcycl : IsCyclotomicExtension {n} ℚ K] (hζ : IsPrimitiveRoot ζ n) :
    hζ.integralPowerBasis.gen = hζ.toInteger :=
  Subtype.ext <| show algebraMap _ K hζ.integralPowerBasis.gen = _ by
    rw [integralPowerBasis, PowerBasis.map_gen, adjoin.powerBasis'_gen]
    simp

@[simp]
/-
**IsPrimitiveRoot.integralPowerBasis_dim** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveR
oot`。
形式化陈述：integralPowerBasis_dim [IsCyclotomicExtension {n} Rat K] (hζ : IsPrimitive
Root ζ n) : hζ.integralPowerBasis.dim = φ n
参数：hζ : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin.powerBasis'`：Algebra.adjoin.powerBasis'_minpoly_gen [IsDo
main R] [IsDomain S] [IsTorsionFree R S] [IsIntegrallyClosed R] {x : S} (hx' : I
sIntegral R x) :…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `PowerBasis.map_dim`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] 
[inst_1 : Ring S] [inst_2 : Algebra R S] {S' : Type u_7}   [inst_3 : CommRing S'
] [inst_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.cyclotomic_eq_minpoly`：cyclotomic_eq_minpoly {n : Nat} {K : T
ype*} [Field K] {μ : K} (h : IsPrimitiveRoot μ n) (hpos : 0 < n) [CharZero K] : 
cyclotomic n Int = min…
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.natDegree_cyclotomic`：natDegree_cyclotomic (n : Nat) (R : Typ
e*) [Ring R] [Nontrivial R] : (cyclotomic n R).natDegree = Nat.totient n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem integralPowerBasis_dim [IsCyclotomicExtension {n} ℚ K] (hζ : IsPrimitiveRoot ζ n) :
    hζ.integralPowerBasis.dim = φ n := by
  simp [integralPowerBasis, ← cyclotomic_eq_minpoly hζ (NeZero.pos _), natDegree_cyclotomic]

set_option backward.isDefEq.respectTransparency.types false in
/-- The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a cyclotomic
extension of `ℚ`. -/
/-
**IsPrimitiveRoot.subOneIntegralPowerBasis** 是 Mathlib 中的一个定义，位于命名空间 `IsPrimitiv
eRoot`。
形式化陈述：subOneIntegralPowerBasis [IsCyclotomicExtension {n} Rat K] (hζ : IsPrimiti
veRoot ζ n) : PowerBasis Int (𝓞 K)
参数：hζ : IsPrimitiveRoot ζ n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)

--- 原说明 ---
The integral `PowerBasis` of `𝓞 K` given by `ζ - 1`, where `K` is a cyclotomic
extension of `ℚ`.
-/
noncomputable def subOneIntegralPowerBasis [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) : PowerBasis ℤ (𝓞 K) :=
  PowerBasis.ofAdjoinEqTop'
    (RingOfIntegers.isIntegral ⟨ζ- 1, (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one⟩) (by
    refine hζ.integralPowerBasis.adjoin_eq_top_of_gen_mem_adjoin ?_
    convert! Subalgebra.add_mem _ (self_mem_adjoin_singleton ℤ _) (Subalgebra.one_mem _)
    simp [RingOfIntegers.ext_iff, integralPowerBasis_gen, toInteger])

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**IsPrimitiveRoot.subOneIntegralPowerBasis_gen** 是 Mathlib 中的一个定理，位于命名空间 `IsPrim
itiveRoot`。
形式化陈述：subOneIntegralPowerBasis_gen [IsCyclotomicExtension {n} Rat K] (hζ : IsPri
mitiveRoot ζ n) : hζ.subOneIntegralPowerBasis.gen = ⟨ζ - 1, Subalgebra.sub_mem _
 (hζ.isIntegral (NeZero.pos _)) (Subalgebra.one_mem _)⟩
参数：hζ : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subalgebra.sub_mem`：∀ {R : Type u} {A : Type v} [inst : CommRing R] [ins
t_1 : Ring A] [inst_2 : Algebra R A] (S : Subalgebra R A) {x y : A},   x ∈ S → y
 ∈ S → x…
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Subalgebra.one_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   1 ∈ S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PowerBasis.ofAdjoinEqTop'_gen`：∀ {R : Type u_1} {S : Type u_2} [inst : C
ommRing R] [inst_1 : CommRing S] [inst_2 : IsDomain R] [inst_3 : Algebra R S]   
[inst_4 : IsIntegra…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem subOneIntegralPowerBasis_gen [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) :
    hζ.subOneIntegralPowerBasis.gen =
      ⟨ζ - 1, Subalgebra.sub_mem _ (hζ.isIntegral (NeZero.pos _)) (Subalgebra.one_mem _)⟩ := by
  simp [subOneIntegralPowerBasis]

end IsPrimitiveRoot

end discr

end PowerBasis

section NumberField

open Units

/-
**NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot [NeZero n] {ζ : K} (
hζ : IsPrimitiveRoot ζ n) : n ∣ torsionOrder K
参数：hζ : IsPrimitiveRoot ζ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `IsPrimitiveRoot.isUnit_unit`：isUnit_unit {ζ : M} {n} (hn) (hζ : IsPrimit
iveRoot ζ n) : IsPrimitiveRoot (hζ.isUnit hn).unit n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CommGroup.mem_torsion`：mem_torsion (g : G) : g in torsion G ↔ IsOfFinOrd
er g
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isPeriodicPt_mul_iff_pow_eq_one`：isPeriodicPt_mul_iff_pow_eq_one (x : G)
 : IsPeriodicPt (x * ·) n 1 ↔ x ^ n = 1
· 使用定理 `IsPrimitiveRoot.pow_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M] {ζ : 
M} {k : ℕ}, IsPrimitiveRoot ζ k → ζ ^ k = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subgroup.orderOf_mk`：orderOf_mk (a : G) (ha) : orderOf (⟨a, ha⟩ : H) = o
rderOf a
· 使用定理 `IsPrimitiveRoot.eq_orderOf`：eq_orderOf (h : IsPrimitiveRoot ζ k) : k = o
rderOf ζ
· 使用定理 `orderOf_dvd_natCard`：orderOf_dvd_natCard {G : Type*} [Group G] (x : G) :
 orderOf x ∣ Nat.card G
-/
theorem NumberField.Units.dvd_torsionOrder_of_isPrimitiveRoot [NeZero n] {ζ : K}
    (hζ : IsPrimitiveRoot ζ n) : n ∣ torsionOrder K := by
  replace hζ := (hζ.toInteger_isPrimitiveRoot).isUnit_unit (NeZero.ne n)
  convert! orderOf_dvd_natCard (⟨(hζ.isUnit (NeZero.ne n)).unit, ?_⟩ : torsion K)
  · rw [Subgroup.orderOf_mk]
    exact hζ.eq_orderOf
  · refine (CommGroup.mem_torsion _).mpr ⟨n, NeZero.pos n, ?_⟩
    rw [isPeriodicPt_mul_iff_pow_eq_one]
    exact hζ.pow_eq_one

/--
The order of the torsion group of the `n`-th cyclotomic field is `n` if `n` is even and
`2n` if `n` is odd.
-/
/-
**IsCyclotomicExtension.Rat.torsionOrder_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCyclotomicExtension.Rat.torsionOrder_eq [NeZero n] [NumberField K] [hK :
 IsCyclotomicExtension {n} Rat K] : torsionOrder K = if Even n then n else 2 * n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `IsCyclotomicExtension.zeta_spec`：zeta_spec : IsPrimitiveRoot (zeta n A B
) n
· 使用引理 `IsCyclic.exists_ofOrder_eq_natCard`：IsCyclic.exists_ofOrder_eq_natCard [
h : IsCyclic α] : exists g : α, orderOf g = Nat.card α
· 使用定理 `NumberField.Units.instIsCyclicSubtypeUnitsRingOfIntegersMemSubgroupTorsi
on`：∀ (K : Type u_1) [inst : Field K] [NumberField K], IsCyclic ↥(NumberField.Un
its.torsion K)
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.coe_units_iff`：coe_units_iff {ζ : Mˣ} : IsPrimitiveRoot 
(ζ : M) k ↔ IsPrimitiveRoot ζ k
· 使用定理 `IsPrimitiveRoot.coe_submonoidClass_iff`：coe_submonoidClass_iff {M B : Ty
pe*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {N : B} {ζ : N} : IsPrimi
tiveRoot (ζ : M) k ↔ IsPrimi…
· 使用定理 `IsPrimitiveRoot.iff_orderOf`：∀ {M : Type u_1} [inst : CommMonoid M] {k :
 ℕ} {ζ : M}, IsPrimitiveRoot ζ k ↔ orderOf ζ = k
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NumberField.RingOfIntegers.instIsTorsionFree_2`：∀ (K : Type u_4) (L : Ty
pe u_5) [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   Module.IsT
orsionFree (NumberField.RingOfIntege…
· 使用定理 `IsPrimitiveRoot.pow_mul_pow_lcm`：pow_mul_pow_lcm {ζ' : M} {k' : Nat} (hζ
 : IsPrimitiveRoot ζ k) (hζ' : IsPrimitiveRoot ζ' k') (hk : k != 0) (hk' : k' !=
 0) : IsPrimitiveRoot…
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `NumberField.Units.torsionOrder_ne_zero`：torsionOrder_ne_zero : torsionOr
der K != 0
· 使用定理 `NeZero.of_pos`：of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lcm_pos_iff`：∀ {m n : ℕ}, 0 < m.lcm n ↔ 0 < m ∧ 0 < n
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NumberField.Units.torsionOrder_pos`：torsionOrder_pos : 0 < torsionOrder 
K
· 使用定理 `IsCyclotomicExtension.union_of_isPrimitiveRoot`：union_of_isPrimitiveRoot
 [hB : IsCyclotomicExtension S A B] {r : B} (hr : IsPrimitiveRoot r n) : IsCyclo
tomicExtension (S union {n}) A B
· 使用定理 `IsCyclotomicExtension.iff_union_of_dvd`：iff_union_of_dvd (h : exists s i
n S, s != 0 ∧ n ∣ s) : IsCyclotomicExtension S A B ↔ IsCyclotomicExtension (S un
ion {n}) A B
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
The order of the torsion group of the `n`-th cyclotomic field is `n` if `n` is e
ven and
`2n` if `n` is odd.
-/
theorem IsCyclotomicExtension.Rat.torsionOrder_eq [NeZero n] [NumberField K]
    [hK : IsCyclotomicExtension {n} ℚ K] :
    torsionOrder K = if Even n then n else 2 * n := by
  have hζ := hK.zeta_spec
  -- We first prove that `K` contains a primitive root of order `torsionOrder K`
  obtain ⟨μ, hμ⟩ : ∃ μ : torsion K, orderOf μ = torsionOrder K := by
    exact IsCyclic.exists_ofOrder_eq_natCard
  rw [← IsPrimitiveRoot.iff_orderOf, ← IsPrimitiveRoot.coe_submonoidClass_iff,
    ← IsPrimitiveRoot.coe_units_iff] at hμ
  replace hμ := hμ.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 K) K)
  -- Thus, `K` contains a primitive root of order `l = lcm (n, torsionOrder K)`.
  have h := hζ.pow_mul_pow_lcm hμ (NeZero.ne _) (torsionOrder_ne_zero K)
  have : NeZero (n.lcm (torsionOrder K)) :=
    NeZero.of_pos <| Nat.lcm_pos_iff.mpr ⟨NeZero.pos n, torsionOrder_pos K⟩
  -- and therefore `K` is the `l`-th cyclotomic field
  have : IsCyclotomicExtension {n.lcm (torsionOrder K)} ℚ K := by
    have := hK.union_of_isPrimitiveRoot _ _ _ h
    rwa [Set.union_comm, ← IsCyclotomicExtension.iff_union_of_dvd] at this
    exact ⟨n.lcm (torsionOrder K), by simp, NeZero.ne _, Nat.dvd_lcm_left _ _⟩
  -- We deduce the identity `φ(n) = φ(lcm (n, torsionOrder K))`.
  have h_main := (IsCyclotomicExtension.Rat.finrank n K).symm.trans <|
    (IsCyclotomicExtension.Rat.finrank (n.lcm (torsionOrder K)) K)
  obtain hn | hn := Nat.even_or_odd n
  · rw [if_pos hn]
    apply dvd_antisymm
    · have := hn.eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) h_main
      rwa [eq_comm, Nat.lcm_eq_left_iff_dvd] at this
    · exact dvd_torsionOrder_of_isPrimitiveRoot hζ
  · rw [if_neg (Nat.not_even_iff_odd.mpr hn)]
    have := (Nat.eq_or_eq_of_totient_eq_totient (Nat.dvd_lcm_left _ _) h_main).resolve_left ?_
    · rw [this, eq_comm, Nat.lcm_eq_right_iff_dvd]
      exact dvd_torsionOrder_of_isPrimitiveRoot hζ
    · rw [eq_comm, Nat.lcm_eq_left_iff_dvd]
      exact fun h ↦ Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hn h) (even_torsionOrder K)

end NumberField

