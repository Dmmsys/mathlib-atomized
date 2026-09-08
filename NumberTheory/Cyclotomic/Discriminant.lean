/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs

/-!
# Discriminant of cyclotomic fields

We compute the discriminant of a `p ^ n`-th cyclotomic extension.

## Main results
* `IsCyclotomicExtension.discr_odd_prime` : if `p` is an odd prime such that
  `IsCyclotomicExtension {p} K L` and `Irreducible (cyclotomic p K)`, then
  `discr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` for any
  `hζ : IsPrimitiveRoot ζ p`.

-/

public section


universe u v

open Algebra Polynomial Nat IsPrimitiveRoot PowerBasis

open scoped Polynomial Cyclotomic

namespace IsPrimitiveRoot

variable {n : ℕ} [NeZero n] {K : Type u} [Field K] [CharZero K] {ζ : K}
variable [ce : IsCyclotomicExtension {n} ℚ K]

/-- The discriminant of the power basis given by a primitive root of unity `ζ` is the same as the
discriminant of the power basis given by `ζ - 1`. -/
/-
**IsPrimitiveRoot.discr_zeta_eq_discr_zeta_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `Is
PrimitiveRoot`。
形式化陈述：discr_zeta_eq_discr_zeta_sub_one (hζ : IsPrimitiveRoot ζ n) : discr Rat (h
ζ.powerBasis Rat).basis = discr Rat (hζ.subOnePowerBasis Rat).basis
参数：hζ : IsPrimitiveRoot ζ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.finiteDimensional`：finiteDimensional (C : Type z) 
[Finite S] [CommRing C] [Algebra K C] [IsDomain C] [IsCyclotomicExtension S K C]
 : FiniteDimensional K C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsPrimitiveRoot.powerBasis_gen`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsPrimitiveRoot.subOnePowerBasis_gen`：∀ {n : ℕ} [inst : NeZero n] (K : T
ype u) {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain 
L]   [inst_4 : Algebra K L…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Algebra.discr_eq_discr_of_toMatrix_coeff_isIntegral`：Algebra.discr_eq_di
scr_of_toMatrix_coeff_isIntegral [NumberField K] {b : Basis ι Rat K} {b' : Basis
 ι' Rat K} (h : forall i j, IsIntegral In…
· 使用定理 `PowerBasis.toMatrix_isIntegral`：toMatrix_isIntegral {B B' : PowerBasis K
 S} {P : R[X]} (h : aeval B.gen P = B'.gen) (hB : IsIntegral R B.gen) (hmin : mi
npoly K B.gen = (min…
· 使用定理 `IsPrimitiveRoot.isIntegral`：isIntegral (hpos : 0 < n) : IsIntegral Int μ
· 使用定理 `NeZero.pos`：pos [PartialOrder α] [IsBotZeroClass α] (a : α) [NeZero a] :
 0 < a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `minpoly.isIntegrallyClosed_eq_field_fractions'`：isIntegrallyClosed_eq_fi
eld_fractions' [IsDomain S] [Algebra K S] [IsScalarTower R K S] {s : S} (hs : Is
Integral R s) : minpoly K s = (minpo…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The discriminant of the power basis given by a primitive root of unity `ζ` is th
e same as the
discriminant of the power basis given by `ζ - 1`.
-/
theorem discr_zeta_eq_discr_zeta_sub_one (hζ : IsPrimitiveRoot ζ n) :
    discr ℚ (hζ.powerBasis ℚ).basis = discr ℚ (hζ.subOnePowerBasis ℚ).basis := by
  have : NumberField K := @NumberField.mk _ _ _ (IsCyclotomicExtension.finiteDimensional {n} ℚ K)
  have H₁ : (aeval (hζ.powerBasis ℚ).gen) (X - 1 : ℤ[X]) = (hζ.subOnePowerBasis ℚ).gen := by simp
  have H₂ : (aeval (hζ.subOnePowerBasis ℚ).gen) (X + 1 : ℤ[X]) = (hζ.powerBasis ℚ).gen := by simp
  refine discr_eq_discr_of_toMatrix_coeff_isIntegral _ (fun i j => toMatrix_isIntegral H₁ ?_ ?_ _ _)
    fun i j => toMatrix_isIntegral H₂ ?_ ?_ _ _
  · exact hζ.isIntegral (NeZero.pos _)
  · refine minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) (hζ.isIntegral (NeZero.pos _))
  · exact (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one
  · refine minpoly.isIntegrallyClosed_eq_field_fractions' (K := ℚ) ?_
    exact (hζ.isIntegral (NeZero.pos _)).sub isIntegral_one

end IsPrimitiveRoot

namespace IsCyclotomicExtension

variable {p : ℕ} {k : ℕ} {K : Type u} {L : Type v} {ζ : L} [Field K] [Field L]
variable [Algebra K L]

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ (k + 1)} K L`, then the discriminant of
`hζ.powerBasis K` is `(-1) ^ ((p ^ (k + 1).totient) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))`
if `Irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`. -/
/-
**IsCyclotomicExtension.discr_prime_pow_ne_two** 是 Mathlib 中的一个定理，位于命名空间 `IsCycl
otomicExtension`。
形式化陈述：discr_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} K L] [hp : Fac
t p.Prime] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hirr : Irreducible (cyclotomi
c (p ^ (k + 1)) K)) (hk : p ^ (k + 1) != 2) : discr K (hζ.powerBasis K).basis = 
(-1) ^ ((p ^ (k + 1)).totient / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；hirr : Irreducible (cyclotomic (p 
^ (k + 1)) K)；hk : p ^ (k + 1) != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclotomicExtension.neZero'`：neZero' [IsCyclotomicExtension {n} A B] [
IsDomain B] : NeZero (n : A)
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsCyclotomicExtension.finiteDimensional`：finiteDimensional (C : Type z) 
[Finite S] [CommRing C] [Algebra K C] [IsDomain C] [IsCyclotomicExtension S K C]
 : FiniteDimensional K C
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsCyclotomicExtension.isSeparable`：isSeparable [IsCyclotomicExtension S 
K L] : Algebra.IsSeparable K L
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr_powerBasis_eq_norm`：discr_powerBasis_eq_norm [Algebra.IsSe
parable K L] : discr K pb.basis = (-1) ^ (n * (n - 1) / 2) * norm K (aeval pb.ge
n (minpoly K pb.gen).d…
· 使用定理 `IsCyclotomicExtension.finrank`：finrank (hirr : Irreducible (cyclotomic n
 K)) : finrank K L = n.totient
· 使用定理 `IsPrimitiveRoot.powerBasis_gen`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible`：∀ {K : Type u_2} [
inst : Field K] {R : Type u_3} [inst_1 : CommRing R] [IsDomain R] {μ : R} {n : ℕ
}   [inst_3 : Algebra K R],   IsPrimitiveR…
· 使用定理 `Nat.totient_prime_pow`：totient_prime_pow {p : Nat} (hp : p.Prime) {n : N
at} (hn : 0 < n) : φ (p ^ n) = p ^ (n - 1) * (p - 1)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.add_one_sub_one`：∀ (n : ℕ), n + 1 - 1 = n
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 118 条，此处仅展示前 30 条）

--- 原说明 ---
If `p` is a prime and `IsCyclotomicExtension {p ^ (k + 1)} K L`, then the discri
minant of
`hζ.powerBasis K` is `(-1) ^ ((p ^ (k + 1).totient) / 2) * p ^ (p ^ k * ((p - 1)
 * (k + 1) - 1))`
if `Irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`.
-/
theorem discr_prime_pow_ne_two [IsCyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K))
    (hk : p ^ (k + 1) ≠ 2) : discr K (hζ.powerBasis K).basis =
      (-1) ^ ((p ^ (k + 1)).totient / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  have hne := IsCyclotomicExtension.neZero' (p ^ (k + 1)) K L
  have mf : Module.Finite K L := finiteDimensional {p ^ (k + 1)} K L
  have se : Algebra.IsSeparable K L := isSeparable {p ^ (k + 1)} K L
  rw [discr_powerBasis_eq_norm, finrank L hirr, hζ.powerBasis_gen _,
    ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, totient_prime_pow hp.out (succ_pos k),
    Nat.add_one_sub_one]
  have hp2 : p = 2 → k ≠ 0 := by
    rintro rfl rfl
    exact absurd rfl hk
  congr 1
  · rcases eq_or_ne p 2 with (rfl | hp2)
    · rcases Nat.exists_eq_succ_of_ne_zero (hp2 rfl) with ⟨k, rfl⟩
      rw [succ_sub_succ_eq_sub, tsub_zero, mul_one]; simp only [_root_.pow_succ']
      rw [mul_assoc, Nat.mul_div_cancel_left _ zero_lt_two, Nat.mul_div_cancel_left _ zero_lt_two]
      cases k
      · simp
      · simp_rw [_root_.pow_succ', (even_two.mul_right _).neg_one_pow,
          ((even_two.mul_right _).mul_right _).neg_one_pow]
    · have hpo : Odd p := hp.out.odd_of_ne_two hp2
      obtain ⟨a, ha⟩ := (hp.out.even_sub_one hp2).two_dvd
      rw [ha, mul_left_comm, mul_assoc, Nat.mul_div_cancel_left _ two_pos,
        Nat.mul_div_cancel_left _ two_pos, mul_right_comm, pow_mul, (hpo.pow.mul _).neg_one_pow,
        pow_mul, hpo.pow.neg_one_pow]
      refine Nat.Even.sub_odd ?_ (even_two_mul _) odd_one
      rw [mul_left_comm, ← ha]
      exact one_le_mul (one_le_pow _ _ hp.1.pos) (succ_le_iff.2 <| tsub_pos_of_lt hp.1.one_lt)
  · have H := congr_arg (@derivative K _) (cyclotomic_prime_pow_mul_X_pow_sub_one K p k)
    rw [derivative_mul, derivative_sub, derivative_one, sub_zero, derivative_X_pow, C_eq_natCast,
      derivative_sub, derivative_one, sub_zero, derivative_X_pow, C_eq_natCast,
      hζ.minpoly_eq_cyclotomic_of_irreducible hirr] at H
    replace H := congr_arg (fun P => aeval ζ P) H
    simp only [aeval_add, aeval_mul, minpoly.aeval, zero_mul, add_zero, aeval_natCast,
      map_sub, aeval_one, aeval_X_pow] at H
    replace H := congr_arg (Algebra.norm K) H
    have hnorm : (norm K) (ζ ^ p ^ k - 1) = (p : K) ^ p ^ k := by
      by_cases hp : p = 2
      · exact mod_cast hζ.norm_pow_sub_one_eq_prime_pow_of_ne_zero hirr le_rfl (hp2 hp)
      · exact mod_cast hζ.norm_pow_sub_one_of_prime_ne_two hirr le_rfl hp
    rw [map_mul, hnorm, map_mul, ← map_natCast (algebraMap K L),
      Algebra.norm_algebraMap, finrank L hirr, ← succ_eq_add_one,
      totient_prime_pow hp.out (succ_pos k), Nat.sub_one, Nat.pred_succ] at H
    rw [← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, map_pow, hζ.norm_eq_one hk hirr, one_pow,
      mul_one, cast_pow, ← pow_mul, ← mul_assoc, mul_comm (k + 1), mul_assoc] at H
    have := mul_pos (succ_pos k) (tsub_pos_of_lt hp.out.one_lt)
    rw [← succ_pred_eq_of_pos this, mul_succ, pow_add _ _ (p ^ k)] at H
    replace H := (mul_left_inj' fun h => ?_).1 H
    · simp only [H, mul_comm _ (k + 1)]; norm_cast
    · have := hne.1
      rw [Nat.cast_pow, Ne, pow_eq_zero_iff (by lia)] at this
      exact absurd (eq_zero_of_pow_eq_zero h) this

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ (k + 1)} K L`, then the discriminant of
`hζ.powerBasis K` is `(-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))`
if `Irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`. -/
/-
**IsCyclotomicExtension.discr_prime_pow_ne_two'** 是 Mathlib 中的一个定理，位于命名空间 `IsCyc
lotomicExtension`。
形式化陈述：discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} K L] [hp : Fa
ct p.Prime] (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hirr : Irreducible (cyclotom
ic (p ^ (k + 1)) K)) (hk : p ^ (k + 1) != 2) : discr K (hζ.powerBasis K).basis =
 (-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1))
参数：k + 1；hζ : IsPrimitiveRoot ζ (p ^ (k + 1))；hirr : Irreducible (cyclotomic (p 
^ (k + 1)) K)；hk : p ^ (k + 1) != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.discr.congr_simp`：∀ {ι : Type w} {inst : DecidableEq ι} [inst_1 
: DecidableEq ι] (A : Type u) {B : Type v} [inst_2 : CommRing A]   [inst_3 : Com
mRing B] [inst…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PowerBasis.coe_basis`：coe_basis (pb : PowerBasis R S) : ⇑pb.basis = fun 
i : Fin pb.dim => pb.gen ^ (i : Nat)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsPrimitiveRoot.powerBasis_gen`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `IsCyclotomicExtension.discr_prime_pow_ne_two`：discr_prime_pow_ne_two [Is
CyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact p.Prime] (hζ : IsPrimitiveRoot
 ζ (p ^ (k + 1))) (hirr : Irreduci…

--- 原说明 ---
If `p` is a prime and `IsCyclotomicExtension {p ^ (k + 1)} K L`, then the discri
minant of
`hζ.powerBasis K` is `(-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k 
+ 1) - 1))`
if `Irreducible (cyclotomic (p ^ (k + 1)) K))`, and `p ^ (k + 1) ≠ 2`.
-/
theorem discr_prime_pow_ne_two' [IsCyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) (hirr : Irreducible (cyclotomic (p ^ (k + 1)) K))
    (hk : p ^ (k + 1) ≠ 2) : discr K (hζ.powerBasis K).basis =
      (-1) ^ (p ^ k * (p - 1) / 2) * p ^ (p ^ k * ((p - 1) * (k + 1) - 1)) := by
  simpa [totient_prime_pow hp.out (succ_pos k)] using discr_prime_pow_ne_two hζ hirr hk

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then the discriminant of
`hζ.powerBasis K` is `(-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1))`
if `Irreducible (cyclotomic (p ^ k) K))`. Beware that in the cases `p ^ k = 1` and `p ^ k = 2`
the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to have a uniform result.
See also `IsCyclotomicExtension.discr_prime_pow_eq_unit_mul_pow`. -/
/-
**IsCyclotomicExtension.discr_prime_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicE
xtension`。
形式化陈述：discr_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} K L] [hp : Fact p.P
rime] (hζ : IsPrimitiveRoot ζ (p ^ k)) (hirr : Irreducible (cyclotomic (p ^ k) K
)) : discr K (hζ.powerBasis K).basis = (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (
k - 1) * ((p - 1) * k - 1))
参数：hζ : IsPrimitiveRoot ζ (p ^ k)；hirr : Irreducible (cyclotomic (p ^ k) K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `PowerBasis.coe_basis`：coe_basis (pb : PowerBasis R S) : ⇑pb.basis = fun 
i : Fin pb.dim => pb.gen ^ (i : Nat)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `IsPrimitiveRoot.powerBasis.congr_simp`：∀ {n n_1 : ℕ} (e_n : n = n_1) [in
st : NeZero n] (K : Type u) {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L
]   [inst_3 : IsDomain L] […
· 使用定理 `IsPrimitiveRoot.powerBasis_gen`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `Nat.instNeZeroHPowOfNat_batteries`：∀ {n : ℕ}, NeZero (n ^ 0)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `IsPrimitiveRoot.powerBasis_dim`：∀ {n : ℕ} [inst : NeZero n] (K : Type u)
 {L : Type v} [inst_1 : Field K] [inst_2 : CommRing L] [inst_3 : IsDomain L]   [
inst_4 : Algebra K L…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `minpoly.eq_X_sub_C_of_algebraMap_inj`：eq_X_sub_C_of_algebraMap_inj (a : 
A) (hf : Function.Injective (algebraMap A B)) : minpoly A (algebraMap A B a) = X
 - C a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Polynomial.natDegree_X_sub_C`：natDegree_X_sub_C (x : R) : (X - C x).natD
egree = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then the discriminant
 of
`hζ.powerBasis K` is `(-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1)
 * k - 1))`
if `Irreducible (cyclotomic (p ^ k) K))`. Beware that in the cases `p ^ k = 1` a
nd `p ^ k = 2`
the formula uses `1 / 2 = 0` and `0 - 1 = 0`. It is useful only to have a unifor
m result.
See also `IsCyclotomicExtension.discr_prime_pow_eq_unit_mul_pow`.
-/
theorem discr_prime_pow [hcycl : IsCyclotomicExtension {p ^ k} K L] [hp : Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ (p ^ k)) (hirr : Irreducible (cyclotomic (p ^ k) K)) :
    discr K (hζ.powerBasis K).basis =
      (-1) ^ ((p ^ k).totient / 2) * p ^ (p ^ (k - 1) * ((p - 1) * k - 1)) := by
  rcases k with - | k
  · simp only [coe_basis, _root_.pow_zero, powerBasis_gen _ hζ, totient_one, mul_zero,
      show 1 / 2 = 0 by rfl, discr, traceMatrix]
    have hζone : ζ = 1 := by simpa using hζ
    rw [hζ.powerBasis_dim _, hζone, ← (algebraMap K L).map_one,
      minpoly.eq_X_sub_C_of_algebraMap_inj _ (algebraMap K L).injective, natDegree_X_sub_C]
    simp only [map_one, one_pow, Matrix.det_unique, traceForm_apply, mul_one]
    rw [← (algebraMap K L).map_one, trace_algebraMap, finrank _ hirr]
    simp
  · by_cases hk : p ^ (k + 1) = 2
    · obtain rfl : p = 2 := by
        rw [← pow_one 2] at hk
        exact eq_of_prime_pow_eq (prime_iff.1 hp.out) (prime_iff.1 Nat.prime_two) (succ_pos _) hk
      nth_rw 2 [← pow_one 2] at hk
      replace hk := Nat.pow_right_injective rfl.le hk
      rw [add_eq_right] at hk
      subst hk
      rw [pow_one] at hζ hcycl
      have : natDegree (minpoly K ζ) = 1 := by
        rw [hζ.eq_neg_one_of_two_right, show (-1 : L) = algebraMap K L (-1) by simp,
          minpoly.eq_X_sub_C_of_algebraMap_inj _ (FaithfulSMul.algebraMap_injective K L)]
        exact natDegree_X_sub_C (-1)
      rcases Fin.equiv_iff_eq.2 this with ⟨e⟩
      rw [← Algebra.discr_reindex K (hζ.powerBasis K).basis e, coe_basis, powerBasis_gen]
      simp only [powerBasis_dim,
        zero_add, pow_one, totient_two, reduceDiv, pow_zero, cast_ofNat, tsub_self,
        Nat.add_one_sub_one, mul_one, mul_zero]
      simp_rw [hζ.eq_neg_one_of_two_right, show (-1 : L) = algebraMap K L (-1) by simp]
      convert_to (discr K fun i : Fin 1 ↦ (algebraMap K L) (-1) ^ ↑i) = _
      · congr 1
        ext i
        simp only [map_neg, map_one, Function.comp_apply, Fin.val_eq_zero, _root_.pow_zero]
        suffices (e.symm i : ℕ) = 0 by simp [this]
        rw [← Nat.lt_one_iff]
        convert! (e.symm i).2
        rw [this]
      · simp only [discr, traceMatrix_apply, Matrix.det_unique, Fin.default_eq_zero, Fin.val_zero,
          _root_.pow_zero, traceForm_apply, mul_one]
        rw [← (algebraMap K L).map_one, trace_algebraMap, finrank _ hirr]; simp
    · exact discr_prime_pow_ne_two hζ hirr hk

/-- If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then there are `u : ℤˣ` and
`n : ℕ` such that the discriminant of `hζ.powerBasis K` is `u * p ^ n`. Often this is enough and
less cumbersome to use than `IsCyclotomicExtension.discr_prime_pow`. -/
/-
**IsCyclotomicExtension.discr_prime_pow_eq_unit_mul_pow** 是 Mathlib 中的一个定理，位于命名空
间 `IsCyclotomicExtension`。
形式化陈述：discr_prime_pow_eq_unit_mul_pow [IsCyclotomicExtension {p ^ k} K L] [hp : 
Fact p.Prime] (hζ : IsPrimitiveRoot ζ (p ^ k)) (hirr : Irreducible (cyclotomic (
p ^ k) K)) : exists (u : Intˣ) (n : Nat), discr K (hζ.powerBasis K).basis = u * 
p ^ n
参数：hζ : IsPrimitiveRoot ζ (p ^ k)；hirr : Irreducible (cyclotomic (p ^ k) K)。
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
· 使用定理 `IsCyclotomicExtension.discr_prime_pow`：discr_prime_pow [hcycl : IsCyclot
omicExtension {p ^ k} K L] [hp : Fact p.Prime] (hζ : IsPrimitiveRoot ζ (p ^ k)) 
(hirr : Irreducible (cyclot…
· 使用引理 `Even.neg_one_pow`：Even.neg_one_pow (h : Even n) : (-1 : α) ^ n = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Odd.neg_one_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistrib
Neg α] {n : ℕ}, Odd n → (-1) ^ n = -1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.not_even_iff_odd`：∀ {n : ℕ}, ¬Even n ↔ Odd n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n

--- 原说明 ---
If `p` is a prime and `IsCyclotomicExtension {p ^ k} K L`, then there are `u : ℤ
ˣ` and
`n : ℕ` such that the discriminant of `hζ.powerBasis K` is `u * p ^ n`. Often th
is is enough and
less cumbersome to use than `IsCyclotomicExtension.discr_prime_pow`.
-/
theorem discr_prime_pow_eq_unit_mul_pow [IsCyclotomicExtension {p ^ k} K L]
    [hp : Fact p.Prime] (hζ : IsPrimitiveRoot ζ (p ^ k))
    (hirr : Irreducible (cyclotomic (p ^ k) K)) :
    ∃ (u : ℤˣ) (n : ℕ), discr K (hζ.powerBasis K).basis = u * p ^ n := by
  rw [discr_prime_pow hζ hirr]
  by_cases heven : Even ((p ^ k).totient / 2)
  · exact ⟨1, p ^ (k - 1) * ((p - 1) * k - 1), by rw [heven.neg_one_pow]; simp⟩
  · exact ⟨-1, p ^ (k - 1) * ((p - 1) * k - 1), by
      rw [(not_even_iff_odd.1 heven).neg_one_pow]; simp⟩

/-- If `p` is an odd prime and `IsCyclotomicExtension {p} K L`, then
`discr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` if
`Irreducible (cyclotomic p K)`. -/
/-
**IsCyclotomicExtension.discr_odd_prime** 是 Mathlib 中的一个定理，位于命名空间 `IsCyclotomicE
xtension`。
形式化陈述：discr_odd_prime [IsCyclotomicExtension {p} K L] [hp : Fact p.Prime] (hζ : 
IsPrimitiveRoot ζ p) (hirr : Irreducible (cyclotomic p K)) (hodd : p != 2) : dis
cr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)
参数：hζ : IsPrimitiveRoot ζ p；hirr : Irreducible (cyclotomic p K)；hodd : p != 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Nat.instNeZeroHPow`：∀ {n m : ℕ} [NeZero n], NeZero (n ^ m)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `Nat.totient_prime`：totient_prime {p : Nat} (hp : p.Prime) : φ p = p - 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.sub_sub`：∀ (n m k : ℕ), n - m - k = n - (m + k)
· 使用定理 `IsCyclotomicExtension.discr_prime_pow_ne_two`：discr_prime_pow_ne_two [Is
CyclotomicExtension {p ^ (k + 1)} K L] [hp : Fact p.Prime] (hζ : IsPrimitiveRoot
 ζ (p ^ (k + 1))) (hirr : Irreduci…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `p` is an odd prime and `IsCyclotomicExtension {p} K L`, then
`discr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2)` if
`Irreducible (cyclotomic p K)`.
-/
theorem discr_odd_prime [IsCyclotomicExtension {p} K L] [hp : Fact p.Prime]
    (hζ : IsPrimitiveRoot ζ p) (hirr : Irreducible (cyclotomic p K)) (hodd : p ≠ 2) :
    discr K (hζ.powerBasis K).basis = (-1) ^ ((p - 1) / 2) * p ^ (p - 2) := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} K L := by
    rw [zero_add, pow_one]
    infer_instance
  have hζ' : IsPrimitiveRoot ζ (p ^ (0 + 1)) := by simpa using hζ
  convert! discr_prime_pow_ne_two hζ' (by simpa [hirr]) (by simp [hodd]) using 2
  · rw [zero_add, pow_one, totient_prime hp.out]
  · rw [_root_.pow_zero, one_mul, zero_add, mul_one, Nat.sub_sub]

end IsCyclotomicExtension

