/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.NumDen
public import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Rational root theorem and integral root theorem

This file contains the rational root theorem and integral root theorem.
The rational root theorem (`num_dvd_of_is_root` and `den_dvd_of_is_root`)
for a unique factorization domain `A`
with localization `S`, states that the roots of `p : A[X]` in `A`'s
field of fractions are of the form `x / y` with `x y : A`, `x ∣ p.coeff 0` and
`y ∣ p.leadingCoeff`.
The corollary is the integral root theorem `isInteger_of_is_root_of_monic`:
if `p` is monic, its roots must be integers.
Finally, we use this to show unique factorization domains are integrally closed.

## References

* https://en.wikipedia.org/wiki/Rational_root_theorem
-/

public section


open scoped Polynomial

section ScaleRoots

variable {A K R S : Type*} [CommRing A] [Field K] [CommRing R] [CommRing S]
variable {M : Submonoid A} [Algebra A S] [IsLocalization M S] [Algebra A K] [IsFractionRing A K]

open Finsupp IsFractionRing IsLocalization Polynomial

/-
**scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {A : Type u_1} {S : Type u_4} [inst : CommRing A] [inst_1 : CommRing S] 
{M : Submonoid A} [inst_2 : Algebra A S]   [inst_3 : IsLocalization M S] {p : Po
lynomial A} {r : A} {s : ↥M},   (Polynomial.aeval (IsLocalization.mk' S r s)) p 
= 0 → (Polynomial.aeval ((algebraMap A S) r)) (p.scaleRoots ↑s) = 0
参数：Polynomial.aeval (IsLocalization.mk' S r s)；Polynomial.aeval ((algebraMap A S
) r)；p.scaleRoots ↑s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `IsLocalization.mk'_spec'`：∀ {R : Type u_1} [inst : CommSemiring R] {M : 
Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [
inst_3 : IsLoc…
· 使用定理 `Polynomial.scaleRoots_eval₂_eq_zero`：scaleRoots_eval₂_eq_zero {p : S[X]}
 (f : S ->+* R) {r : R} {s : S} (hr : eval₂ f r p = 0) : eval₂ f (f s * r) (scal
eRoots p s) = 0
-/
theorem scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero {p : A[X]} {r : A} {s : M}
    (hr : aeval (mk' S r s) p = 0) : aeval (algebraMap A S r) (scaleRoots p s) = 0 := by
  convert! scaleRoots_eval₂_eq_zero (algebraMap A S) hr
  funext
  rw [aeval_def, mk'_spec' _ r s]

variable [IsDomain A]
/-
**num_isRoot_scaleRoots_of_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：num_isRoot_scaleRoots_of_aeval_eq_zero [UniqueFactorizationMonoid A] {p : 
A[X]} {x : K} (hr : aeval x p = 0) : IsRoot (scaleRoots p (den A x)) (num A x)
参数：hr : aeval x p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.isRoot_of_eval₂_map_eq_zero`：isRoot_of_eval₂_map_eq_zero (hf 
: Function.Injective f) {r : R} : eval₂ f (f r) p = 0 -> p.IsRoot r
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero`：∀ {A : Type u_1} {S : Typ
e u_4} [inst : CommRing A] [inst_1 : CommRing S] {M : Submonoid A} [inst_2 : Alg
ebra A S]   [inst_3 : IsLocalizatio…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsFractionRing.mk'_num_den`：∀ (A : Type u_1) [inst : CommRing A] [inst_1
 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 :
 Field K] [inst_…
-/
theorem num_isRoot_scaleRoots_of_aeval_eq_zero [UniqueFactorizationMonoid A] {p : A[X]} {x : K}
    (hr : aeval x p = 0) : IsRoot (scaleRoots p (den A x)) (num A x) := by
  apply isRoot_of_eval₂_map_eq_zero (IsFractionRing.injective A K)
  refine scaleRoots_aeval_eq_zero_of_aeval_mk'_eq_zero ?_
  rw [mk'_num_den]
  exact hr

end ScaleRoots

section RationalRootTheorem

variable {A K : Type*} [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A] [Field K]
variable [Algebra A K] [IsFractionRing A K]

open IsFractionRing IsLocalization Polynomial UniqueFactorizationMonoid

/-- **Rational root theorem** part 1:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the numerator of `r` divides the constant coefficient -/
/-
**num_dvd_of_is_root** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：num_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) : num A r ∣ p.c
oeff 0
参数：hr : aeval r p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.dvd_term_of_isRoot_of_dvd_terms`：dvd_term_of_isRoot_of_dvd_te
rms {r p : S} {f : S[X]} (i : Nat) (hr : f.IsRoot r) (h : forall j != i, p ∣ f.c
oeff j * r ^ j) : p ∣ f.coeff i …
· 使用定理 `num_isRoot_scaleRoots_of_aeval_eq_zero`：num_isRoot_scaleRoots_of_aeval_e
q_zero [UniqueFactorizationMonoid A] {p : A[X]} {x : K} (hr : aeval x p = 0) : I
sRoot (scaleRoots p (den A x…
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsFractionRing.num.congr_simp`：∀ (A : Type u_1) [inst : CommRing A] [ins
t_1 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_
3 : Field K] [inst_…
· 使用引理 `IsFractionRing.num_zero`：num_zero : IsFractionRing.num A (0 : K) = 0
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors`：dvd_o
f_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a != 0) (h : forall ⦃d⦄, d 
∣ a -> d ∣ c -> ¬Prime d) : a ∣ b * c -> a ∣ b
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `IsFractionRing.num_den_reduced`：num_den_reduced (x : K) : IsRelPrime (nu
m A x) (den A x)
· 使用定理 `Prime.dvd_of_dvd_pow`：dvd_of_dvd_pow {a : M} {n : Nat} (h : p ∣ a ^ n) :
 p ∣ a

--- 原说明 ---
**Rational root theorem** part 1:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the numerator of `r` divides the constant coefficient
-/
theorem num_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) : num A r ∣ p.coeff 0 := by
  suffices num A r ∣ (scaleRoots p (den A r)).coeff 0 by
    simp only [coeff_scaleRoots] at this
    have inst := Classical.propDecidable
    by_cases hr : num A r = 0
    · simp_all [nonZeroDivisors.coe_ne_zero]
    · refine dvd_of_dvd_mul_left_of_no_prime_factors hr ?_ this
      intro q dvd_num dvd_denom_pow hq
      apply hq.not_isUnit
      exact num_den_reduced A r dvd_num (hq.dvd_of_dvd_pow dvd_denom_pow)
  convert! dvd_term_of_isRoot_of_dvd_terms 0 (num_isRoot_scaleRoots_of_aeval_eq_zero hr) _
  · rw [pow_zero, mul_one]
  intro j hj
  apply dvd_mul_of_dvd_right
  convert! pow_dvd_pow (num A r) (Nat.succ_le_of_lt (bot_lt_iff_ne_bot.mpr hj))
  exact (pow_one _).symm

/-- Rational root theorem part 2:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the denominator of `r` divides the leading coefficient -/
/-
**den_dvd_of_is_root** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：den_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) : (den A r : A)
 ∣ p.leadingCoeff
参数：hr : aeval r p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_scaleRoots_natDegree`：coeff_scaleRoots_natDegree (p : R
[X]) (s : R) : (scaleRoots p s).coeff p.natDegree = p.leadingCoeff
· 使用定理 `Polynomial.dvd_term_of_isRoot_of_dvd_terms`：dvd_term_of_isRoot_of_dvd_te
rms {r p : S} {f : S[X]} (i : Nat) (hr : f.IsRoot r) (h : forall j != i, p ∣ f.c
oeff j * r ^ j) : p ∣ f.coeff i …
· 使用定理 `num_isRoot_scaleRoots_of_aeval_eq_zero`：num_isRoot_scaleRoots_of_aeval_e
q_zero [UniqueFactorizationMonoid A] {p : A[X]} {x : K} (hr : aeval x p = 0) : I
sRoot (scaleRoots p (den A x…
· 使用定理 `Polynomial.coeff_scaleRoots`：coeff_scaleRoots (p : R[X]) (s : R) (i : Na
t) : (scaleRoots p s).coeff i = coeff p i * s ^ (p.natDegree - i)
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `lt_tsub_iff_left`：lt_tsub_iff_left : a < b - c ↔ c + a < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Polynomial.natDegree_scaleRoots`：natDegree_scaleRoots (p : R[X]) (s : R)
 : natDegree (scaleRoots p s) = natDegree p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `UniqueFactorizationMonoid.dvd_of_dvd_mul_left_of_no_prime_factors`：dvd_o
f_dvd_mul_left_of_no_prime_factors {a b c : R} (ha : a != 0) (h : forall ⦃d⦄, d 
∣ a -> d ∣ c -> ¬Prime d) : a ∣ b * c -> a ∣ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `IsFractionRing.num_den_reduced`：num_den_reduced (x : K) : IsRelPrime (nu
m A x) (den A x)
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Rational root theorem part 2:
if `r : f.codomain` is a root of a polynomial over the ufd `A`,
then the denominator of `r` divides the leading coefficient
-/
theorem den_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r p = 0) :
    (den A r : A) ∣ p.leadingCoeff := by
  suffices (den A r : A) ∣ p.leadingCoeff * num A r ^ p.natDegree by
    refine
      dvd_of_dvd_mul_left_of_no_prime_factors (mem_nonZeroDivisors_iff_ne_zero.mp (den A r).2) ?_
        this
    intro q dvd_den dvd_num_pow hq
    apply hq.not_isUnit
    exact num_den_reduced A r (hq.dvd_of_dvd_pow dvd_num_pow) dvd_den
  rw [← coeff_scaleRoots_natDegree]
  apply dvd_term_of_isRoot_of_dvd_terms _ (num_isRoot_scaleRoots_of_aeval_eq_zero hr)
  intro j hj
  by_cases! h : j < p.natDegree
  · rw [coeff_scaleRoots]
    refine (dvd_mul_of_dvd_right ?_ _).mul_right _
    convert! pow_dvd_pow (den A r : A) (Nat.succ_le_iff.mpr (lt_tsub_iff_left.mpr _))
    · exact (pow_one _).symm
    simpa using h
  rw [← natDegree_scaleRoots p (den A r)] at *
  rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_ne h hj.symm),
    zero_mul]
  exact dvd_zero _

/-- **Integral root theorem**:
if `r : f.codomain` is a root of a monic polynomial over the ufd `A`,
then `r` is an integer -/
/-
**isInteger_of_is_root_of_monic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isInteger_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K} (hr : aeva
l r p = 0) : IsInteger A r
参数：hp : Monic p；hr : aeval r p = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.isInteger_of_isUnit_den`：isInteger_of_isUnit_den {x : K} 
(h : IsUnit (den A x : A)) : IsInteger A x
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `den_dvd_of_is_root`：den_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r 
p = 0) : (den A r : A) ∣ p.leadingCoeff

--- 原说明 ---
**Integral root theorem**:
if `r : f.codomain` is a root of a monic polynomial over the ufd `A`,
then `r` is an integer
-/
theorem isInteger_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0) :
    IsInteger A r :=
  isInteger_of_isUnit_den (isUnit_of_dvd_one (hp ▸ den_dvd_of_is_root hr))
/-
**exists_integer_of_is_root_of_monic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_integer_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K} (hr :
 aeval r p = 0) : exists r' : A, r = algebraMap A K r' ∧ r' ∣ p.coeff 0
参数：hp : Monic p；hr : aeval r p = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `den_dvd_of_is_root`：den_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r 
p = 0) : (den A r : A) ∣ p.leadingCoeff
· 使用定理 `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors`：∀ {R : Type u_1} [
inst : CommRing R] {K : Type u_5} [inst_1 : CommRing K] [inst_2 : Algebra R K] [
IsFractionRing R K]   [Nontrivial R] {x : …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsFractionRing.mk'_num_den'`：∀ (A : Type u_1) [inst : CommRing A] [inst_
1 : IsDomain A] [inst_2 : UniqueFactorizationMonoid A] {K : Type u_2}   [inst_3 
: Field K] [inst_…
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
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
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_dvd_mul`：∀ {α : Type u_1} [inst : CommSemigroup α] {a b c d : α}, a 
∣ b → c ∣ d → a * c ∣ b * d
· 使用定理 `num_dvd_of_is_root`：num_dvd_of_is_root {p : A[X]} {r : K} (hr : aeval r 
p = 0) : num A r ∣ p.coeff 0
-/
theorem exists_integer_of_is_root_of_monic {p : A[X]} (hp : Monic p) {r : K} (hr : aeval r p = 0) :
    ∃ r' : A, r = algebraMap A K r' ∧ r' ∣ p.coeff 0 := by
  /- I tried deducing this from above by unwrapping IsInteger,
    but the divisibility condition is annoying -/
  obtain ⟨inv, h_inv⟩ := hp ▸ den_dvd_of_is_root hr
  use num A r * inv, ?_
  · have h : inv ∣ 1 := ⟨den A r, by simpa [mul_comm] using h_inv⟩
    simpa using mul_dvd_mul (num_dvd_of_is_root hr) h
  · have d_ne_zero : algebraMap A K (den A r) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den A r).prop
    nth_rw 1 [← mk'_num_den' A r]
    rw [div_eq_iff d_ne_zero, map_mul, mul_assoc, mul_comm ((algebraMap A K) inv),
      ← map_mul, ← h_inv, map_one, mul_one]

namespace UniqueFactorizationMonoid

/-
**UniqueFactorizationMonoid.integer_of_integral** 是 Mathlib 中的一个定理，位于命名空间 `Uniqu
eFactorizationMonoid`。
形式化陈述：integer_of_integral {x : K} : IsIntegral A x -> IsInteger A x
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isInteger_of_is_root_of_monic`：isInteger_of_is_root_of_monic {p : A[X]} 
(hp : Monic p) {r : K} (hr : aeval r p = 0) : IsInteger A r
-/
theorem integer_of_integral {x : K} : IsIntegral A x → IsInteger A x := fun ⟨_, hp, hx⟩ =>
  isInteger_of_is_root_of_monic hp hx

-- See library note [lower instance priority]
/-
**UniqueFactorizationMonoid.** 是 Mathlib 中的一个实例，位于命名空间 `UniqueFactorizationMonoi
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instIsIntegrallyClosed : IsIntegrallyClosed A :=
  (isIntegrallyClosed_iff (FractionRing A)).mpr fun {_} => integer_of_integral

end UniqueFactorizationMonoid

end RationalRootTheorem

