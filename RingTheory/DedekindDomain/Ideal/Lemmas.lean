/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.OrderIso
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.RingTheory.ChainOfDivisors
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# Dedekind domains and ideals

In this file, we prove some results on the unique factorization monoid structure of the ideals.
The unique factorization of ideals and invertibility of fractional ideals can be found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Main definitions

- `IsDedekindDomain.HeightOneSpectrum` defines the type of nonzero prime ideals of `R`.

## Implementation notes

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## TODO

In #38133, many declarations were moved from the root namespace into `Ideal` or `IsDedekindDomain`.
The deprecations have the effect that downstream files now have to use the fully qualified name
even when the corresponding namespace is `open`ed.

After the deprecations have been removed, the shorter names can be restored:
* In Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind:
  + `Ideal.span_singleton_dvd_span_singleton_iff_dvd` → `span_singleton_dvd_span_singleton_iff_dvd`
     in line 75 (as of 2026-04-17)
  + `Ideal.normalizedFactorsEquivSpanNormalizedFactors` →
    `normalizedFactorsEquivSpanNormalizedFactors` in line 115
  + `Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity` →
    `emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity` in line 129
  + `Ideal.normalizedFactorsEquivSpanNormalizedFactors` →
    `normalizedFactorsEquivSpanNormalizedFactors` in line 221
* In Mathlib.NumberTheory.NumberField.ClassNumber:
  + `Ideal.prod_normalizedFactors_eq_self` → `prod_normalizedFactors_eq_self` in line 122
* In Mathlib.NumberTheory.RamificationInertia.Basic, one could add `open IsDedekindDomain`
  around line 498 and then remove many `IsDedekindDomain.` prefixes below.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

@[expose] public section

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open Module
open scoped nonZeroDivisors Polynomial

section Inverse

variable [Algebra A K] [IsFractionRing A K]

variable {A K}

namespace FractionalIdeal

open Ideal

/-
**FractionalIdeal.exists_notMem_one_of_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Fractio
nalIdeal`。
形式化陈述：exists_notMem_one_of_ne_bot [IsDedekindDomain A] {I : Ideal A} (hI0 : I !=
 ⊥) (hI1 : I != ⊤) : exists x in (I⁻¹ : FractionalIdeal A⁰ K), x ∉ (1 : Fraction
alIdeal A⁰ K)
参数：hI0 : I != ⊥；hI1 : I != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用引理 `FractionalIdeal.not_inv_le_one_of_ne_bot`：not_inv_le_one_of_ne_bot (hI0 
: I != ⊥) (hI1 : I != ⊤) : ¬(I⁻¹ : FractionalIdeal A⁰ K) <= 1
-/
theorem exists_notMem_one_of_ne_bot [IsDedekindDomain A] {I : Ideal A} (hI0 : I ≠ ⊥)
    (hI1 : I ≠ ⊤) : ∃ x ∈ (I⁻¹ : FractionalIdeal A⁰ K), x ∉ (1 : FractionalIdeal A⁰ K) :=
  Set.not_subset.1 <| not_inv_le_one_of_ne_bot hI0 hI1

end FractionalIdeal

end Inverse

section IsDedekindDomain

variable {R A}
variable [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal

namespace Ideal

@[simp]
/-
**Ideal.dvd_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：dvd_span_singleton {I : Ideal A} {x : A} : I ∣ span {x} ↔ x in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
-/
theorem dvd_span_singleton {I : Ideal A} {x : A} : I ∣ span {x} ↔ x ∈ I :=
  dvd_iff_le.trans (span_le.trans Set.singleton_subset_iff)
/-
**Ideal.isPrime_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_of_prime {P : Ideal A} (h : Prime P) : IsPrime P
参数：h : Prime P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.not_isUnit`：not_isUnit : ¬IsUnit p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prime.dvd_or_dvd`：dvd_or_dvd {a b : M} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem isPrime_of_prime {P : Ideal A} (h : Prime P) : IsPrime P := by
  refine ⟨?_, fun hxy => ?_⟩
  · rintro rfl
    rw [← one_eq_top] at h
    exact h.not_isUnit isUnit_one
  · simp only [← dvd_span_singleton, ← span_singleton_mul_span_singleton] at hxy ⊢
    exact h.dvd_or_dvd hxy
/-
**Ideal.prime_of_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h : IsPrime P) : Prime P
参数：hP : P != ⊥；h : IsPrime P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.isUnit_iff`：isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.IsPrime.mul_le`：∀ {R : Type u} [inst : CommSemiring R] {I J P : Id
eal R}, P.IsPrime → (I * J ≤ P ↔ I ≤ P ∨ J ≤ P)
· 使用定理 `Ideal.le_of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {I J : Ideal R},
 I ∣ J → J ≤ I
-/
theorem prime_of_isPrime {P : Ideal A} (hP : P ≠ ⊥) (h : IsPrime P) : Prime P := by
  refine ⟨hP, mt isUnit_iff.mp h.ne_top, fun I J hIJ => ?_⟩
  simpa only [dvd_iff_le] using h.mul_le.mp (le_of_dvd hIJ)
/-
**Ideal.prime_of_mem_primesOver** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prime_of_mem_primesOver {R : Type*} [CommRing R] [Algebra R A] {p : Ideal 
R} [IsDomain R] [IsTorsionFree R A] (hp : p != ⊥) {P : Ideal A} (hP : P in prime
sOver p A) : Prime P
参数：hp : p != ⊥；hP : P in primesOver p A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
· 使用定理 `Ideal.ne_bot_of_mem_primesOver`：ne_bot_of_mem_primesOver [FaithfulSMul A
 B] (hp : p != ⊥) {P : Ideal B} (hP : P in p.primesOver B) : P != ⊥
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem prime_of_mem_primesOver {R : Type*} [CommRing R] [Algebra R A] {p : Ideal R}
    [IsDomain R] [IsTorsionFree R A] (hp : p ≠ ⊥) {P : Ideal A} (hP : P ∈ primesOver p A) :
    Prime P :=
  prime_of_isPrime (ne_bot_of_mem_primesOver hp hP) hP.1

/-- In a Dedekind domain, the (nonzero) prime elements of the monoid with zero `Ideal A`
are exactly the prime ideals. -/
/-
**Ideal.prime_iff_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prime_iff_isPrime {P : Ideal A} (hP : P != ⊥) : Prime P ↔ IsPrime P
参数：hP : P != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P

--- 原说明 ---
In a Dedekind domain, the (nonzero) prime elements of the monoid with zero `Idea
l A`
are exactly the prime ideals.
-/
theorem prime_iff_isPrime {P : Ideal A} (hP : P ≠ ⊥) : Prime P ↔ IsPrime P :=
  ⟨isPrime_of_prime, prime_of_isPrime hP⟩

/-- In a Dedekind domain, the prime ideals are the zero ideal together with the prime elements
of the monoid with zero `Ideal A`. -/
/-
**Ideal.isPrime_iff_bot_or_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_iff_bot_or_prime {P : Ideal A} : IsPrime P ↔ P = ⊥ ∨ Prime P
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P

--- 原说明 ---
In a Dedekind domain, the prime ideals are the zero ideal together with the prim
e elements
of the monoid with zero `Ideal A`.
-/
theorem isPrime_iff_bot_or_prime {P : Ideal A} : IsPrime P ↔ P = ⊥ ∨ Prime P :=
  ⟨fun hp => (eq_or_ne P ⊥).imp_right fun hp0 => prime_of_isPrime hp0 hp, fun hp =>
    hp.elim (fun h => h.symm ▸ isPrime_bot) isPrime_of_prime⟩

@[simp]
/-
**Ideal.prime_span_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prime_span_singleton_iff {a : A} : Prime (span {a}) ↔ Prime a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.singleton_zero`：∀ {α : Type u_2} [inst : Zero α], {0} = 0
· 使用定理 `Ideal.span_zero`：span_zero : span (0 : Set α) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Ideal.prime_iff_isPrime`：prime_iff_isPrime {P : Ideal A} (hP : P != ⊥) :
 Prime P ↔ IsPrime P
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem prime_span_singleton_iff {a : A} : Prime (span {a}) ↔ Prime a := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Set.singleton_zero, span_zero, ← zero_eq_bot, ← not_iff_not]
    simp only [not_prime_zero, not_false_eq_true]
  · have ha' : span {a} ≠ ⊥ := by simpa only [ne_eq, span_singleton_eq_bot] using ha
    rw [prime_iff_isPrime ha', span_singleton_prime ha]

open Submodule.IsPrincipal in
/-
**Ideal.prime_generator_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prime_generator_of_prime {P : Ideal A} (h : Prime P) [P.IsPrincipal] : Pri
me (generator P)
参数：h : Prime P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `Submodule.IsPrincipal.prime_generator_of_isPrime`：prime_generator_of_isP
rime (S : Ideal R) [S.IsPrincipal] [is_prime : S.IsPrime] (ne_bot : S != ⊥) : Pr
ime (generator S)
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
-/
theorem prime_generator_of_prime {P : Ideal A} (h : Prime P) [P.IsPrincipal] :
    Prime (generator P) :=
  have : IsPrime P := isPrime_of_prime h
  prime_generator_of_isPrime _ h.ne_zero

open UniqueFactorizationMonoid in
nonrec theorem mem_normalizedFactors_iff {p I : Ideal A} (hI : I ≠ ⊥) :
    p ∈ normalizedFactors I ↔ p.IsPrime ∧ I ≤ p := by
  rw [← dvd_iff_le]
  by_cases hp : p = 0
  · rw [← zero_eq_bot] at hI
    simp only [hp, zero_notMem_normalizedFactors, zero_dvd_iff, hI, false_iff, not_and,
      not_false_eq_true, implies_true]
  · rwa [mem_normalizedFactors_iff hI, prime_iff_isPrime]

variable (A) in
open UniqueFactorizationMonoid in
/-
**Ideal.mem_primesOver_iff_mem_normalizedFactors** 是 Mathlib 中的一个定理，位于命名空间 `Idea
l`。
形式化陈述：mem_primesOver_iff_mem_normalizedFactors {p : Ideal R} [h : p.IsMaximal] [
Algebra R A] [IsDomain R] [IsTorsionFree R A] (hp : p != ⊥) {P : Ideal A} : P in
 p.primesOver A ↔ P in normalizedFactors (map (algebraMap R A) p)
参数：hp : p != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.primesOver.eq_1`：∀ {A : Type u_2} [inst : CommSemiring A] (p : Ide
al A) (B : Type u_3) [inst_1 : Semiring B] [inst_2 : Algebra A B],   p.primesOve
r B = {P | …
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Ideal.mem_normalizedFactors_iff`：∀ {A : Type u_2} [inst : CommRing A] [i
nst_1 : IsDedekindDomain A] {p I : Ideal A},   I ≠ ⊥ → (p ∈ UniqueFactorizationM
onoid.normalizedFacto…
· 使用定理 `Ideal.map_ne_bot_of_ne_bot`：map_ne_bot_of_ne_bot {R S : Type*} [CommSemi
ring R] [Semiring S] [Algebra R S] [FaithfulSMul R S] {I : Ideal R} (h : I != ⊥)
 : map (algebraM…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
· 使用定理 `Ideal.under_def`：under_def : P.under A = Ideal.comap (algebraMap A B) P
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `Ideal.map_le_iff_le_comap`：map_le_iff_le_comap [RingHomClass F R S] : ma
p f I <= K ↔ I <= comap f K
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsCoatom.le_iff_eq`：IsCoatom.le_iff_eq (ha : IsCoatom a) (hb : b != ⊤) :
 a <= b ↔ b = a
· 使用定理 `Ideal.isMaximal_def`：isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoato
m I
· 使用定理 `Ideal.comap_ne_top`：comap_ne_top [RingHomClass F R S] (hK : K != ⊤) : co
map f K != ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
-/
theorem mem_primesOver_iff_mem_normalizedFactors {p : Ideal R} [h : p.IsMaximal]
    [Algebra R A] [IsDomain R] [IsTorsionFree R A] (hp : p ≠ ⊥) {P : Ideal A} :
    P ∈ p.primesOver A ↔ P ∈ normalizedFactors (map (algebraMap R A) p) := by
  rw [primesOver, Set.mem_ofPred_eq, mem_normalizedFactors_iff (map_ne_bot_of_ne_bot hp),
    liesOver_iff, under_def, and_congr_right_iff, map_le_iff_le_comap]
  intro hP
  refine ⟨fun h ↦ le_of_eq h, fun h' ↦ ((IsCoatom.le_iff_eq (isMaximal_def.mp h) ?_).mp h').symm⟩
  exact comap_ne_top (algebraMap R A) (IsPrime.ne_top hP)
/-
**Ideal.pow_right_strictAnti** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pow_right_strictAnti (I : Ideal A) (hI0 : I != ⊥) (hI1 : I != ⊤) : StrictA
nti (I ^ · : Nat -> Ideal A)
参数：I : Ideal A；hI0 : I != ⊥；hI1 : I != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictAnti_nat_of_succ_lt`：strictAnti_nat_of_succ_lt {f : Nat -> α} (hf 
: forall n, f (n + 1) < f n) : StrictAnti f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.dvdNotUnit_iff_lt`：Ideal.dvdNotUnit_iff_lt {I J : Ideal A} : DvdNo
tUnit I J ↔ J < I
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Ideal.isUnit_iff`：isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
-/
theorem pow_right_strictAnti (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    StrictAnti (I ^ · : ℕ → Ideal A) :=
  strictAnti_nat_of_succ_lt fun e =>
    dvdNotUnit_iff_lt.mp ⟨pow_ne_zero _ hI0, I, mt isUnit_iff.mp hI1, pow_succ I e⟩
/-
**Ideal.pow_lt_self** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pow_lt_self (I : Ideal A) (hI0 : I != ⊥) (hI1 : I != ⊤) (e : Nat) (he : 2 
<= e) : I ^ e < I
参数：I : Ideal A；hI0 : I != ⊥；hI1 : I != ⊤；e : Nat；he : 2 <= e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Ideal.pow_right_strictAnti`：pow_right_strictAnti (I : Ideal A) (hI0 : I 
!= ⊥) (hI1 : I != ⊤) : StrictAnti (I ^ · : Nat -> Ideal A)
-/
theorem pow_lt_self (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) (he : 2 ≤ e) :
    I ^ e < I := by
  convert! I.pow_right_strictAnti hI0 hI1 he
  dsimp only
  rw [pow_one]
/-
**Ideal.exists_mem_pow_notMem_pow_succ** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_mem_pow_notMem_pow_succ (I : Ideal A) (hI0 : I != ⊥) (hI1 : I != ⊤)
 (e : Nat) : exists x in I ^ e, x ∉ I ^ (e + 1)
参数：I : Ideal A；hI0 : I != ⊥；hI1 : I != ⊤；e : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.exists_of_lt`：exists_of_lt : p < q -> exists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.pow_right_strictAnti`：pow_right_strictAnti (I : Ideal A) (hI0 : I 
!= ⊥) (hI1 : I != ⊤) : StrictAnti (I ^ · : Nat -> Ideal A)
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem exists_mem_pow_notMem_pow_succ (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) :
    ∃ x ∈ I ^ e, x ∉ I ^ (e + 1) :=
  SetLike.exists_of_lt (I.pow_right_strictAnti hI0 hI1 e.lt_succ_self)

open UniqueFactorizationMonoid
/-
**Ideal.eq_prime_pow_of_succ_lt_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_prime_pow_of_succ_lt_of_le {P I : Ideal A} [P_prime : P.IsPrime] (hP : 
P != ⊥) {i : Nat} (hlt : P ^ (i + 1) < I) (hle : I <= P ^ i) : I = P ^ i
参数：hP : P != ⊥；hlt : P ^ (i + 1) < I；hle : I <= P ^ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
`：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y
 != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_pow`：normalizedFactors_pow {
x : α} (n : Nat) : normalizedFactors (x ^ n) = n • normalizedFactors x
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_irreducible`：normalizedFacto
rs_irreducible {a : α} (ha : Irreducible a) : normalizedFactors a = {normalize a
}
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用引理 `Multiset.nsmul_singleton`：nsmul_singleton (a : α) (n) : n • ({a} : Multi
set α) = replicate n a
· 使用定理 `Multiset.lt_replicate_succ`：lt_replicate_succ {m : Multiset α} {x : α} {
n : Nat} : m < replicate (n + 1) x ↔ m <= replicate n x
· 使用定理 `UniqueFactorizationMonoid.dvdNotUnit_iff_normalizedFactors_lt_normalized
Factors`：dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors {x y : α} (hx : x
 != 0) (hy : y != 0) : DvdNotUnit x y ↔ normalizedFactors x < normali…
· 使用定理 `Ideal.dvdNotUnit_iff_lt`：Ideal.dvdNotUnit_iff_lt {I J : Ideal A} : DvdNo
tUnit I J ↔ J < I
-/
theorem eq_prime_pow_of_succ_lt_of_le {P I : Ideal A} [P_prime : P.IsPrime] (hP : P ≠ ⊥)
    {i : ℕ} (hlt : P ^ (i + 1) < I) (hle : I ≤ P ^ i) : I = P ^ i := by
  refine le_antisymm hle ?_
  have P_prime' := prime_of_isPrime hP P_prime
  have h1 : I ≠ ⊥ := (lt_of_le_of_lt bot_le hlt).ne'
  have := pow_ne_zero i hP
  have h3 := pow_ne_zero (i + 1) hP
  rw [← dvdNotUnit_iff_lt, dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors h1 h3,
    normalizedFactors_pow, normalizedFactors_irreducible P_prime'.irreducible,
    Multiset.nsmul_singleton, Multiset.lt_replicate_succ] at hlt
  rw [← dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors, normalizedFactors_pow,
    normalizedFactors_irreducible P_prime'.irreducible, Multiset.nsmul_singleton]
  all_goals assumption
/-
**Ideal.pow_succ_lt_pow** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：pow_succ_lt_pow {P : Ideal A} [P_prime : P.IsPrime] (hP : P != ⊥) (i : Nat
) : P ^ (i + 1) < P ^ i
参数：hP : P != ⊥；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `pow_inj_of_not_isUnit`：pow_inj_of_not_isUnit {q : M} (hq : ¬IsUnit q) (h
q' : q != 0) {m n : Nat} : q ^ m = q ^ n ↔ m = n
· 使用定理 `Ideal.isUnit_iff`：isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Nat.succ_ne_self`：∀ (n : ℕ), n.succ ≠ n
-/
theorem pow_succ_lt_pow {P : Ideal A} [P_prime : P.IsPrime] (hP : P ≠ ⊥) (i : ℕ) :
    P ^ (i + 1) < P ^ i :=
  lt_of_le_of_ne (pow_le_pow_right (Nat.le_succ _))
    (mt (pow_inj_of_not_isUnit (mt isUnit_iff.mp P_prime.ne_top) hP).mp i.succ_ne_self)

end Ideal

/-
**Associates.le_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Associates.le_singleton_iff (x : A) (n : Nat) (I : Ideal A) : Associates.m
k I ^ n <= Associates.mk (Ideal.span {x}) ↔ x in I ^ n
参数：x : A；n : Nat；I : Ideal A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Associates.le_singleton_iff (x : A) (n : ℕ) (I : Ideal A) :
    Associates.mk I ^ n ≤ Associates.mk (Ideal.span {x}) ↔ x ∈ I ^ n := by
  simp_rw [← Associates.dvd_eq_le, ← Associates.mk_pow, Associates.mk_dvd_mk,
    Ideal.dvd_span_singleton]

variable {K}

namespace FractionalIdeal

/-
**FractionalIdeal.le_inv_comm** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：le_inv_comm {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0) : I <
= J⁻¹ ↔ J <= I⁻¹
参数：hI : I != 0；hJ : J != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.inv_eq`：inv_eq : I⁻¹ = 1 / I
· 使用定理 `FractionalIdeal.le_div_iff_mul_le`：le_div_iff_mul_le {I J J' : Fractiona
lIdeal R₁⁰ K} (hJ' : J' != 0) : I <= J / J' ↔ I * J' <= J
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_inv_comm {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J⁻¹ ↔ J ≤ I⁻¹ := by
  rw [inv_eq, inv_eq, le_div_iff_mul_le hI, le_div_iff_mul_le hJ, mul_comm]
/-
**FractionalIdeal.inv_le_comm** 是 Mathlib 中的一个引理，位于命名空间 `FractionalIdeal`。
形式化陈述：inv_le_comm {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0) : I⁻¹
 <= J ↔ J⁻¹ <= I
参数：hI : I != 0；hJ : J != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用引理 `FractionalIdeal.le_inv_comm`：le_inv_comm {I J : FractionalIdeal A⁰ K} (h
I : I != 0) (hJ : J != 0) : I <= J⁻¹ ↔ J <= I⁻¹
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
-/
lemma inv_le_comm {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I⁻¹ ≤ J ↔ J⁻¹ ≤ I := by
  simpa using le_inv_comm (A := A) (K := K) (inv_ne_zero hI) (inv_ne_zero hJ)

@[simp]
/-
**FractionalIdeal.inv_le_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `FractionalIdeal`。
形式化陈述：inv_le_inv_iff {I J : FractionalIdeal A⁰ K} (hI : I != 0) (hJ : J != 0) : 
I⁻¹ <= J⁻¹ ↔ J <= I
参数：hI : I != 0；hJ : J != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `FractionalIdeal.le_inv_comm`：le_inv_comm {I J : FractionalIdeal A⁰ K} (h
I : I != 0) (hJ : J != 0) : I <= J⁻¹ ↔ J <= I⁻¹
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inv_le_inv_iff {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I⁻¹ ≤ J⁻¹ ↔ J ≤ I := by
  rw [le_inv_comm (inv_ne_zero hI) hJ, inv_inv]

end FractionalIdeal

namespace Ideal

/-- Strengthening of `IsLocalization.exist_integer_multiples`:
Let `J ≠ ⊤` be an ideal in a Dedekind domain `A`, and `f ≠ 0` a finite collection
of elements of `K = Frac(A)`, then we can multiply the elements of `f` by some `a : K`
to find a collection of elements of `A` that is not completely contained in `J`. -/
/-
**Ideal.exist_integer_multiples_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exist_integer_multiples_notMem {J : Ideal A} (hJ : J != ⊤) {ι : Type*} (s 
: Finset ι) (f : ι -> K) {j} (hjs : j in s) (hjf : f j != 0) : exists a : K, (fo
rall i in s, IsLocalization.IsInteger A (a * f i)) ∧ exists i in s, a * f i ∉ (J
 : FractionalIdeal A⁰ K)
参数：hJ : J != ⊤；s : Finset ι；f : ι -> K；hjs : j in s；hjf : f j != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FractionalIdeal.spanFinset_ne_zero`：spanFinset_ne_zero {ι : Type*} {s : 
Finset ι} {f : ι -> K} : spanFinset R₁ s f != 0 ↔ exists j in s, f j != 0
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_lt_of_lt_one_left`：mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 
0 < b) (h : a < 1) : a * b < b
· 使用定理 `FractionalIdeal.instMulPosStrictMonoNonZeroDivisors`：∀ {A : Type u_2} (K
 : Type u_3) [inst : CommRing A] [inst_1 : Field K] [IsDedekindDomain A] [inst_3
 : Algebra A K]   [IsFractionRing A K], M…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `FractionalIdeal.instCanonicallyOrderedAdd`：∀ {R : Type u_1} [inst : Comm
Ring R] {S : Submonoid R} {P : Type u_2} [inst_1 : CommRing P] [inst_2 : Algebra
 R P],   CanonicallyOrderedAdd …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FractionalIdeal.coeIdeal_top`：coeIdeal_top : ((⊤ : Ideal R) : Fractional
Ideal S P) = 1
· 使用定理 `strictMono_of_le_iff_le`：strictMono_of_le_iff_le [Preorder α] [Preorder 
β] {f : α -> β} (h : forall x y, x <= y ↔ f x <= f y) : StrictMono f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `FractionalIdeal.coeIdeal_le_coeIdeal`：coeIdeal_le_coeIdeal (K : Type*) [
CommRing K] [Algebra R K] [IsFractionRing R K] {I J : Ideal R} : (I : Fractional
Ideal R⁰ K) <= J ↔ I <= J
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.lt_iff_le_and_exists`：lt_iff_le_and_exists : p < q ↔ p <= q ∧ ex
ists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `FractionalIdeal.mem_one_iff`：mem_one_iff {x : P} : x in (1 : FractionalI
deal S P) ↔ exists x' : R, algebraMap R P x' = x
· 使用定理 `FractionalIdeal.mem_inv_iff`：mem_inv_iff (hI : I != 0) {x : K} : x in I⁻
¹ ↔ forall y in I, x * y in (1 : FractionalIdeal R₁⁰ K)
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `FractionalIdeal.mem_div_iff_of_ne_zero`：mem_div_iff_of_ne_zero {I J : Fr
actionalIdeal R₁⁰ K} (h : J != 0) {x} : x in I / J ↔ forall y in J, x * y in I
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Strengthening of `IsLocalization.exist_integer_multiples`:
Let `J ≠ ⊤` be an ideal in a Dedekind domain `A`, and `f ≠ 0` a finite collectio
n
of elements of `K = Frac(A)`, then we can multiply the elements of `f` by some `
a : K`
to find a collection of elements of `A` that is not completely contained in `J`.
-/
theorem exist_integer_multiples_notMem {J : Ideal A} (hJ : J ≠ ⊤) {ι : Type*} (s : Finset ι)
    (f : ι → K) {j} (hjs : j ∈ s) (hjf : f j ≠ 0) :
    ∃ a : K,
      (∀ i ∈ s, IsLocalization.IsInteger A (a * f i)) ∧
        ∃ i ∈ s, a * f i ∉ (J : FractionalIdeal A⁰ K) := by
  -- Consider the fractional ideal `I` spanned by the `f`s.
  let I : FractionalIdeal A⁰ K := spanFinset A s f
  have hI0 : I ≠ 0 := spanFinset_ne_zero.mpr ⟨j, hjs, hjf⟩
  -- We claim the multiplier `a` we're looking for is in `I⁻¹ \ (J / I)`.
  suffices ↑J / I < I⁻¹ by
    obtain ⟨_, a, hI, hpI⟩ := SetLike.lt_iff_le_and_exists.mp this
    rw [mem_inv_iff hI0] at hI
    refine ⟨a, fun i hi => ?_, ?_⟩
    -- By definition, `a ∈ I⁻¹` multiplies elements of `I` into elements of `1`,
    -- in other words, `a * f i` is an integer.
    · exact (mem_one_iff _).mp (hI (f i) (Submodule.subset_span (Set.mem_image_of_mem f hi)))
    · contrapose! hpI
      -- And if all `a`-multiples of `I` are an element of `J`,
      -- then `a` is actually an element of `J / I`, contradiction.
      refine (mem_div_iff_of_ne_zero hI0).mpr fun y hy => Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, hi, rfl⟩; exact hpI i hi
      · rw [mul_zero]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy; rw [mul_add]; exact Submodule.add_mem _ hx hy
      · intro b x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ b hx
  -- To show the inclusion of `J / I` into `I⁻¹ = 1 / I`, note that `J < I`.
  rw [div_eq_mul_inv]
  refine mul_lt_of_lt_one_left (by simpa [pos_iff_ne_zero]) ?_
  rw [← coeIdeal_top]
  -- And multiplying by `I⁻¹` is indeed strictly monotone.
  exact
    strictMono_of_le_iff_le (fun _ _ => (coeIdeal_le_coeIdeal K).symm)
      (lt_top_iff_ne_top.mpr hJ)
/-
**Ideal.mul_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：mul_iInf (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι -> Ideal A) : I * ⨅
 i, J i = ⨅ i, I * J i
参数：I : Ideal A；J : ι -> Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.bot_mul`：bot_mul : ⊥ * M = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciInf_const`：∀ {α : Type u_1} {ι : Sort u_4} [inst : ConditionallyComple
tePartialOrderInf α] [hι : Nonempty ι] {a : α}, ⨅ x, a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `Ideal.mul_mono_right`：mul_mono_right (h : J <= K) : I * J <= I * K
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ideal.mul_le_left`：mul_le_left [I.IsTwoSided] : I * J <= I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Submodule.instMulLeftMono`：∀ {R : Type u} [inst : Semiring R] {A : Type 
v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower 
R A A], MulLeft…
· 使用定理 `Submodule.instMulRightMono`：∀ {R : Type u} [inst : Semiring R] {A : Type
 v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTower
 R A A], MulRigh…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_le_mul_iff_of_pos_left`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Ze
ro α] [inst_2 : Preorder α] {a b c : α} [PosMulMono α] [PosMulReflectLE α],   0 
< a → (a * b ≤ a…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Submodule.instIsOrderedRing`：∀ {R : Type u} [inst : CommSemiring R] {A :
 Type v} [inst_1 : Semiring A] [inst_2 : Algebra R A],   IsOrderedRing (Submodul
e R A)
· 使用定理 `FractionalIdeal.instPosMulReflectLEIdeal`：∀ {A : Type u_2} [inst : CommR
ing A] [IsDedekindDomain A], PosMulReflectLE (Ideal A)
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
-/
lemma mul_iInf (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι → Ideal A) :
    I * ⨅ i, J i = ⨅ i, I * J i := by
  by_cases hI : I = 0
  · simp [hI]
  refine (le_iInf fun i ↦ mul_mono_right (iInf_le _ _)).antisymm ?_
  have H : ⨅ i, I * J i ≤ I := (iInf_le _ (Nonempty.some ‹_›)).trans mul_le_left
  obtain ⟨K, hK⟩ := dvd_iff_le.mpr H
  grw [hK, le_iInf (a := K) fun i ↦ ?_]
  rw [← mul_le_mul_iff_of_pos_left (a := I), ← hK]
  · exact iInf_le _ _
  · exact bot_lt_iff_ne_bot.mpr hI
/-
**Ideal.iInf_mul** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：iInf_mul (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι -> Ideal A) : (⨅ i,
 J i) * I = ⨅ i, J i * I
参数：I : Ideal A；J : ι -> Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Ideal.mul_iInf`：mul_iInf (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι -
> Ideal A) : I * ⨅ i, J i = ⨅ i, I * J i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iInf_mul (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι → Ideal A) :
    (⨅ i, J i) * I = ⨅ i, J i * I := by
  simp only [mul_iInf, mul_comm _ I]
/-
**Ideal.mul_inf** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：mul_inf (I J K : Ideal A) : I * (J ⊓ K) = I * J ⊓ I * K
参数：I J K : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] (x y : α), x ⊓ 
y = ⨅ b, bif b then x else y
· 使用引理 `Ideal.mul_iInf`：mul_iInf (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι -
> Ideal A) : I * ⨅ i, J i = ⨅ i, I * J i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma mul_inf (I J K : Ideal A) : I * (J ⊓ K) = I * J ⊓ I * K := by
  rw [inf_eq_iInf, mul_iInf, inf_eq_iInf]
  congr! 2 with ⟨⟩
/-
**Ideal.inf_mul** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：inf_mul (I J K : Ideal A) : (I ⊓ J) * K = I * K ⊓ J * K
参数：I J K : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Ideal.mul_inf`：mul_inf (I J K : Ideal A) : I * (J ⊓ K) = I * J ⊓ I * K
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inf_mul (I J K : Ideal A) : (I ⊓ J) * K = I * K ⊓ J * K := by
  simp only [mul_inf, mul_comm _ K]

end Ideal

/-
**FractionalIdeal.mul_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FractionalIdeal.mul_inf (I J K : FractionalIdeal A⁰ K) : I * (J ⊓ K) = I *
 J ⊓ I * K
参数：I J K : FractionalIdeal A⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mul_inf₀`：mul_inf₀ [SemilatticeInf G₀] [PosMulReflectLT G₀] {c : G₀} (hc
 : 0 <= c) (a b : G₀) : c * (a ⊓ b) = c * a ⊓ c * b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `FractionalIdeal.instPosMulReflectLENonZeroDivisors`：∀ {A : Type u_2} (K 
: Type u_3) [inst : CommRing A] [inst_1 : Field K] [IsDedekindDomain A] [inst_3 
: Algebra A K]   [IsFractionRing A K], P…
· 使用定理 `FractionalIdeal.zero_le`：zero_le (I : FractionalIdeal S P) : 0 <= I
-/
lemma FractionalIdeal.mul_inf (I J K : FractionalIdeal A⁰ K) : I * (J ⊓ K) = I * J ⊓ I * K :=
  mul_inf₀ (zero_le _) _ _
/-
**FractionalIdeal.inf_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FractionalIdeal.inf_mul (I J K : FractionalIdeal A⁰ K) : (I ⊓ J) * K = I *
 K ⊓ J * K
参数：I J K : FractionalIdeal A⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inf_mul₀`：inf_mul₀ [SemilatticeInf G₀] [MulPosReflectLT G₀] {c : G₀} (hc
 : 0 <= c) (a b : G₀) : (a ⊓ b) * c = a * c ⊓ b * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `FractionalIdeal.instMulPosReflectLENonZeroDivisors`：∀ {A : Type u_2} (K 
: Type u_3) [inst : CommRing A] [inst_1 : Field K] [IsDedekindDomain A] [inst_3 
: Algebra A K]   [IsFractionRing A K], M…
· 使用定理 `FractionalIdeal.zero_le`：zero_le (I : FractionalIdeal S P) : 0 <= I
-/
lemma FractionalIdeal.inf_mul (I J K : FractionalIdeal A⁰ K) : (I ⊓ J) * K = I * K ⊓ J * K :=
  inf_mul₀ (zero_le _) _ _

section Gcd

namespace Ideal

/-! ### GCD and LCM of ideals in a Dedekind domain

We show that the gcd of two ideals in a Dedekind domain is just their supremum,
and the lcm is their infimum, and use this to instantiate `NormalizedGCDMonoid (Ideal A)`.
-/


@[simp]
/-
**Ideal.sup_mul_inf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：sup_mul_inf (I J : Ideal A) : (I ⊔ J) * (I ⊓ J) = I * J
参数：I J : Ideal A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gcd_eq_normalize`：gcd_eq_normalize [NormalizedGCDMonoid α] {a b c : α} (
habc : gcd a b ∣ c) (hcab : c ∣ gcd a b) : gcd a b = normalize c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
· 使用定理 `GCDMonoid.gcd_dvd_right`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a b : α), gcd a b ∣ b
· 使用定理 `dvd_gcd_iff`：dvd_gcd_iff [GCDMonoid α] (a b c : α) : a ∣ gcd b c ↔ a ∣ b
 ∧ a ∣ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `lcm_eq_normalize`：lcm_eq_normalize [NormalizedGCDMonoid α] {a b c : α} (
habc : lcm a b ∣ c) (hcab : c ∣ lcm a b) : lcm a b = normalize c
· 使用定理 `lcm_dvd_iff`：lcm_dvd_iff [GCDMonoid α] {a b c : α} : lcm a b ∣ c ↔ a ∣ c
 ∧ b ∣ c
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `dvd_lcm_left`：dvd_lcm_left [GCDMonoid α] (a b : α) : a ∣ lcm a b
· 使用定理 `dvd_lcm_right`：dvd_lcm_right [GCDMonoid α] (a b : α) : b ∣ lcm a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `GCDMonoid.gcd_mul_lcm`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [s
elf : GCDMonoid α] (a b : α), Associated (gcd a b * lcm a b) (a * b)

--- 原说明 ---
### GCD and LCM of ideals in a Dedekind domain

We show that the gcd of two ideals in a Dedekind domain is just their supremum,
and the lcm is their infimum, and use this to instantiate `NormalizedGCDMonoid (
Ideal A)`.
-/
theorem sup_mul_inf (I J : Ideal A) : (I ⊔ J) * (I ⊓ J) = I * J := by
  let := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Ideal A)
  have hgcd : gcd I J = I ⊔ J := by
    rw [gcd_eq_normalize _ _, normalize_eq]
    · rw [dvd_iff_le, sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩
    · rw [dvd_gcd_iff, dvd_iff_le, dvd_iff_le]
      simp
  have hlcm : lcm I J = I ⊓ J := by
    rw [lcm_eq_normalize _ _, normalize_eq]
    · rw [lcm_dvd_iff, dvd_iff_le, dvd_iff_le]
      simp
    · rw [dvd_iff_le, le_inf_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩
  rw [← hgcd, ← hlcm, associated_iff_eq.mp (gcd_mul_lcm _ _)]

/-- Ideals in a Dedekind domain have gcd and lcm operators that (trivially) are compatible with
the normalization operator. -/
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ideals in a Dedekind domain have gcd and lcm operators that (trivially) are comp
atible with
the normalization operator.
-/
noncomputable instance : StrongNormalizedGCDMonoid (Ideal A) :=
  { strongNormalizationMonoid with
    gcd := (· ⊔ ·)
    gcd_dvd_left := fun _ _ => by simpa only [dvd_iff_le] using le_sup_left
    gcd_dvd_right := fun _ _ => by simpa only [dvd_iff_le] using le_sup_right
    dvd_gcd := by
      simp only [dvd_iff_le]
      exact fun h1 h2 => @sup_le (Ideal A) _ _ _ _ h1 h2
    lcm := (· ⊓ ·)
    lcm_zero_left := fun _ => by simp only [zero_eq_bot, bot_inf_eq]
    lcm_zero_right := fun _ => by simp only [zero_eq_bot, inf_bot_eq]
    gcd_mul_lcm := fun _ _ => by rw [associated_iff_eq, sup_mul_inf]
    normalize_gcd := fun _ _ => normalize_eq _
    normalize_lcm := fun _ _ => normalize_eq _ }

-- In fact, any lawful gcd and lcm would equal sup and inf respectively.
@[simp]
/-
**Ideal.gcd_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：gcd_eq_sup (I J : Ideal A) : gcd I J = I ⊔ J
参数：I J : Ideal A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem gcd_eq_sup (I J : Ideal A) : gcd I J = I ⊔ J := rfl

@[simp]
/-
**Ideal.lcm_eq_inf** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：lcm_eq_inf (I J : Ideal A) : lcm I J = I ⊓ J
参数：I J : Ideal A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lcm_eq_inf (I J : Ideal A) : lcm I J = I ⊓ J := rfl
/-
**Ideal.isCoprime_iff_gcd** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isCoprime_iff_gcd {I J : Ideal A} : IsCoprime I J ↔ gcd I J = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.isCoprime_iff_codisjoint`：isCoprime_iff_codisjoint : IsCoprime I J
 ↔ Codisjoint I J
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Ideal.gcd_eq_sup`：gcd_eq_sup (I J : Ideal A) : gcd I J = I ⊔ J
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCoprime_iff_gcd {I J : Ideal A} : IsCoprime I J ↔ gcd I J = 1 := by
  rw [isCoprime_iff_codisjoint, codisjoint_iff, one_eq_top, gcd_eq_sup]

open UniqueFactorizationMonoid
/-
**Ideal.factors_span_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：factors_span_eq {p : K[X]} : factors (span {p}) = (factors p).map (fun q =
> span {q})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Polynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} [inst : Semiring R]
 [IsCancelAdd R] [IsDomain R], IsDomain (Polynomial R)
· 使用定理 `AddCancelMonoid.toIsCancelAdd`：∀ (M : Type u) [inst : AddCancelMonoid M]
, IsCancelAdd M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniqueFactorizationMonoid.factors.congr_simp`：∀ {α : Type u_1} [inst : C
ommMonoidWithZero α] [inst_1 : UniqueFactorizationMonoid α] (a a_1 : α),   a = a
_1 → UniqueFactorizationMonoid.fac…
· 使用定理 `Submodule.span_zero`：span_zero : span R (0 : Set M) = ⊥
· 使用定理 `UniqueFactorizationMonoid.factors_eq_normalizedFactors`：factors_eq_norma
lizedFactors {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M] [S
ubsingleton Mˣ] (x : M) : factors x = normal…
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `UniqueFactorizationMonoid.factors_zero`：factors_zero : factors (0 : α) =
 0
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.prime_span_singleton_iff`：prime_span_singleton_iff {a : A} : Prime
 (span {a}) ↔ Prime a
· 使用定理 `UniqueFactorizationMonoid.prime_of_factor`：prime_of_factor {a : α} (x : 
α) (hx : x in factors a) : Prime x
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `UniqueFactorizationMonoid.factors_prod`：factors_prod {a : α} (ane0 : a !
= 0) : Associated (factors a).prod a
· 使用定理 `Ideal.multiset_prod_span_singleton`：multiset_prod_span_singleton (m : Mu
ltiset R) : (m.map fun x => Ideal.span {x}).prod = Ideal.span ({Multiset.prod m}
 : Set R)
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_prod_of_prime`：normalizedFac
tors_prod_of_prime [Subsingleton αˣ] {m : Multiset α} (h : forall p in m, Prime 
p) : normalizedFactors m.prod = m
-/
theorem factors_span_eq {p : K[X]} : factors (span {p}) = (factors p).map (fun q ↦ span {q}) := by
  rcases eq_or_ne p 0 with rfl | hp; · simpa [Set.singleton_zero] using! normalizedFactors_zero
  have : ∀ q ∈ (factors p).map (fun q ↦ span {q}), Prime q := fun q hq ↦ by
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
    exact prime_span_singleton_iff.mpr <| prime_of_factor r hr
  rw [← span_singleton_eq_span_singleton.mpr (factors_prod hp), ← multiset_prod_span_singleton,
    factors_eq_normalizedFactors, normalizedFactors_prod_of_prime this]

end Ideal

/-
**FractionalIdeal.sup_mul_inf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：FractionalIdeal.sup_mul_inf (I J : FractionalIdeal A⁰ K) : (I ⊓ J) * (I ⊔ 
J) = I * J
参数：I J : FractionalIdeal A⁰ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FractionalIdeal.spanSingleton.congr_simp`：∀ {R : Type u_5} [inst : CommR
ing R] (S : Submonoid R) {P : Type u_6} [inst_1 : CommRing P] [inst_2 : Algebra 
R P]   [inst_3 : IsLocalizatio…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.sup_mul_inf`：sup_mul_inf (I J : Ideal A) : (I ⊔ J) * (I ⊓ J) = I *
 J
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 57 条，此处仅展示前 30 条）
-/
lemma FractionalIdeal.sup_mul_inf (I J : FractionalIdeal A⁰ K) :
    (I ⊓ J) * (I ⊔ J) = I * J := by
  apply mul_left_injective₀ (b := spanSingleton A⁰ (algebraMap A K
    (I.den.1 * I.den.1 * J.den.1 * J.den.1))) (by simp [spanSingleton_eq_zero_iff])
  have := Ideal.sup_mul_inf (Ideal.span {J.den.1} * I.num) (Ideal.span {I.den.1} * J.num)
  simp only [← coeIdeal_inj (K := K), coeIdeal_mul, coeIdeal_sup, coeIdeal_inf,
    ← den_mul_self_eq_num', coeIdeal_span_singleton] at this
  rw [mul_left_comm, ← mul_add, ← mul_add, ← mul_inf₀ (FractionalIdeal.zero_le _),
    ← mul_inf₀ (FractionalIdeal.zero_le _)] at this
  simp only [FractionalIdeal.sup_eq_add, _root_.map_mul, ← spanSingleton_mul_spanSingleton]
  convert! this using 1 <;> ring

end Gcd

end IsDedekindDomain

section IsDedekindDomain

variable {T : Type*} [CommRing T] [IsDedekindDomain T] {I J : Ideal T}

open Multiset UniqueFactorizationMonoid

namespace Ideal

/-
**Ideal.prod_normalizedFactors_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：prod_normalizedFactors_eq_self (hI : I != ⊥) : (normalizedFactors I).prod 
= I
参数：hI : I != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
-/
theorem prod_normalizedFactors_eq_self (hI : I ≠ ⊥) : (normalizedFactors I).prod = I :=
  associated_iff_eq.1 (prod_normalizedFactors hI)

@[deprecated (since := "2026-04-16")]
alias _root_.prod_normalizedFactors_eq_self := prod_normalizedFactors_eq_self
/-
**Ideal.count_le_of_ideal_ge** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：count_le_of_ideal_ge {I J : Ideal T} (h : I <= J) (hI : I != ⊥) (K : Ideal
 T) : count K (normalizedFactors J) <= count K (normalizedFactors I)
参数：h : I <= J；hI : I != ⊥；K : Ideal T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
· 使用定理 `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
`：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y
 != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
-/
theorem count_le_of_ideal_ge
    {I J : Ideal T} (h : I ≤ J) (hI : I ≠ ⊥) (K : Ideal T) :
    count K (normalizedFactors J) ≤ count K (normalizedFactors I) :=
  le_iff_count.1 ((dvd_iff_normalizedFactors_le_normalizedFactors (ne_bot_of_le_ne_bot hI h) hI).1
    (dvd_iff_le.2 h))
    _

@[deprecated (since := "2026-04-16")] alias _root_.count_le_of_ideal_ge := count_le_of_ideal_ge
/-
**Ideal.sup_eq_prod_inf_factors** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：sup_eq_prod_inf_factors (hI : I != ⊥) (hJ : J != ⊥) : I ⊔ J = (normalizedF
actors I inter normalizedFactors J).prod
参数：hI : I != ⊥；hJ : J != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `UniqueFactorizationMonoid.prod_inter_normalizedFactors_ne_zero`：prod_int
er_normalizedFactors_ne_zero [NormalizationMonoid α] [Nontrivial α] (a b : α) : 
(normalizedFactors a inter normalizedFactors b).prod…
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
`：dvd_iff_normalizedFactors_le_normalizedFactors {x y : α} (hx : x != 0) (hy : y
 != 0) : x ∣ y ↔ normalizedFactors x <= normalizedFactors y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `UniqueFactorizationMonoid.normalizedFactors_prod_inter_eq_inter`：normali
zedFactors_prod_inter_eq_inter [Subsingleton αˣ] (a b : α) : normalizedFactors (
normalizedFactors a inter normalizedFactors b).prod =…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
· 使用引理 `Multiset.count_inter`：count_inter (a : α) (s t : Multiset α) : count a (
s inter t) = min (count a s) (count a t)
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `Ideal.count_le_of_ideal_ge`：count_le_of_ideal_ge {I J : Ideal T} (h : I 
<= J) (hI : I != ⊥) (K : Ideal T) : count K (normalizedFactors J) <= count K (no
rmalizedFactors …
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem sup_eq_prod_inf_factors (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I ⊔ J = (normalizedFactors I ∩ normalizedFactors J).prod := by
  have := prod_inter_normalizedFactors_ne_zero I J
  apply le_antisymm
  · rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
    constructor <;>
      rw [dvd_iff_normalizedFactors_le_normalizedFactors this (by assumption),
        normalizedFactors_prod_inter_eq_inter]
    exacts [inf_le_left, inf_le_right]
  · rw [← dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors ?H this,
      normalizedFactors_prod_inter_eq_inter, le_iff_count]
    case H => exact ne_bot_of_le_ne_bot hI le_sup_left
    intro a
    rw [Multiset.count_inter]
    exact le_min (count_le_of_ideal_ge le_sup_left hI a) (count_le_of_ideal_ge le_sup_right hJ a)

@[deprecated (since := "2026-04-16")]
alias _root_.sup_eq_prod_inf_factors := sup_eq_prod_inf_factors
/-
**Ideal.irreducible_pow_sup** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：irreducible_pow_sup (hI : I != ⊥) (hJ : Irreducible J) (n : Nat) : J ^ n ⊔
 I = J ^ min ((normalizedFactors I).count J) n
参数：hI : I != ⊥；hJ : Irreducible J；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.sup_eq_prod_inf_factors`：sup_eq_prod_inf_factors (hI : I != ⊥) (hJ
 : J != ⊥) : I ⊔ J = (normalizedFactors I inter normalizedFactors J).prod
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用引理 `min_comm`：min_comm (a b : α) : min a b = min b a
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_of_irreducible_pow`：normaliz
edFactors_of_irreducible_pow {p : α} (hp : Irreducible p) (k : Nat) : normalized
Factors (p ^ k) = Multiset.replicate k (normalize p)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Multiset.replicate_inter`：replicate_inter (n : Nat) (x : α) (s : Multise
t α) : replicate n x inter s = replicate (min n (s.count x)) x
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
-/
theorem irreducible_pow_sup (hI : I ≠ ⊥) (hJ : Irreducible J) (n : ℕ) :
    J ^ n ⊔ I = J ^ min ((normalizedFactors I).count J) n := by
  rw [sup_eq_prod_inf_factors (pow_ne_zero n hJ.ne_zero) hI, min_comm,
    normalizedFactors_of_irreducible_pow hJ, normalize_eq J, replicate_inter, prod_replicate]

@[deprecated (since := "2026-04-16")] alias _root_.irreducible_pow_sup := irreducible_pow_sup
/-
**Ideal.irreducible_pow_sup_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：irreducible_pow_sup_of_le (hJ : Irreducible J) (n : Nat) (hn : n <= emulti
plicity J I) : J ^ n ⊔ I = J ^ n
参数：hJ : Irreducible J；n : Nat；hn : n <= emultiplicity J I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.irreducible_pow_sup`：irreducible_pow_sup (hI : I != ⊥) (hJ : Irred
ucible J) (n : Nat) : J ^ n ⊔ I = J ^ min ((normalizedFactors I).count J) n
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
-/
theorem irreducible_pow_sup_of_le (hJ : Irreducible J) (n : ℕ) (hn : n ≤ emultiplicity J I) :
    J ^ n ⊔ I = J ^ n := by
  by_cases hI : I = ⊥
  · simp_all
  rw [irreducible_pow_sup hI hJ, min_eq_right]
  rw [emultiplicity_eq_count_normalizedFactors hJ hI, normalize_eq J] at hn
  exact_mod_cast hn

@[deprecated (since := "2026-04-16")]
alias _root_.irreducible_pow_sup_of_le := irreducible_pow_sup_of_le
/-
**Ideal.irreducible_pow_sup_of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：irreducible_pow_sup_of_ge (hI : I != ⊥) (hJ : Irreducible J) (n : Nat) (hn
 : emultiplicity J I <= n) : J ^ n ⊔ I = J ^ multiplicity J I
参数：hI : I != ⊥；hJ : Irreducible J；n : Nat；hn : emultiplicity J I <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.irreducible_pow_sup`：irreducible_pow_sup (hI : I != ⊥) (hJ : Irred
ucible J) (n : Nat) : J ^ n ⊔ I = J ^ min ((normalizedFactors I).count J) n
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `emultiplicity_lt_top`：emultiplicity_lt_top {a b : α} : emultiplicity a b
 < ⊤ ↔ FiniteMultiplicity a b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem irreducible_pow_sup_of_ge (hI : I ≠ ⊥) (hJ : Irreducible J) (n : ℕ)
    (hn : emultiplicity J I ≤ n) : J ^ n ⊔ I = J ^ multiplicity J I := by
  rw [irreducible_pow_sup hI hJ, min_eq_left]
  · congr
    rw [← Nat.cast_inj (R := ℕ∞), ← FiniteMultiplicity.emultiplicity_eq_multiplicity,
      emultiplicity_eq_count_normalizedFactors hJ hI, normalize_eq J]
    rw [← emultiplicity_lt_top]
    apply hn.trans_lt
    simp
  · rw [emultiplicity_eq_count_normalizedFactors hJ hI, normalize_eq J] at hn
    exact_mod_cast hn

@[deprecated (since := "2026-04-16")]
alias _root_.irreducible_pow_sup_of_ge := irreducible_pow_sup_of_ge
/-
**Ideal.eq_prime_pow_mul_coprime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_prime_pow_mul_coprime {I : Ideal T} (hI : I != ⊥) (P : Ideal T) [hpm : 
P.IsMaximal] : exists Q : Ideal T, P ⊔ Q = ⊤ ∧ I = P ^ (Multiset.count P (normal
izedFactors I)) * Q
参数：hI : I != ⊥；P : Ideal T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.sup_multiset_prod_eq_top`：sup_multiset_prod_eq_top {s : Multiset (
Ideal R)} (h : forall p in s, I ⊔ p = ⊤) : I ⊔ s.prod = ⊤
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `Multiset.filter_subset`：filter_subset (s : Multiset α) : filter p s subs
eteq s
· 使用定理 `Ideal.IsMaximal.coprime_of_ne`：∀ {α : Type u} [inst : Semiring α] {M M' 
: Ideal α}, M.IsMaximal → M'.IsMaximal → M ≠ M' → M ⊔ M' = ⊤
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `Multiset.of_mem_filter`：of_mem_filter {a : α} {s} (h : a in filter p s) 
: p a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.prod_normalizedFactors_eq_self`：prod_normalizedFactors_eq_self (hI
 : I != ⊥) : (normalizedFactors I).prod = I
· 使用定理 `Multiset.filter_add_not`：filter_add_not (s : Multiset α) : filter p s + 
filter (fun a => ¬p a) s = s
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `Multiset.pow_count`：pow_count [DecidableEq M] (a : M) : a ^ s.count a = 
(s.filter (Eq a)).prod
-/
theorem eq_prime_pow_mul_coprime {I : Ideal T} (hI : I ≠ ⊥)
    (P : Ideal T) [hpm : P.IsMaximal] :
    ∃ Q : Ideal T, P ⊔ Q = ⊤ ∧ I = P ^ (Multiset.count P (normalizedFactors I)) * Q := by
  use (filter (¬ P = ·) (normalizedFactors I)).prod
  constructor
  · refine P.sup_multiset_prod_eq_top (fun p hpi ↦ ?_)
    have hp : Prime p := prime_of_normalized_factor p (filter_subset _ (normalizedFactors I) hpi)
    exact hpm.coprime_of_ne ((isPrime_of_prime hp).isMaximal hp.ne_zero) (of_mem_filter hpi)
  · nth_rw 1 [← prod_normalizedFactors_eq_self hI, ← filter_add_not (P = ·) (normalizedFactors I)]
    rw [prod_add, pow_count]
/-
**Ideal.map_prime_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：map_prime_of_equiv {R : Type*} [CommRing R] [IsDedekindDomain R] (f : T ≃+
* R) {I : Ideal T} (hI : Prime I) (h : I != ⊥) : Prime (I.map f)
参数：f : T ≃+* R；hI : Prime I；h : I != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.prime_iff_isPrime`：prime_iff_isPrime {P : Ideal A} (hP : P != ⊥) :
 Prime P ↔ IsPrime P
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem map_prime_of_equiv {R : Type*} [CommRing R] [IsDedekindDomain R]
    (f : T ≃+* R) {I : Ideal T} (hI : Prime I) (h : I ≠ ⊥) : Prime (I.map f) := by
  rw [prime_iff_isPrime h] at hI
  exact (prime_iff_isPrime <| (I.map_eq_bot_iff_of_injective f.injective).not.2 h).2
    (map_isPrime_of_equiv _)

@[deprecated (since := "2026-04-16")] alias _root_.map_prime_of_equiv := map_prime_of_equiv

end Ideal

end IsDedekindDomain

/-!
### Height one spectrum of a Dedekind domain
If `R` is a Dedekind domain of Krull dimension 1, the maximal ideals of `R` are exactly its nonzero
prime ideals.
We define `HeightOneSpectrum` and provide lemmas to recover the facts that prime ideals of height
one are prime and irreducible.
-/


namespace IsDedekindDomain

variable [IsDedekindDomain R]

/-- The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of
`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1. -/
@[ext, nolint unusedArguments]
/-
**IsDedekindDomain.HeightOneSpectrum** 是 Mathlib 中的一个归纳类型，位于命名空间 `IsDedekindDoma
in`。
形式化陈述：(R : Type u_1) → [CommRing R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The height one prime spectrum of a Dedekind domain `R` is the type of nonzero pr
ime ideals of
`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1.
-/
structure HeightOneSpectrum where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime
  ne_bot : asIdeal ≠ ⊥

attribute [instance] HeightOneSpectrum.isPrime

variable (v : HeightOneSpectrum R) {R}

namespace HeightOneSpectrum

/-
**IsDedekindDomain.HeightOneSpectrum.isMaximal** 是 Mathlib 中的一个实例，位于命名空间 `IsDede
kindDomain.HeightOneSpectrum`。
形式化陈述：isMaximal : v.asIdeal.IsMaximal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
-/
instance isMaximal : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
/-
**IsDedekindDomain.HeightOneSpectrum.prime** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekind
Domain.HeightOneSpectrum`。
形式化陈述：prime : Prime v.asIdeal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ne_bot`：∀ {R : Type u_1} [inst : Comm
Ring R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal ≠ ⊥
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
-/
theorem prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
/-
**IsDedekindDomain.HeightOneSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomai
n.HeightOneSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (HeightOneSpectrum R) (Ideal R) where
  coe P := P.asIdeal

omit [IsDedekindDomain R] in
/-
**IsDedekindDomain.HeightOneSpectrum.asIdeal_injective** 是 Mathlib 中的一个引理，位于命名空间
 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：asIdeal_injective : (HeightOneSpectrum.asIdeal (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.ext`：∀ {R : Type u_1} {inst : CommRin
g R} {x y : IsDedekindDomain.HeightOneSpectrum R}, x.asIdeal = y.asIdeal → x = y
-/
lemma asIdeal_injective : (HeightOneSpectrum.asIdeal (R := R)).Injective :=
  fun ⦃_ _⦄ h ↦ HeightOneSpectrum.ext h

alias asIdeal_inj := HeightOneSpectrum.ext

/--
The (nonzero) prime elements of the monoid with zero `Ideal R` correspond
to an element of type `HeightOneSpectrum R`.

See `IsDedekindDomain.HeightOneSpectrum.prime` for the inverse direction. -/
@[simps]
/-
**IsDedekindDomain.HeightOneSpectrum.ofPrime** 是 Mathlib 中的一个定义，位于命名空间 `IsDedeki
ndDomain.HeightOneSpectrum`。
形式化陈述：ofPrime {p : Ideal R} (hp : Prime p) : HeightOneSpectrum R
参数：hp : Prime p。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P

--- 原说明 ---
The (nonzero) prime elements of the monoid with zero `Ideal R` correspond
to an element of type `HeightOneSpectrum R`.

See `IsDedekindDomain.HeightOneSpectrum.prime` for the inverse direction.
-/
def ofPrime {p : Ideal R} (hp : Prime p) : HeightOneSpectrum R :=
  ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩

@[simp]
/-
**IsDedekindDomain.HeightOneSpectrum.ofPrime_prime** 是 Mathlib 中的一个定理，位于命名空间 `Is
DedekindDomain.HeightOneSpectrum`。
形式化陈述：ofPrime_prime : ofPrime v.prime = v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.prime`：prime : Prime v.asIdeal
-/
theorem ofPrime_prime : ofPrime v.prime = v := rfl
/-
**IsDedekindDomain.HeightOneSpectrum.irreducible** 是 Mathlib 中的一个定理，位于命名空间 `IsDe
dekindDomain.HeightOneSpectrum`。
形式化陈述：irreducible : Irreducible v.asIdeal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `UniqueFactorizationMonoid.irreducible_iff_prime`：∀ {α : Type u_2} {inst 
: CommMonoidWithZero α} [self : UniqueFactorizationMonoid α] {a : α}, Irreducibl
e a ↔ Prime a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.prime`：prime : Prime v.asIdeal
-/
theorem irreducible : Irreducible v.asIdeal :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mpr v.prime
/-
**IsDedekindDomain.HeightOneSpectrum.associates_irreducible** 是 Mathlib 中的一个定理，位
于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：associates_irreducible : Irreducible Associates.mk v.asIdeal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.irreducible_mk`：irreducible_mk {a : M} : Irreducible (Associa
tes.mk a) ↔ Irreducible a
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.irreducible`：irreducible : Irreducibl
e v.asIdeal
-/
theorem associates_irreducible : Irreducible <| Associates.mk v.asIdeal :=
  Associates.irreducible_mk.mpr v.irreducible

/-- An equivalence between the height one and maximal spectra for rings of Krull dimension 1. -/
/-
**IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum** 是 Mathlib 中的一个定义，位于命
名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：equivMaximalSpectrum (hR : ¬IsField R) : HeightOneSpectrum R ≃ MaximalSpec
trum R where toFun v
参数：hR : ¬IsField R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between the height one and maximal spectra for rings of Krull dim
ension 1.
-/
def equivMaximalSpectrum (hR : ¬IsField R) : HeightOneSpectrum R ≃ MaximalSpectrum R where
  toFun v := ⟨v.asIdeal, v.isPrime.isMaximal v.ne_bot⟩
  invFun v :=
    ⟨v.asIdeal, v.isMaximal.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField v.isMaximal hR⟩

/-- An ideal of `R` is not the whole ring if and only if it is contained in an element of
`HeightOneSpectrum R` -/
/-
**IsDedekindDomain.HeightOneSpectrum.ideal_ne_top_iff_exists** 是 Mathlib 中的一个定理，
位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：ideal_ne_top_iff_exists (hR : ¬IsField R) (I : Ideal R) : I != ⊤ ↔ exists 
P : HeightOneSpectrum R, I <= P.asIdeal
参数：hR : ¬IsField R；I : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.ne_top_iff_exists_maximal`：ne_top_iff_exists_maximal {I : Ideal α}
 : I != ⊤ ↔ exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal

--- 原说明 ---
An ideal of `R` is not the whole ring if and only if it is contained in an eleme
nt of
`HeightOneSpectrum R`
-/
theorem ideal_ne_top_iff_exists (hR : ¬IsField R) (I : Ideal R) :
    I ≠ ⊤ ↔ ∃ P : HeightOneSpectrum R, I ≤ P.asIdeal := by
  rw [Ideal.ne_top_iff_exists_maximal]
  constructor
  · rintro ⟨M, hMmax, hIM⟩
    exact ⟨(equivMaximalSpectrum hR).symm ⟨M, hMmax⟩, hIM⟩
  · rintro ⟨P, hP⟩
    exact ⟨((equivMaximalSpectrum hR) P).asIdeal, ((equivMaximalSpectrum hR) P).isMaximal, hP⟩
/-
**IsDedekindDomain.HeightOneSpectrum.isCoprime_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：isCoprime_of_ne (P Q : HeightOneSpectrum R) (hPQ : P != Q) : IsCoprime P.a
sIdeal Q.asIdeal
参数：P Q : HeightOneSpectrum R；hPQ : P != Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isCoprime_iff_sup_eq`：isCoprime_iff_sup_eq : IsCoprime I J ↔ I ⊔ J
 = ⊤
· 使用定理 `Ideal.IsMaximal.coprime_of_ne`：∀ {α : Type u} [inst : Semiring α] {M M' 
: Ideal α}, M.IsMaximal → M'.IsMaximal → M ≠ M' → M ⊔ M' = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isCoprime_of_ne (P Q : HeightOneSpectrum R) (hPQ : P ≠ Q) : IsCoprime P.asIdeal Q.asIdeal :=
  Ideal.isCoprime_iff_sup_eq.mpr (Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal
    (by simpa [HeightOneSpectrum.ext_iff] using hPQ))
/-
**IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne** 是 Mathlib 中的一个定理，位于命名
空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：isCoprime_pow_of_ne (P Q : HeightOneSpectrum R) (hPQ : P != Q) (n m : Nat)
 : IsCoprime (P.asIdeal ^ n) (Q.asIdeal ^ m)
参数：P Q : HeightOneSpectrum R；hPQ : P != Q；n m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.isCoprime_iff_sup_eq`：isCoprime_iff_sup_eq : IsCoprime I J ↔ I ⊔ J
 = ⊤
· 使用定理 `Ideal.pow_sup_pow_eq_top`：pow_sup_pow_eq_top [I.IsTwoSided] {m n : Nat} 
(h : I ⊔ J = ⊤) : I ^ m ⊔ J ^ n = ⊤
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsCoprime.sup_eq`：∀ {R : Type u} [inst : CommSemiring R] {I J : Ideal R}
, IsCoprime I J → I ⊔ J = ⊤
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isCoprime_of_ne`：isCoprime_of_ne (P Q
 : HeightOneSpectrum R) (hPQ : P != Q) : IsCoprime P.asIdeal Q.asIdeal
-/
theorem isCoprime_pow_of_ne (P Q : HeightOneSpectrum R) (hPQ : P ≠ Q) (n m : ℕ) :
    IsCoprime (P.asIdeal ^ n) (Q.asIdeal ^ m) :=
  Ideal.isCoprime_iff_sup_eq.mpr (Ideal.pow_sup_pow_eq_top (P.isCoprime_of_ne Q hPQ).sup_eq)

variable (R)

/-- A Dedekind domain is equal to the intersection of its localizations at all its height one
non-zero prime ideals viewed as subalgebras of its field of fractions. -/
/-
**IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot** 是 Mathlib 中的一个定理
，位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：iInf_localization_eq_bot [Algebra R K] [hK : IsFractionRing R K] : (⨅ v : 
HeightOneSpectrum R, Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le
_nonZeroDivisors) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isPrime`：∀ {R : Type u_1} [inst : Com
mRing R] (self : IsDedekindDomain.HeightOneSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.mem_iInf`：mem_iInf {ι : Sort*} {S : ι -> Subalgebra R A} {x : A}
 : x in ⨅ i, S i ↔ forall i, x in S i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `IsField.localization_map_bijective`：IsField.localization_map_bijective {
R Rₘ : Type*} [CommRing R] [CommRing Rₘ] {M : Submonoid R} (hM : (0 : R) ∉ M) (h
R : IsField R) [Algebra …
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MaximalSpectrum.iInf_localization_eq_bot`：iInf_localization_eq_bot : (⨅ 
v : MaximalSpectrum R, Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_
le_nonZeroDivisors) = ⊥
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A

--- 原说明 ---
A Dedekind domain is equal to the intersection of its localizations at all its h
eight one
non-zero prime ideals viewed as subalgebras of its field of fractions.
-/
theorem iInf_localization_eq_bot [Algebra R K] [hK : IsFractionRing R K] :
    (⨅ v : HeightOneSpectrum R,
        Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_iInf]
  constructor
  on_goal 1 => by_cases hR : IsField R
  · rcases Function.bijective_iff_has_inverse.mp
      (IsField.localization_map_bijective (Rₘ := K) (flip nonZeroDivisors.ne_zero rfl : 0 ∉ R⁰) hR)
      with ⟨algebra_map_inv, _, algebra_map_right_inv⟩
    exact fun _ => Algebra.mem_bot.mpr ⟨algebra_map_inv x, algebra_map_right_inv x⟩
  all_goals rw [← MaximalSpectrum.iInf_localization_eq_bot, Algebra.mem_iInf]
  · exact fun hx ⟨v, hv⟩ => hx ((equivMaximalSpectrum hR).symm ⟨v, hv⟩)
  · exact fun hx ⟨v, hv, hbot⟩ => hx ⟨v, hv.isMaximal hbot⟩

section RingEquiv

variable {R} {S : Type*} [CommRing S]

/-- A surjective ring homomorphism `f : R →+* S` induces a map from `HeightOneSpectrum S` to
  `HeightOneSpectrum R` sending `v` to `v.asIdeal.comap f`. -/
@[simps]
/-
**IsDedekindDomain.HeightOneSpectrum.comap** 是 Mathlib 中的一个定义，位于命名空间 `IsDedekind
Domain.HeightOneSpectrum`。
形式化陈述：comap (f : R ->+* S) (hf : Function.Surjective f) (v : HeightOneSpectrum S
) : (HeightOneSpectrum R) where asIdeal
参数：f : R ->+* S；hf : Function.Surjective f；v : HeightOneSpectrum S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A surjective ring homomorphism `f : R →+* S` induces a map from `HeightOneSpectr
um S` to
  `HeightOneSpectrum R` sending `v` to `v.asIdeal.comap f`.
-/
def comap (f : R →+* S) (hf : Function.Surjective f) (v : HeightOneSpectrum S) :
    (HeightOneSpectrum R) where
  asIdeal := v.asIdeal.comap f
  isPrime := v.asIdeal.comap_isPrime f
  ne_bot := (Ideal.eq_bot_of_comap_eq_bot' hf).mt v.ne_bot

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism between `HeightOneSpectrum`s of isomorphic rings. -/
@[simps]
/-
**IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：equivOfRingEquiv (e : R ≃+* S) : (HeightOneSpectrum R) ≃ (HeightOneSpectru
m S) where toFun
参数：e : R ≃+* S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `HeightOneSpectrum`s of isomorphic rings.
-/
def equivOfRingEquiv (e : R ≃+* S) : (HeightOneSpectrum R) ≃ (HeightOneSpectrum S) where
  toFun := HeightOneSpectrum.comap e.symm e.symm.surjective
  invFun := HeightOneSpectrum.comap e e.surjective
  left_inv x := by ext; simp
  right_inv x := by
    ext
    rw [← Ideal.map_comap_eq_self_of_equiv e x.asIdeal]
    simp only [comap_asIdeal, Ideal.mem_comap, RingHom.coe_coe, Ideal.symm_apply_mem_of_equiv_iff]
    exact Iff.rfl
/-
**IsDedekindDomain.HeightOneSpectrum.RingEquiv.nontrivial_heightOneSpectrum** 是 
Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain.HeightOneSpectrum.RingEquiv`。
形式化陈述：∀ {R : Type u_5} {S : Type u_6} [inst : CommRing R] [inst_1 : CommRing S] 
  [Nontrivial (IsDedekindDomain.HeightOneSpectrum S)] (e : R ≃+* S), Nontrivial 
(IsDedekindDomain.HeightOneSpectrum R)
参数：IsDedekindDomain.HeightOneSpectrum S；e : R ≃+* S；IsDedekindDomain.HeightOneSp
ectrum R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontriv
ial β] {f : α → β}, Function.Surjective f → Nontrivial α
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem RingEquiv.nontrivial_heightOneSpectrum {R S : Type*} [CommRing R] [CommRing S]
    [Nontrivial (HeightOneSpectrum S)] (e : R ≃+* S) : Nontrivial (HeightOneSpectrum R) :=
  (equivOfRingEquiv e).surjective.nontrivial

end RingEquiv

end HeightOneSpectrum

end IsDedekindDomain

section

open Ideal

variable {R A}
variable [IsDedekindDomain A] {I : Ideal R} {J : Ideal A}

namespace IsDedekindDomain

/-- The map from ideals of `R` dividing `I` to the ideals of `A` dividing `J` induced by
  a homomorphism `f : R/I →+* A/J` -/
@[simps]
/-
**IsDedekindDomain.idealFactorsFunOfQuotHom** 是 Mathlib 中的一个定义，位于命名空间 `IsDedekin
dDomain`。
形式化陈述：idealFactorsFunOfQuotHom {f : R ⧸ I ->+* A ⧸ J} (hf : Function.Surjective 
f) : {p : Ideal R // p ∣ I} ->o {p : Ideal A // p ∣ J} where toFun X
参数：hf : Function.Surjective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided

--- 原说明 ---
The map from ideals of `R` dividing `I` to the ideals of `A` dividing `J` induce
d by
  a homomorphism `f : R/I →+* A/J`
-/
def idealFactorsFunOfQuotHom {f : R ⧸ I →+* A ⧸ J} (hf : Function.Surjective f) :
    {p : Ideal R // p ∣ I} →o {p : Ideal A // p ∣ J} where
  toFun X := ⟨comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)), by
    have : RingHom.ker (Ideal.Quotient.mk J) ≤
        comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)) :=
      ker_le_comap (Ideal.Quotient.mk J)
    rw [mk_ker] at this
    exact dvd_iff_le.mpr this⟩
  monotone' := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ h
    rw [← Subtype.coe_le_coe, Subtype.coe_mk, Subtype.coe_mk] at h ⊢
    rw [Subtype.coe_mk, comap_le_comap_iff_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective, map_le_iff_le_comap, Subtype.coe_mk,
      comap_map_of_surjective _ hf (map (Ideal.Quotient.mk I) Y)]
    suffices map (Ideal.Quotient.mk I) X ≤ map (Ideal.Quotient.mk I) Y by
      exact le_sup_of_le_left this
    rwa [map_le_iff_le_comap, comap_map_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, mk_ker,
      sup_eq_left.mpr <| le_of_dvd hY]

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsFunOfQuotHom := idealFactorsFunOfQuotHom

@[simp]
/-
**IsDedekindDomain.idealFactorsFunOfQuotHom_id** 是 Mathlib 中的一个定理，位于命名空间 `IsDede
kindDomain`。
形式化陈述：idealFactorsFunOfQuotHom_id : idealFactorsFunOfQuotHom (RingHom.id (A ⧸ J)
).surjective = OrderHom.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHom.surjective`：RingHom.surjective (σ : R₁ ->+* R₂) [t : RingHomSurj
ective σ] : Function.Surjective σ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `Ideal.map_id`：map_id : I.map (RingHom.id R) = I
· 使用定理 `Ideal.comap_map_of_surjective`：comap_map_of_surjective (hf : Function.Su
rjective f) (I : Ideal R) : comap f (map f I) = I ⊔ comap f ⊥
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderHom.mk.congr_simp`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder
 α] [inst_1 : Preorder β] (toFun toFun_1 : α → β)   (e_toFun : toFun = toFun_1) 
(monotone' :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `OrderHom.id_coe`：∀ {α : Type u_2} [inst : Preorder α], ⇑OrderHom.id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem idealFactorsFunOfQuotHom_id :
    idealFactorsFunOfQuotHom (RingHom.id (A ⧸ J)).surjective = OrderHom.id :=
  OrderHom.ext _ _
    (funext fun X => by
      simp only [idealFactorsFunOfQuotHom, map_id, OrderHom.coe_mk, OrderHom.id_coe, id,
        comap_map_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, ←
        RingHom.ker_eq_comap_bot (Ideal.Quotient.mk J), mk_ker,
        sup_eq_left.mpr (dvd_iff_le.mp X.prop), Subtype.coe_eta])

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsFunOfQuotHom_id := idealFactorsFunOfQuotHom_id

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {L : Ideal B}
/-
**IsDedekindDomain.idealFactorsFunOfQuotHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsDe
dekindDomain`。
形式化陈述：idealFactorsFunOfQuotHom_comp {f : R ⧸ I ->+* A ⧸ J} {g : A ⧸ J ->+* B ⧸ L
} (hf : Function.Surjective f) (hg : Function.Surjective g) : (idealFactorsFunOf
QuotHom hg).comp (idealFactorsFunOfQuotHom hf) = idealFactorsFunOfQuotHom (show 
Function.Surjective (g.comp f) from hg.comp hf)
参数：hf : Function.Surjective f；hg : Function.Surjective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.idealFactorsFunOfQuotHom.eq_1`：∀ {R : Type u_1} {A : Ty
pe u_2} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : IsDedekindDomain A] 
{I : Ideal R}   {J : Ideal A} {f : R…
· 使用定理 `OrderHom.comp_coe`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α 
→o β), …
· 使用定理 `OrderHom.coe_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [in
st_1 : Preorder β] (f : α → β) (hf : Monotone f),   ⇑{ toFun := f, monotone' := 
hf } …
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Ideal.map_comap_of_surjective`：map_comap_of_surjective (I : Ideal S) : m
ap f (comap f I) = I
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
-/
theorem idealFactorsFunOfQuotHom_comp {f : R ⧸ I →+* A ⧸ J} {g : A ⧸ J →+* B ⧸ L}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (idealFactorsFunOfQuotHom hg).comp (idealFactorsFunOfQuotHom hf) =
      idealFactorsFunOfQuotHom (show Function.Surjective (g.comp f) from hg.comp hf) := by
  refine OrderHom.ext _ _ (funext fun x => ?_)
  rw [idealFactorsFunOfQuotHom, idealFactorsFunOfQuotHom, OrderHom.comp_coe, OrderHom.coe_mk,
    OrderHom.coe_mk, Function.comp_apply, idealFactorsFunOfQuotHom, OrderHom.coe_mk,
    Subtype.mk_eq_mk, Subtype.coe_mk, map_comap_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, map_map]

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsFunOfQuotHom_comp := idealFactorsFunOfQuotHom_comp

variable [IsDedekindDomain R] (f : R ⧸ I ≃+* A ⧸ J)

/-- The bijection between ideals of `R` dividing `I` and the ideals of `A` dividing `J` induced by
  an isomorphism `f : R/I ≅ A/J`. -/
/-
**IsDedekindDomain.idealFactorsEquivOfQuotEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsDed
ekindDomain`。
形式化陈述：idealFactorsEquivOfQuotEquiv : { p : Ideal R | p ∣ I } ≃o { p : Ideal A | 
p ∣ J }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between ideals of `R` dividing `I` and the ideals of `A` dividing 
`J` induced by
  an isomorphism `f : R/I ≅ A/J`.
-/
def idealFactorsEquivOfQuotEquiv : { p : Ideal R | p ∣ I } ≃o { p : Ideal A | p ∣ J } := by
  have f_surj : Function.Surjective (f : R ⧸ I →+* A ⧸ J) := f.surjective
  have fsym_surj : Function.Surjective (f.symm : A ⧸ J →+* R ⧸ I) := f.symm.surjective
  refine OrderIso.ofHomInv (idealFactorsFunOfQuotHom f_surj) (idealFactorsFunOfQuotHom fsym_surj)
    ?_ ?_
  · simpa using! idealFactorsFunOfQuotHom_comp fsym_surj f_surj
  · simpa using! idealFactorsFunOfQuotHom_comp f_surj fsym_surj

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsEquivOfQuotEquiv := idealFactorsEquivOfQuotEquiv
/-
**IsDedekindDomain.idealFactorsEquivOfQuotEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `
IsDedekindDomain`。
形式化陈述：idealFactorsEquivOfQuotEquiv_symm : (idealFactorsEquivOfQuotEquiv f).symm 
= idealFactorsEquivOfQuotEquiv f.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem idealFactorsEquivOfQuotEquiv_symm :
    (idealFactorsEquivOfQuotEquiv f).symm = idealFactorsEquivOfQuotEquiv f.symm := rfl

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsEquivOfQuotEquiv_symm := idealFactorsEquivOfQuotEquiv_symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsDedekindDomain.idealFactorsEquivOfQuotEquiv_is_dvd_iso** 是 Mathlib 中的一个定理，位于
命名空间 `IsDedekindDomain`。
形式化陈述：idealFactorsEquivOfQuotEquiv_is_dvd_iso {L M : Ideal R} (hL : L ∣ I) (hM :
 M ∣ I) : (idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ : Ideal A) ∣ idealFactorsEquiv
OfQuotEquiv f ⟨M, hM⟩ ↔ L ∣ M
参数：hL : L ∣ I；hM : M ∣ I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `Subtype.mk_le_mk`：mk_le_mk [LE α] {p : α -> Prop} {x y : α} {hx : p x} {
hy : p y} : (⟨x, hx⟩ : Subtype p) <= ⟨y, hy⟩ ↔ x <= y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem idealFactorsEquivOfQuotEquiv_is_dvd_iso {L M : Ideal R} (hL : L ∣ I) (hM : M ∣ I) :
    (idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ : Ideal A) ∣ idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ ↔
      L ∣ M := by
  suffices
    idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ ≤ idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ ↔
      (⟨M, hM⟩ : { p : Ideal R | p ∣ I }) ≤ ⟨L, hL⟩
    by rw [dvd_iff_le, dvd_iff_le, Subtype.coe_le_coe, this, Subtype.mk_le_mk]
  exact (idealFactorsEquivOfQuotEquiv f).le_iff_le

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsEquivOfQuotEquiv_is_dvd_iso := idealFactorsEquivOfQuotEquiv_is_dvd_iso

open UniqueFactorizationMonoid
/-
**IsDedekindDomain.idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_nor
malizedFactors** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain`。
形式化陈述：idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactor
s (hJ : J != ⊥) {L : Ideal R} (hL : L in normalizedFactors I) : ↑(idealFactorsEq
uivOfQuotEquiv f ⟨L, dvd_of_mem_normalizedFactors hL⟩) in normalizedFactors J
参数：hJ : J != ⊥；hL : L in normalizedFactors I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.empty_eq_zero`：empty_eq_zero : (∅ : Multiset α) = 0
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用定理 `mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors`：mem_norma
lizedFactors_factor_dvd_iso_of_mem_normalizedFactors {m p : M} {n : N} (hm : m !
= 0) (hn : n != 0) (hp : p in normalizedFactors m) …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `IsDedekindDomain.idealFactorsEquivOfQuotEquiv_is_dvd_iso`：idealFactorsEq
uivOfQuotEquiv_is_dvd_iso {L M : Ideal R} (hL : L ∣ I) (hM : M ∣ I) : (idealFact
orsEquivOfQuotEquiv f ⟨L, hL⟩ : Ideal A) ∣ ide…
-/
theorem idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors (hJ : J ≠ ⊥)
    {L : Ideal R} (hL : L ∈ normalizedFactors I) :
    ↑(idealFactorsEquivOfQuotEquiv f ⟨L, dvd_of_mem_normalizedFactors hL⟩)
      ∈ normalizedFactors J := by
  have hI : I ≠ ⊥ := by
    intro hI
    rw [hI, bot_eq_zero, normalizedFactors_zero, ← Multiset.empty_eq_zero] at hL
    exact Finset.notMem_empty _ hL
  refine mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEquiv) ?_
  rintro ⟨l, hl⟩ ⟨l', hl'⟩
  rw [Subtype.coe_mk, Subtype.coe_mk]
  apply idealFactorsEquivOfQuotEquiv_is_dvd_iso f

@[deprecated (since := "2026-04-16")]
alias _root_.idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors :=
  idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors

set_option backward.isDefEq.respectTransparency false in
/-- The bijection between the sets of normalized factors of I and J induced by a ring
isomorphism `f : R/I ≅ A/J`. -/
/-
**IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv** 是 Mathlib 中的一个定义，位于命名空间 `
IsDedekindDomain`。
形式化陈述：normalizedFactorsEquivOfQuotEquiv (hI : I != ⊥) (hJ : J != ⊥) : { L : Idea
l R | L in normalizedFactors I } ≃ { M : Ideal A | M in normalizedFactors J } wh
ere toFun j
参数：hI : I != ⊥；hJ : J != ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between the sets of normalized factors of I and J induced by a rin
g
isomorphism `f : R/I ≅ A/J`.
-/
def normalizedFactorsEquivOfQuotEquiv (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    { L : Ideal R | L ∈ normalizedFactors I } ≃ { M : Ideal A | M ∈ normalizedFactors J } where
  toFun j :=
    ⟨idealFactorsEquivOfQuotEquiv f ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩,
      idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f hJ j.prop⟩
  invFun j :=
    ⟨(idealFactorsEquivOfQuotEquiv f).symm ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩, by
      rw [idealFactorsEquivOfQuotEquiv_symm]
      exact
        idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f.symm hI
          j.prop⟩
  left_inv := fun ⟨j, hj⟩ => by simp
  right_inv := fun ⟨j, hj⟩ => by simp

@[deprecated (since := "2026-04-16")]
alias _root_.normalizedFactorsEquivOfQuotEquiv := normalizedFactorsEquivOfQuotEquiv

@[simp]
/-
**IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_symm** 是 Mathlib 中的一个定理，位于命
名空间 `IsDedekindDomain`。
形式化陈述：normalizedFactorsEquivOfQuotEquiv_symm (hI : I != ⊥) (hJ : J != ⊥) : (norm
alizedFactorsEquivOfQuotEquiv f hI hJ).symm = normalizedFactorsEquivOfQuotEquiv 
f.symm hJ hI
参数：hI : I != ⊥；hJ : J != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem normalizedFactorsEquivOfQuotEquiv_symm (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    (normalizedFactorsEquivOfQuotEquiv f hI hJ).symm =
      normalizedFactorsEquivOfQuotEquiv f.symm hJ hI := rfl

@[deprecated (since := "2026-04-16")]
alias _root_.normalizedFactorsEquivOfQuotEquiv_symm := normalizedFactorsEquivOfQuotEquiv_symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The map `normalizedFactorsEquivOfQuotEquiv` preserves multiplicities. -/
/-
**IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplic
ity** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain`。
形式化陈述：normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity (hI : I !
= ⊥) (hJ : J != ⊥) (L : Ideal R) (hL : L in normalizedFactors I) : emultiplicity
 (↑(normalizedFactorsEquivOfQuotEquiv f hI hJ ⟨L, hL⟩)) J = emultiplicity L I
参数：hI : I != ⊥；hJ : J != ⊥；L : Ideal R；hL : L in normalizedFactors I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv.eq_1`：∀ {R : Type u_1
} {A : Type u_2} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : IsDedekindD
omain A] {I : Ideal R}   {J : Ideal A} [inst_…
· 使用定理 `Equiv.coe_fn_mk`：∀ {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l 
: Function.LeftInverse g f) (r : Function.RightInverse g f),   ⇑{ toFun := f, in
vFun …
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors`：
emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors {m p : M}
 {n : N} (hm : m != 0) (hn : n != 0) (hp : p in normalizedFa…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDedekindDomain.idealFactorsEquivOfQuotEquiv_is_dvd_iso`：idealFactorsEq
uivOfQuotEquiv_is_dvd_iso {L M : Ideal R} (hL : L ∣ I) (hM : M ∣ I) : (idealFact
orsEquivOfQuotEquiv f ⟨L, hL⟩ : Ideal A) ∣ ide…

--- 原说明 ---
The map `normalizedFactorsEquivOfQuotEquiv` preserves multiplicities.
-/
theorem normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (L : Ideal R) (hL : L ∈ normalizedFactors I) :
    emultiplicity (↑(normalizedFactorsEquivOfQuotEquiv f hI hJ ⟨L, hL⟩)) J = emultiplicity L I := by
  rw [normalizedFactorsEquivOfQuotEquiv, Equiv.coe_fn_mk, Subtype.coe_mk]
  refine emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEquiv) ?_
  exact fun ⟨l, hl⟩ ⟨l', hl'⟩ => idealFactorsEquivOfQuotEquiv_is_dvd_iso f hl hl'

@[deprecated (since := "2026-04-16")]
alias _root_.normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity :=
  normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity

end IsDedekindDomain

end

noncomputable section ChineseRemainder

open Ideal UniqueFactorizationMonoid

variable {R ι}

/-
**Ring.DimensionLeOne.prime_le_prime_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.DimensionLeOne.prime_le_prime_iff_eq [Ring.DimensionLEOne R] {P Q : I
deal R} [hP : P.IsPrime] [hQ : Q.IsPrime] (hP0 : P != ⊥) : P <= Q ↔ P = Q
参数：hP0 : P != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem Ring.DimensionLeOne.prime_le_prime_iff_eq [Ring.DimensionLEOne R] {P Q : Ideal R}
    [hP : P.IsPrime] [hQ : Q.IsPrime] (hP0 : P ≠ ⊥) : P ≤ Q ↔ P = Q :=
  ⟨(hP.isMaximal hP0).eq_of_le hQ.ne_top, Eq.le⟩

section DedekindDomain

variable [IsDedekindDomain R]

namespace Ideal

/-- See also `Ideal.IsMaximal.mul_mem_pow` for maximal ideal. -/
/-
**Ideal.IsPrime.mul_mem_pow** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [IsDedekindDomain R] (I : Ideal R) [h
I : I.IsPrime] {a b : R} {n : ℕ},   a * b ∈ I ^ n → a ∈ I ∨ b ∈ I ^ n
参数：I : Ideal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Submodule.mul_bot`：mul_bot : M * ⊥ = ⊥
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `Ideal.IsMaximal.mul_mem_pow`：∀ {R : Type u} [inst : CommSemiring R] (I :
 Ideal R) [I.IsMaximal] {a b : R} {n : ℕ}, a * b ∈ I ^ n → a ∈ I ∨ b ∈ I ^ n

--- 原说明 ---
See also `Ideal.IsMaximal.mul_mem_pow` for maximal ideal.
-/
theorem IsPrime.mul_mem_pow (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ}
    (h : a * b ∈ I ^ n) : a ∈ I ∨ b ∈ I ^ n := by
  cases n; · simp
  by_cases hI0 : I = ⊥; · simpa [pow_succ, hI0] using h
  have : I.IsMaximal := hI.isMaximal hI0
  exact IsMaximal.mul_mem_pow I h

/-- See also `Ideal.IsMaximal.mem_pow_mul` for maximal ideal. -/
/-
**Ideal.IsPrime.mem_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [IsDedekindDomain R] (I : Ideal R) [h
I : I.IsPrime] {a b : R} {n : ℕ},   a * b ∈ I ^ n → a ∈ I ^ n ∨ b ∈ I
参数：I : Ideal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
· 使用定理 `Ideal.IsPrime.mul_mem_pow`：∀ {R : Type u_1} [inst : CommRing R] [IsDedek
indDomain R] (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ},   a * b ∈ I ^ n →
 a ∈ I ∨ b ∈ I …
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
See also `Ideal.IsMaximal.mem_pow_mul` for maximal ideal.
-/
theorem IsPrime.mem_pow_mul (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ}
    (h : a * b ∈ I ^ n) : a ∈ I ^ n ∨ b ∈ I := by
  rw [mul_comm] at h
  rw [or_comm]
  exact IsPrime.mul_mem_pow _ h

section

/-
**Ideal.count_normalizedFactors_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：count_normalizedFactors_eq {p x : Ideal R} [hp : p.IsPrime] {n : Nat} (hle
 : x <= p ^ n) (hlt : ¬x <= p ^ (n + 1)) : (normalizedFactors x).count p = n
参数：hle : x <= p ^ n；hlt : ¬x <= p ^ (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniqueFactorizationMonoid.count_normalizedFactors_eq'`：count_normalizedF
actors_eq' {p x : R} (hp : p = 0 ∨ Irreducible p) (hnorm : normalize p = p) {n :
 Nat} (hle : p ^ n ∣ x) (hlt : ¬p ^ (n + 1)…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.isPrime_iff_bot_or_prime`：isPrime_iff_bot_or_prime {P : Ideal A} :
 IsPrime P ↔ P = ⊥ ∨ Prime P
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Ideal.le_of_dvd`：∀ {R : Type u} [inst : CommSemiring R] {I J : Ideal R},
 I ∣ J → J ≤ I
-/
theorem count_normalizedFactors_eq {p x : Ideal R} [hp : p.IsPrime] {n : ℕ} (hle : x ≤ p ^ n)
    (hlt : ¬x ≤ p ^ (n + 1)) : (normalizedFactors x).count p = n :=
  count_normalizedFactors_eq' ((isPrime_iff_bot_or_prime.mp hp).imp_right Prime.irreducible)
    (normalize_eq _) (dvd_iff_le.mpr hle) (mt le_of_dvd hlt)

/-- The number of times an ideal `I` occurs as normalized factor of another ideal `J` is stable
when regarding these ideals as associated elements of the monoid of ideals. -/
/-
**Ideal.count_associates_factors_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：count_associates_factors_eq {I J : Ideal R} (hI : I != 0) (hJ : J.IsPrime)
 (hJ₀ : J != ⊥) : (Associates.mk J).count (Associates.mk I).factors = Multiset.c
ount J (normalizedFactors I)
参数：hI : I != 0；hJ : J.IsPrime；hJ₀ : J != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Associates.mk_ne_zero`：mk_ne_zero {a : M} : Associates.mk a != 0 ↔ a != 
0
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Ideal.prime_of_isPrime`：prime_of_isPrime {P : Ideal A} (hP : P != ⊥) (h 
: IsPrime P) : Prime P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.count_normalizedFactors_eq`：count_normalizedFactors_eq {p x : Idea
l R} [hp : p.IsPrime] {n : Nat} (hle : x <= p ^ n) (hlt : ¬x <= p ^ (n + 1)) : (
normalizedFactors x).c…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Associates.mk_dvd_mk`：mk_dvd_mk {a b : M} : Associates.mk a ∣ Associates
.mk b ↔ a ∣ b
· 使用定理 `Associates.mk_pow`：mk_pow (a : M) (n : Nat) : Associates.mk (a ^ n) = As
sociates.mk a ^ n
· 使用定理 `Associates.prime_pow_dvd_iff_le`：prime_pow_dvd_iff_le {m p : Associates 
α} (h₁ : m != 0) (h₂ : Irreducible p) {k : Nat} : p ^ k <= m ↔ k <= count p m.fa
ctors
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The number of times an ideal `I` occurs as normalized factor of another ideal `J
` is stable
when regarding these ideals as associated elements of the monoid of ideals.
-/
theorem count_associates_factors_eq
    {I J : Ideal R} (hI : I ≠ 0) (hJ : J.IsPrime) (hJ₀ : J ≠ ⊥) :
    (Associates.mk J).count (Associates.mk I).factors = Multiset.count J (normalizedFactors I) := by
  replace hI : Associates.mk I ≠ 0 := Associates.mk_ne_zero.mpr hI
  have hJ' : Irreducible (Associates.mk J) := by
    simpa only [Associates.irreducible_mk] using (prime_of_isPrime hJ₀ hJ).irreducible
  apply (count_normalizedFactors_eq (p := J) (x := I) _ _).symm
  all_goals
    rw [← dvd_iff_le, ← Associates.mk_dvd_mk, Associates.mk_pow]
    simp only [Associates.dvd_eq_le]
    rw [Associates.prime_pow_dvd_iff_le hI hJ']
  lia

@[deprecated (since := "2026-04-16")]
alias _root_.count_associates_factors_eq := count_associates_factors_eq

/-- Variant of `UniqueFactorizationMonoid.count_normalizedFactors_eq` for associated Ideals. -/
/-
**Ideal.count_associates_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：count_associates_eq {a a₀ x : R} {n : Nat} (hx : Prime x) (ha : ¬x ∣ a) (h
eq : a₀ = x ^ n * a) : (Associates.mk (span {x})).count (Associates.mk (span {a₀
})).factors = n
参数：hx : Prime x；ha : ¬x ∣ a；heq : a₀ = x ^ n * a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.count_associates_factors_eq`：count_associates_factors_eq {I J : Id
eal R} (hI : I != 0) (hJ : J.IsPrime) (hJ₀ : J != ⊥) : (Associates.mk J).count (
Associates.mk I).factor…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `UniqueFactorizationMonoid.count_normalizedFactors_eq`：count_normalizedFa
ctors_eq {p x : R} (hp : Irreducible p) (hnorm : normalize p = p) {n : Nat} (hle
 : p ^ n ∣ x) (hlt : ¬p ^ (n + 1) ∣ x) : (…
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Ideal.prime_span_singleton_iff`：prime_span_singleton_iff {a : A} : Prime
 (span {a}) ↔ Prime a
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.mem_span_singleton_self`：mem_span_singleton_self (x : α) : x in sp
an ({x} : Set α)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `mul_dvd_mul_iff_left`：mul_dvd_mul_iff_left [MonoidWithZero α] [IsLeftCan
celMulZero α] {a b c : α} (ha : a != 0) : a * b ∣ a * c ↔ b ∣ c
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Variant of `UniqueFactorizationMonoid.count_normalizedFactors_eq` for associated
 Ideals.
-/
theorem count_associates_eq
    {a a₀ x : R} {n : ℕ} (hx : Prime x) (ha : ¬x ∣ a) (heq : a₀ = x ^ n * a) :
    (Associates.mk (span {x})).count (Associates.mk (span {a₀})).factors = n := by
  have hx0 : x ≠ 0 := Prime.ne_zero hx
  rw [count_associates_factors_eq, UniqueFactorizationMonoid.count_normalizedFactors_eq]
  · exact (prime_span_singleton_iff.mpr hx).irreducible
  · exact normalize_eq _
  · simp only [span_singleton_pow, heq, dvd_span_singleton]
    exact mul_mem_right _ _ (mem_span_singleton_self (x ^ n))
  · simp only [span_singleton_pow, heq, dvd_span_singleton, mem_span_singleton]
    rw [pow_add, pow_one, mul_dvd_mul_iff_left (pow_ne_zero n hx0)]
    exact ha
  · simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot]
    aesop
  · exact (span_singleton_prime hx0).mpr hx
  · simp only [ne_eq, span_singleton_eq_bot]; exact hx0

/-- Variant of `UniqueFactorizationMonoid.count_normalizedFactors_eq` for associated Ideals. -/
/-
**Ideal.count_associates_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：count_associates_eq' {a x : R} (hx : Prime x) {n : Nat} (hle : x ^ n ∣ a) 
(hlt : ¬x ^ (n + 1) ∣ a) : (Associates.mk (span {x})).count (Associates.mk (span
 {a})).factors = n
参数：hx : Prime x；hle : x ^ n ∣ a；hlt : ¬x ^ (n + 1) ∣ a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.count_associates_eq`：count_associates_eq {a a₀ x : R} {n : Nat} (h
x : Prime x) (ha : ¬x ∣ a) (heq : a₀ = x ^ n * a) : (Associates.mk (span {x})).c
ount (Associate…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
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
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_one_cast_of_isNat`：∀ {R : Type u_1} [inst
 : CommSemiring R] (a : R) (b : ℕ), Mathlib.Meta.NormNum.IsNat b 1 → a ^ b = a

--- 原说明 ---
Variant of `UniqueFactorizationMonoid.count_normalizedFactors_eq` for associated
 Ideals.
-/
theorem count_associates_eq'
    {a x : R} (hx : Prime x) {n : ℕ} (hle : x ^ n ∣ a) (hlt : ¬x ^ (n + 1) ∣ a) :
    (Associates.mk (span {x})).count (Associates.mk (span {a})).factors = n := by
  obtain ⟨q, hq⟩ := hle
  apply count_associates_eq hx _ hq
  contrapose hlt with hdvd
  obtain ⟨q', hq'⟩ := hdvd
  use q'
  rw [hq, hq']
  ring

end

/-
**Ideal.le_mul_of_no_prime_factors** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：le_mul_of_no_prime_factors {I J K : Ideal R} (coprime : forall P, J <= P -
> K <= P -> ¬IsPrime P) (hJ : I <= J) (hK : I <= K) : I <= J * K
参数：coprime : forall P, J <= P -> K <= P -> ¬IsPrime P；hJ : I <= J；hK : I <= K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
· 使用定理 `UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors`：dvd_
of_dvd_mul_right_of_no_prime_factors {a b c : R} (ha : a != 0) (no_factors : for
all {d}, d ∣ a -> d ∣ b -> ¬Prime d) : a ∣ b * c -> a ∣ …
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem le_mul_of_no_prime_factors {I J K : Ideal R}
    (coprime : ∀ P, J ≤ P → K ≤ P → ¬IsPrime P) (hJ : I ≤ J) (hK : I ≤ K) : I ≤ J * K := by
  simp only [← dvd_iff_le] at coprime hJ hK ⊢
  by_cases hJ0 : J = 0
  · simpa only [hJ0, zero_mul] using hJ
  obtain ⟨I', rfl⟩ := hK
  rw [mul_comm]
  refine mul_dvd_mul_left K
    (UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors (b := K) hJ0 ?_ hJ)
  exact fun hPJ hPK => mt isPrime_of_prime (coprime _ hPJ hPK)

end Ideal

namespace IsDedekindDomain

/-- The intersection of distinct prime powers in a Dedekind domain is the product of these
prime powers.
See `IsDedekindDomain.inf_pow_eq_prod_of_prime` for the version in terms of `Ideal R`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.inf_pow_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {ι : Type u_4} [IsDedekindDomain R] (
s : Finset ι) (e : ι → ℕ)   (f : ι → IsDedekindDomain.HeightOneSpectrum R),   (∀
 i ∈ s, ∀ j ∈ s, i ≠ j → f i ≠ f j) → (s.inf fun i => (f i).asIdeal ^ e i) = ∏ i
 ∈ s, (f i).asIdeal ^ e i
参数：s : Finset ι；e : ι → ℕ；f : ι → IsDedekindDomain.HeightOneSpectrum R；∀ i ∈ s, 
∀ j ∈ s, i ≠ j → f i ≠ f j；s.inf fun i => (f i).asIdeal ^ e i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.prod_eq_iInf_of_pairwise_isCoprime`：prod_eq_iInf_of_pairwise_isCop
rime {s : Finset ι} {J : ι -> Ideal R} (hp : (s : Set ι).Pairwise (IsCoprime on 
J)) : ∏ i in s, J i = ⨅ i in s…
· 使用定理 `IsDedekindDomain.HeightOneSpectrum.isCoprime_pow_of_ne`：isCoprime_pow_of
_ne (P Q : HeightOneSpectrum R) (hPQ : P != Q) (n m : Nat) : IsCoprime (P.asIdea
l ^ n) (Q.asIdeal ^ m)
· 使用定理 `Finset.inf_eq_iInf`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] (s : Finset α) (f : α → β), s.inf f = ⨅ a ∈ s, f a

--- 原说明 ---
The intersection of distinct prime powers in a Dedekind domain is the product of
 these
prime powers.
See `IsDedekindDomain.inf_pow_eq_prod_of_prime` for the version in terms of `Ide
al R`.
-/
theorem HeightOneSpectrum.inf_pow_eq_prod (s : Finset ι) (e : ι → ℕ)
    (f : ι → HeightOneSpectrum R) (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → f i ≠ f j) :
    (s.inf fun i => (f i).asIdeal ^ e i) = ∏ i ∈ s, (f i).asIdeal ^ e i := by
  rw [prod_eq_iInf_of_pairwise_isCoprime]
  · rw [Finset.inf_eq_iInf s fun i ↦ (f i).asIdeal ^ e i]
  · intro i hi j hj hij
    exact HeightOneSpectrum.isCoprime_pow_of_ne _ _ (coprime i hi j hj hij) _ _

/-- The intersection of distinct prime powers in a Dedekind domain is the product of these
prime powers. -/
/-
**IsDedekindDomain.inf_pow_eq_prod_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekin
dDomain`。
形式化陈述：inf_pow_eq_prod_of_prime (s : Finset ι) (f : ι -> Ideal R) (e : ι -> Nat) 
(prime : forall i in s, Prime (f i)) (coprime : forallᵉ (i in s) (j in s), i != 
j -> f i != f j) : (s.inf fun i => f i ^ e i) = ∏ i in s, f i ^ e i
参数：s : Finset ι；f : ι -> Ideal R；e : ι -> Nat；prime : forall i in s, Prime (f i)
；coprime : forallᵉ (i in s) (j in s), i != j -> f i != f j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.prod_eq_iInf_of_pairwise_isCoprime`：prod_eq_iInf_of_pairwise_isCop
rime {s : Finset ι} {J : ι -> Ideal R} (hp : (s : Set ι).Pairwise (IsCoprime on 
J)) : ∏ i in s, J i = ⨅ i in s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isCoprime_iff_sup_eq`：isCoprime_iff_sup_eq : IsCoprime I J ↔ I ⊔ J
 = ⊤
· 使用定理 `Ideal.pow_sup_pow_eq_top`：pow_sup_pow_eq_top [I.IsTwoSided] {m n : Nat} 
(h : I ⊔ J = ⊤) : I ^ m ⊔ J ^ n = ⊤
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.coprime_of_ne`：∀ {α : Type u} [inst : Semiring α] {M M' 
: Ideal α}, M.IsMaximal → M'.IsMaximal → M ≠ M' → M ⊔ M' = ⊤
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `Finset.inf_eq_iInf`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] (s : Finset α) (f : α → β), s.inf f = ⨅ a ∈ s, f a

--- 原说明 ---
The intersection of distinct prime powers in a Dedekind domain is the product of
 these
prime powers.
-/
theorem inf_pow_eq_prod_of_prime (s : Finset ι) (f : ι → Ideal R)
    (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (f i)) (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → f i ≠ f j) :
    (s.inf fun i => f i ^ e i) = ∏ i ∈ s, f i ^ e i := by
  rw [prod_eq_iInf_of_pairwise_isCoprime, Finset.inf_eq_iInf s fun i ↦ (f i) ^ e i]
  intro i hi j hj hij
  exact Ideal.isCoprime_iff_sup_eq.mpr (pow_sup_pow_eq_top (IsMaximal.coprime_of_ne
    (IsPrime.isMaximal (isPrime_of_prime (prime i hi)) (prime i hi).ne_zero)
    (IsPrime.isMaximal (isPrime_of_prime (prime j hj)) (prime j hj).ne_zero)
    (coprime i hi j hj hij)))

@[deprecated (since := "2026-03-10")] alias inf_prime_pow_eq_prod :=
  inf_pow_eq_prod_of_prime

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i, P i ^ e i`, then `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`.
See `IsDedekindDomain.quotientEquivPiOfProdEq` for the version in terms of `Ideal R`. -/
/-
**IsDedekindDomain.HeightOneSpectrum.quotientEquivPiOfProdEq** 是 Mathlib 中的一个定义，
位于命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {ι : Type u_4} →       [IsDed
ekindDomain R] →         [inst_2 : Fintype ι] →           (I : Ideal R) →       
      (P : ι → IsDedekindDomain.HeightOneSpectrum R) →               (e : ι → ℕ)
 →                 (Pairwise fun i j => P i ≠ P j) →                   ∏ i, (P i
).asIdeal ^ e i = I → R ⧸ I ≃+* ((i : ι) → R ⧸ (P i).asIdeal ^ e i)
参数：I : Ideal R；P : ι → IsDedekindDomain.HeightOneSpectrum R；e : ι → ℕ；Pairwise f
un i j => P i ≠ P j；P i；(i : ι) → R ⧸ (P i).asIdeal ^ e i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
**Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i, P i ^ e i`, then `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`.
See `IsDedekindDomain.quotientEquivPiOfProdEq` for the version in terms of `Idea
l R`.
-/
def HeightOneSpectrum.quotientEquivPiOfProdEq [Fintype ι] (I : Ideal R)
    (P : ι → HeightOneSpectrum R) (e : ι → ℕ) (coprime : Pairwise fun i j => P i ≠ P j)
    (prod_eq : ∏ i, (P i).asIdeal ^ e i = I) : R ⧸ I ≃+* ∀ i, R ⧸ (P i).asIdeal ^ e i :=
  (Ideal.quotEquivOfEq
    (by simp [← prod_eq, Finset.inf_eq_iInf, Finset.mem_univ,
      ← HeightOneSpectrum.inf_pow_eq_prod _ _ _ (coprime.set_pairwise _)])).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun i j hij =>
      HeightOneSpectrum.isCoprime_pow_of_ne _ _ (coprime hij) _ _

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i, P i ^ e i`, then `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
/-
**IsDedekindDomain.quotientEquivPiOfProdEq** 是 Mathlib 中的一个定义，位于命名空间 `IsDedekind
Domain`。
形式化陈述：quotientEquivPiOfProdEq {ι : Type*} [Fintype ι] (I : Ideal R) (P : ι -> Id
eal R) (e : ι -> Nat) (prime : forall i, Prime (P i)) (coprime : Pairwise fun i 
j => P i != P j) (prod_eq : ∏ i, P i ^ e i = I) : R ⧸ I ≃+* forall i, R ⧸ P i ^ 
e i
参数：I : Ideal R；P : ι -> Ideal R；e : ι -> Nat；prime : forall i, Prime (P i)；copri
me : Pairwise fun i j => P i != P j；prod_eq : ∏ i, P i ^ e i = I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i, P i ^ e i`, then `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`.
-/
def quotientEquivPiOfProdEq {ι : Type*} [Fintype ι] (I : Ideal R) (P : ι → Ideal R)
    (e : ι → ℕ) (prime : ∀ i, Prime (P i)) (coprime : Pairwise fun i j => P i ≠ P j)
    (prod_eq : ∏ i, P i ^ e i = I) : R ⧸ I ≃+* ∀ i, R ⧸ P i ^ e i :=
  HeightOneSpectrum.quotientEquivPiOfProdEq I
    (fun i ↦ ⟨P i, (isPrime_of_prime (prime i)), (prime i).ne_zero⟩) e (by grind) prod_eq

/-- **Chinese remainder theorem** for a Dedekind domain: `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`,
where `P i` ranges over the prime factors of `I` and `e i` over the multiplicities. -/
/-
**IsDedekindDomain.quotientEquivPiFactors** 是 Mathlib 中的一个定义，位于命名空间 `IsDedekindD
omain`。
形式化陈述：quotientEquivPiFactors {I : Ideal R} (hI : I != ⊥) : R ⧸ I ≃+* forall P : 
(factors I).toFinset, R ⧸ (P : Ideal R) ^ (Multiset.count ↑P (factors I))
参数：hI : I != ⊥。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Chinese remainder theorem** for a Dedekind domain: `R ⧸ I` factors as `Π i, R 
⧸ (P i ^ e i)`,
where `P i` ranges over the prime factors of `I` and `e i` over the multipliciti
es.
-/
def quotientEquivPiFactors {I : Ideal R} (hI : I ≠ ⊥) :
    R ⧸ I ≃+* ∀ P : (factors I).toFinset, R ⧸ (P : Ideal R) ^ (Multiset.count ↑P (factors I)) :=
  quotientEquivPiOfProdEq _ _ _
    (fun P : (factors I).toFinset => prime_of_factor _ (Multiset.mem_toFinset.mp P.prop))
    (fun _ _ hij => Subtype.coe_injective.ne hij)
    (calc
      (∏ P : (factors I).toFinset, (P : Ideal R) ^ (factors I).count (P : Ideal R)) =
          ∏ P ∈ (factors I).toFinset, P ^ (factors I).count P :=
        (factors I).toFinset.prod_coe_sort fun P => P ^ (factors I).count P
      _ = ((factors I).map fun P => P).prod := (Finset.prod_multiset_map_count (factors I) id).symm
      _ = (factors I).prod := by rw [Multiset.map_id']
      _ = I := associated_iff_eq.mp (factors_prod hI))

@[simp]
/-
**IsDedekindDomain.quotientEquivPiFactors_mk** 是 Mathlib 中的一个定理，位于命名空间 `IsDedeki
ndDomain`。
形式化陈述：quotientEquivPiFactors_mk {I : Ideal R} (hI : I != ⊥) (x : R) : quotientEq
uivPiFactors hI (Ideal.Quotient.mk I x) = fun _P => Ideal.Quotient.mk _ x
参数：hI : I != ⊥；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem quotientEquivPiFactors_mk {I : Ideal R} (hI : I ≠ ⊥) (x : R) :
    quotientEquivPiFactors hI (Ideal.Quotient.mk I x) = fun _P =>
      Ideal.Quotient.mk _ x := rfl

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i ∈ s, P i ^ e i`, then `R ⧸ I` factors as `Π (i : s), R ⧸ (P i ^ e i)`.

This is a version of `IsDedekindDomain.quotientEquivPiOfProdEq` where we restrict
the product to a finite subset `s` of a potentially infinite indexing type `ι`.
-/
/-
**IsDedekindDomain.quotientEquivPiOfFinsetProdEq** 是 Mathlib 中的一个定义，位于命名空间 `IsDe
dekindDomain`。
形式化陈述：quotientEquivPiOfFinsetProdEq {ι : Type*} {s : Finset ι} (I : Ideal R) (P 
: ι -> Ideal R) (e : ι -> Nat) (prime : forall i in s, Prime (P i)) (coprime : f
orallᵉ (i in s) (j in s), i != j -> P i != P j) (prod_eq : ∏ i in s, P i ^ e i =
 I) : R ⧸ I ≃+* forall i : s, R ⧸ P i ^ e i
参数：I : Ideal R；P : ι -> Ideal R；e : ι -> Nat；prime : forall i in s, Prime (P i)；
coprime : forallᵉ (i in s) (j in s), i != j -> P i != P j；prod_eq : ∏ i in s, P 
i ^ e i = I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i ∈ s, P i ^ e i`, then `R ⧸ I` factors as `Π (i : s), R ⧸ (P i ^ e i)`.

This is a version of `IsDedekindDomain.quotientEquivPiOfProdEq` where we restric
t
the product to a finite subset `s` of a potentially infinite indexing type `ι`.
-/
def quotientEquivPiOfFinsetProdEq {ι : Type*} {s : Finset ι}
    (I : Ideal R) (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j)
    (prod_eq : ∏ i ∈ s, P i ^ e i = I) : R ⧸ I ≃+* ∀ i : s, R ⧸ P i ^ e i :=
  quotientEquivPiOfProdEq I (fun i : s => P i) (fun i : s => e i)
    (fun i => prime i i.2) (fun i j h => coprime i i.2 j j.2 (Subtype.coe_injective.ne h))
    (_root_.trans (Finset.prod_coe_sort s fun i => P i ^ e i) prod_eq)

/-- Corollary of the Chinese remainder theorem: given elements `x i : R / P i ^ e i`,
we can choose a representative `y : R` such that `y ≡ x i (mod P i ^ e i)`. -/
/-
**IsDedekindDomain.exists_representative_mod_finset** 是 Mathlib 中的一个定理，位于命名空间 `I
sDedekindDomain`。
形式化陈述：exists_representative_mod_finset {ι : Type*} {s : Finset ι} (P : ι -> Idea
l R) (e : ι -> Nat) (prime : forall i in s, Prime (P i)) (coprime : forallᵉ (i i
n s) (j in s), i != j -> P i != P j) (x : forall i : s, R ⧸ P i ^ e i) : exists 
y, forall (i) (hi : i in s), Ideal.Quotient.mk (P i ^ e i) y = x ⟨i, hi⟩
参数：P : ι -> Ideal R；e : ι -> Nat；prime : forall i in s, Prime (P i)；coprime : fo
rallᵉ (i in s) (j in s), i != j -> P i != P j；x : forall i : s, R ⧸ P i ^ e i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)

--- 原说明 ---
Corollary of the Chinese remainder theorem: given elements `x i : R / P i ^ e i`
,
we can choose a representative `y : R` such that `y ≡ x i (mod P i ^ e i)`.
-/
theorem exists_representative_mod_finset {ι : Type*} {s : Finset ι}
    (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j) (x : ∀ i : s, R ⧸ P i ^ e i) :
    ∃ y, ∀ (i) (hi : i ∈ s), Ideal.Quotient.mk (P i ^ e i) y = x ⟨i, hi⟩ := by
  let f := quotientEquivPiOfFinsetProdEq _ P e prime coprime rfl
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨z, fun i _hi => rfl⟩

/-- Corollary of the Chinese remainder theorem: given elements `x i : R`,
we can choose a representative `y : R` such that `y - x i ∈ P i ^ e i`. -/
/-
**IsDedekindDomain.exists_forall_sub_mem_ideal** 是 Mathlib 中的一个定理，位于命名空间 `IsDede
kindDomain`。
形式化陈述：exists_forall_sub_mem_ideal {ι : Type*} {s : Finset ι} (P : ι -> Ideal R) 
(e : ι -> Nat) (prime : forall i in s, Prime (P i)) (coprime : forallᵉ (i in s) 
(j in s), i != j -> P i != P j) (x : s -> R) : exists y, forall (i) (hi : i in s
), y - x ⟨i, hi⟩ in P i ^ e i
参数：P : ι -> Ideal R；e : ι -> Nat；prime : forall i in s, Prime (P i)；coprime : fo
rallᵉ (i in s) (j in s), i != j -> P i != P j；x : s -> R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsDedekindDomain.exists_representative_mod_finset`：exists_representative
_mod_finset {ι : Type*} {s : Finset ι} (P : ι -> Ideal R) (e : ι -> Nat) (prime 
: forall i in s, Prime (P i)) (coprime …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …

--- 原说明 ---
Corollary of the Chinese remainder theorem: given elements `x i : R`,
we can choose a representative `y : R` such that `y - x i ∈ P i ^ e i`.
-/
theorem exists_forall_sub_mem_ideal {ι : Type*} {s : Finset ι} (P : ι → Ideal R)
    (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j) (x : s → R) :
    ∃ y, ∀ (i) (hi : i ∈ s), y - x ⟨i, hi⟩ ∈ P i ^ e i := by
  obtain ⟨y, hy⟩ :=
    exists_representative_mod_finset P e prime coprime fun i =>
      Ideal.Quotient.mk _ (x i)
  exact ⟨y, fun i hi => Ideal.Quotient.eq.mp (hy i hi)⟩

end IsDedekindDomain

end DedekindDomain

end ChineseRemainder

section PID

open UniqueFactorizationMonoid Ideal

variable {R}
variable [IsDomain R] [IsPrincipalIdealRing R]

namespace Ideal

/-
**Ideal.span_singleton_dvd_span_singleton_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Ide
al`。
形式化陈述：span_singleton_dvd_span_singleton_iff_dvd {a b : R} : span {a} ∣ span ({b}
 : Set R) ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
-/
theorem span_singleton_dvd_span_singleton_iff_dvd {a b : R} :
    span {a} ∣ span ({b} : Set R) ↔ a ∣ b :=
  ⟨fun h => mem_span_singleton.mp (dvd_iff_le.mp h (mem_span_singleton.mpr (dvd_refl b))), fun h =>
    dvd_iff_le.mpr fun _d hd => mem_span_singleton.mpr (dvd_trans h (mem_span_singleton.mp hd))⟩

@[deprecated (since := "2026-04-16")]
alias _root_.span_singleton_dvd_span_singleton_iff_dvd := span_singleton_dvd_span_singleton_iff_dvd

@[simp]
/-
**Ideal.squarefree_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：squarefree_span_singleton {a : R} : Squarefree (span {a}) ↔ Squarefree a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_mul_span_singleton`：span_singleton_mul_span_singlet
on (r s : R) [(span {r}).IsTwoSided] : span {r} * span {s} = (span {r * s} : Ide
al R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.span_singleton_dvd_span_singleton_iff_dvd`：span_singleton_dvd_span
_singleton_iff_dvd {a b : R} : span {a} ∣ span ({b} : Set R) ↔ a ∣ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isUnit_iff`：isUnit_iff {I : Ideal R} : IsUnit I ↔ I = ⊤
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `Submodule.IsPrincipal.generator_mem`：generator_mem (S : Submodule R M) [
S.IsPrincipal] : generator S in S
· 使用定理 `Ideal.span_singleton_generator`：∀ {R : Type u} [inst : Semiring R] (I : 
Ideal R) [inst_1 : Submodule.IsPrincipal I],   Ideal.span {Submodule.IsPrincipal
.generator I} = I
-/
theorem squarefree_span_singleton {a : R} :
    Squarefree (span {a}) ↔ Squarefree a := by
  refine ⟨fun h x hx ↦ ?_, fun h I hI ↦ ?_⟩
  · rw [← span_singleton_dvd_span_singleton_iff_dvd, ← span_singleton_mul_span_singleton] at hx
    simpa using h _ hx
  · rw [← span_singleton_generator I, span_singleton_mul_span_singleton,
      span_singleton_dvd_span_singleton_iff_dvd] at hI
    exact isUnit_iff.mpr <| eq_top_of_isUnit_mem _ (Submodule.IsPrincipal.generator_mem I) (h _ hI)
/-
**Ideal.singleton_span_mem_normalizedFactors_of_mem_normalizedFactors** 是 Mathli
b 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：singleton_span_mem_normalizedFactors_of_mem_normalizedFactors [Normalizati
onMonoid R] {a b : R} (ha : a in normalizedFactors b) : span ({a} : Set R) in no
rmalizedFactors (span ({b} : Set R))
参数：ha : a in normalizedFactors b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_zero`：normalizedFactors_zero
 : normalizedFactors (0 : α) = 0
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
· 使用定理 `Ideal.prime_iff_isPrime`：prime_iff_isPrime {P : Ideal A} (hP : P != ⊥) :
 Prime P ↔ IsPrime P
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `UniqueFactorizationMonoid.prime_of_normalized_factor`：prime_of_normalize
d_factor {a : α} : forall x : α, x in normalizedFactors a -> Prime x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd`：exists_me
m_normalizedFactors_of_dvd {a p : α} (ha0 : a != 0) (hp : Irreducible p) : p ∣ a
 -> exists q in normalizedFactors a, p ~ᵤ q
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Ideal.span_singleton_le_span_singleton`：span_singleton_le_span_singleton
 {x y : α} : span ({x} : Set α) <= span ({y} : Set α) ↔ y ∣ x
· 使用定理 `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors`：dvd_of_mem_norma
lizedFactors {a p : α} (H : p in normalizedFactors a) : p ∣ a
· 使用定理 `associated_iff_eq`：associated_iff_eq {x y : M} : x ~ᵤ y ↔ x = y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem singleton_span_mem_normalizedFactors_of_mem_normalizedFactors [NormalizationMonoid R]
    {a b : R} (ha : a ∈ normalizedFactors b) :
    span ({a} : Set R) ∈ normalizedFactors (span ({b} : Set R)) := by
  by_cases hb : b = 0
  · rw [span_singleton_eq_bot.mpr hb, bot_eq_zero, normalizedFactors_zero]
    rw [hb, normalizedFactors_zero] at ha
    exact absurd ha (Multiset.notMem_zero a)
  · suffices Prime (span ({a} : Set R)) by
      obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd ?_ this.irreducible
          (dvd_iff_le.mpr (span_singleton_le_span_singleton.mpr (dvd_of_mem_normalizedFactors ha)))
      rwa [associated_iff_eq.mp hc']
    · by_contra h
      exact hb (span_singleton_eq_bot.mp h)
    rw [prime_iff_isPrime]
    · exact (span_singleton_prime (prime_of_normalized_factor a ha).ne_zero).mpr
        (prime_of_normalized_factor a ha)
    · by_contra h
      exact (prime_of_normalized_factor a ha).ne_zero (span_singleton_eq_bot.mp h)

@[deprecated (since := "2026-04-16")]
alias _root_.singleton_span_mem_normalizedFactors_of_mem_normalizedFactors :=
  singleton_span_mem_normalizedFactors_of_mem_normalizedFactors
/-
**Ideal.emultiplicity_eq_emultiplicity_span** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：emultiplicity_eq_emultiplicity_span {a b : R} : emultiplicity (span {a}) (
span ({b} : Set R)) = emultiplicity a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteMultiplicity.emultiplicity_eq_multiplicity`：FiniteMultiplicity.emu
ltiplicity_eq_multiplicity (h : FiniteMultiplicity a b) : emultiplicity a b = mu
ltiplicity a b
· 使用定理 `emultiplicity_eq_of_dvd_of_not_dvd`：emultiplicity_eq_of_dvd_of_not_dvd {
k : Nat} (hk : a ^ k ∣ b) (hsucc : ¬a ^ (k + 1) ∣ b) : emultiplicity a b = k
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.span_singleton_dvd_span_singleton_iff_dvd`：span_singleton_dvd_span
_singleton_iff_dvd {a b : R} : span {a} ∣ span ({b} : Set R) ↔ a ∣ b
· 使用定理 `pow_multiplicity_dvd`：pow_multiplicity_dvd (a b : α) : a ^ (multiplicity
 a b) ∣ b
· 使用定理 `FiniteMultiplicity.not_pow_dvd_of_multiplicity_lt`：FiniteMultiplicity.no
t_pow_dvd_of_multiplicity_lt (hf : FiniteMultiplicity a b) {m : Nat} (hm : multi
plicity a b < m) : ¬a ^ m ∣ b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FiniteMultiplicity.not_iff_forall`：FiniteMultiplicity.not_iff_forall : ¬
FiniteMultiplicity a b ↔ forall n : Nat, a ^ n ∣ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `emultiplicity_eq_top`：emultiplicity_eq_top : emultiplicity a b = ⊤ ↔ ¬Fi
niteMultiplicity a b
-/
theorem emultiplicity_eq_emultiplicity_span {a b : R} :
    emultiplicity (span {a}) (span ({b} : Set R)) = emultiplicity a b := by
  by_cases h : FiniteMultiplicity a b
  · rw [h.emultiplicity_eq_multiplicity]
    apply emultiplicity_eq_of_dvd_of_not_dvd <;>
      rw [span_singleton_pow, span_singleton_dvd_span_singleton_iff_dvd]
    · exact pow_multiplicity_dvd a b
    · apply h.not_pow_dvd_of_multiplicity_lt
      apply lt_add_one
  · suffices ¬FiniteMultiplicity (span ({a} : Set R)) (span ({b} : Set R)) by
      rw [emultiplicity_eq_top.2 h, emultiplicity_eq_top.2 this]
    exact FiniteMultiplicity.not_iff_forall.mpr fun n => by
      rw [span_singleton_pow, span_singleton_dvd_span_singleton_iff_dvd]
      exact FiniteMultiplicity.not_iff_forall.mp h n

@[deprecated (since := "2026-04-16")]
alias _root_.emultiplicity_eq_emultiplicity_span := emultiplicity_eq_emultiplicity_span

section NormalizationMonoid
variable [NormalizationMonoid R]

set_option backward.isDefEq.respectTransparency.types false in
/-- The bijection between the (normalized) prime factors of `r` and the (normalized) prime factors
of `span {r}` -/
/-
**Ideal.normalizedFactorsEquivSpanNormalizedFactors** 是 Mathlib 中的一个定义，位于命名空间 `I
deal`。
形式化陈述：normalizedFactorsEquivSpanNormalizedFactors {r : R} (hr : r != 0) : { d : 
R | d in normalizedFactors r } ≃ { I : Ideal R | I in normalizedFactors (span ({
r} : Set R)) }
参数：hr : r != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A

--- 原说明 ---
The bijection between the (normalized) prime factors of `r` and the (normalized)
 prime factors
of `span {r}`
-/
noncomputable def normalizedFactorsEquivSpanNormalizedFactors {r : R} (hr : r ≠ 0) :
    { d : R | d ∈ normalizedFactors r } ≃
      { I : Ideal R | I ∈ normalizedFactors (span ({r} : Set R)) } := by
  refine Equiv.ofBijective ?_ ?_
  · exact fun d =>
      ⟨span {↑d}, singleton_span_mem_normalizedFactors_of_mem_normalizedFactors d.prop⟩
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      rw [Subtype.mk_eq_mk, span_singleton_eq_span_singleton, Subtype.coe_mk,
          Subtype.coe_mk] at h
      exact Subtype.mk_eq_mk.mpr (mem_normalizedFactors_eq_of_associated ha hb h)
    · rintro ⟨i, hi⟩
      have : i.IsPrime := isPrime_of_prime (prime_of_normalized_factor i hi)
      have := exists_mem_normalizedFactors_of_dvd hr
        (Submodule.IsPrincipal.prime_generator_of_isPrime i
        (prime_of_normalized_factor i hi).ne_zero).irreducible ?_
      · obtain ⟨a, ha, ha'⟩ := this
        use ⟨a, ha⟩
        simp only [← span_singleton_eq_span_singleton.mpr ha',
            span_singleton_generator]
      · exact (Submodule.IsPrincipal.mem_iff_generator_dvd i).mp
          ((show span {r} ≤ i from dvd_iff_le.mp (dvd_of_mem_normalizedFactors hi))
            (mem_span_singleton.mpr (dvd_refl r)))

@[deprecated (since := "2026-04-16")]
alias _root_.normalizedFactorsEquivSpanNormalizedFactors :=
  normalizedFactorsEquivSpanNormalizedFactors

set_option backward.isDefEq.respectTransparency.types false in
/-- The bijection `normalizedFactorsEquivSpanNormalizedFactors` between the set of prime
factors of `r` and the set of prime factors of the ideal `⟨r⟩` preserves multiplicities. See
`count_normalizedFactorsSpan_eq_count` for the version stated in terms of multisets `count`. -/
/-
**Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplici
ty** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity
 {r d : R} (hr : r != 0) (hd : d in normalizedFactors r) : emultiplicity d r = e
multiplicity (normalizedFactorsEquivSpanNormalizedFactors hr ⟨d, hd⟩ : Ideal R) 
(span {r})
参数：hr : r != 0；hd : d in normalizedFactors r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.ofBijective_apply`：∀ {α : Sort u} {β : Sort v} (f : α → β) (hf : F
unction.Bijective f) (a : α), (Equiv.ofBijective f hf) a = f a
· 使用定理 `Ideal.emultiplicity_eq_emultiplicity_span`：emultiplicity_eq_emultiplicit
y_span {a b : R} : emultiplicity (span {a}) (span ({b} : Set R)) = emultiplicity
 a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The bijection `normalizedFactorsEquivSpanNormalizedFactors` between the set of p
rime
factors of `r` and the set of prime factors of the ideal `⟨r⟩` preserves multipl
icities. See
`count_normalizedFactorsSpan_eq_count` for the version stated in terms of multis
ets `count`.
-/
theorem emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity {r d : R}
    (hr : r ≠ 0) (hd : d ∈ normalizedFactors r) :
    emultiplicity d r =
      emultiplicity (normalizedFactorsEquivSpanNormalizedFactors hr ⟨d, hd⟩ : Ideal R)
        (span {r}) := by
  simp only [normalizedFactorsEquivSpanNormalizedFactors, emultiplicity_eq_emultiplicity_span,
    Subtype.coe_mk, Equiv.ofBijective_apply]

@[deprecated (since := "2026-04-16")]
alias _root_.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity :=
  emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity

/-- The bijection `normalized_factors_equiv_span_normalized_factors.symm` between the set of prime
factors of the ideal `⟨r⟩` and the set of prime factors of `r` preserves multiplicities. -/
/-
**Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emulti
plicity** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultipl
icity {r : R} (hr : r != 0) (I : { I : Ideal R | I in normalizedFactors (span ({
r} : Set R)) }) : emultiplicity ((normalizedFactorsEquivSpanNormalizedFactors hr
).symm I : R) r = emultiplicity (I : Ideal R) (span {r})
参数：hr : r != 0；I : { I : Ideal R | I in normalizedFactors (span ({r} : Set R)) }
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emult
iplicity`：emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultipli
city {r d : R} (hr : r != 0) (hd : d in normalizedFactors r) : emultip…

--- 原说明 ---
The bijection `normalized_factors_equiv_span_normalized_factors.symm` between th
e set of prime
factors of the ideal `⟨r⟩` and the set of prime factors of `r` preserves multipl
icities.
-/
theorem emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity {r : R}
    (hr : r ≠ 0) (I : { I : Ideal R | I ∈ normalizedFactors (span ({r} : Set R)) }) :
    emultiplicity ((normalizedFactorsEquivSpanNormalizedFactors hr).symm I : R) r =
      emultiplicity (I : Ideal R) (span {r}) := by
  obtain ⟨x, hx⟩ := (normalizedFactorsEquivSpanNormalizedFactors hr).surjective I
  obtain ⟨a, ha⟩ := x
  rw [hx.symm, Equiv.symm_apply_apply, Subtype.coe_mk,
    emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity hr ha]

@[deprecated (since := "2026-04-16")]
alias _root_.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity :=
  emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity

variable [DecidableEq R]

/-- The bijection between the set of prime factors of the ideal `⟨r⟩` and the set of prime factors
  of `r` preserves `count` of the corresponding multisets. See
  `multiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_multiplicity` for the version
  stated in terms of multiplicity. -/
/-
**Ideal.count_span_normalizedFactors_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：count_span_normalizedFactors_eq {r X : R} (hr : r != 0) (hX : Prime X) : M
ultiset.count (span {X} : Ideal R) (normalizedFactors (span {r})) = Multiset.cou
nt (normalize X) (normalizedFactors r)
参数：hr : r != 0；hX : Prime X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.emultiplicity_eq_emultiplicity_span`：emultiplicity_eq_emultiplicit
y_span {a b : R} : emultiplicity (span {a}) (span ({b} : Set R)) = emultiplicity
 a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `normUnit_eq_one`：normUnit_eq_one (x : α) : normUnit x = 1
· 使用定理 `normalize_apply`：normalize_apply (x : α) : normalize x = x * normUnit x
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The bijection between the set of prime factors of the ideal `⟨r⟩` and the set of
 prime factors
  of `r` preserves `count` of the corresponding multisets. See
  `multiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_multiplicity` for
 the version
  stated in terms of multiplicity.
-/
theorem count_span_normalizedFactors_eq {r X : R} (hr : r ≠ 0) (hX : Prime X) :
    Multiset.count (span {X} : Ideal R) (normalizedFactors (span {r})) =
        Multiset.count (normalize X) (normalizedFactors r) := by
  have := emultiplicity_eq_emultiplicity_span (R := R) (a := X) (b := r)
  rw [emultiplicity_eq_count_normalizedFactors (Prime.irreducible hX) hr,
    emultiplicity_eq_count_normalizedFactors (Prime.irreducible ?_), normalize_apply,
    normUnit_eq_one, Units.val_one, one_eq_top, mul_top, Nat.cast_inj] at this
  · simp only [normalize_apply, this]
  · simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, hr, not_false_eq_true]
  · simpa only [prime_span_singleton_iff]

@[deprecated (since := "2026-04-16")]
alias _root_.count_span_normalizedFactors_eq := count_span_normalizedFactors_eq
/-
**Ideal.count_span_normalizedFactors_eq_of_normUnit** 是 Mathlib 中的一个定理，位于命名空间 `I
deal`。
形式化陈述：count_span_normalizedFactors_eq_of_normUnit {r X : R} (hr : r != 0) (hX₁ :
 normUnit X = 1) (hX : Prime X) : Multiset.count (span {X} : Ideal R) (normalize
dFactors (span {r})) = Multiset.count X (normalizedFactors r)
参数：hr : r != 0；hX₁ : normUnit X = 1；hX : Prime X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ideal.count_span_normalizedFactors_eq`：count_span_normalizedFactors_eq {
r X : R} (hr : r != 0) (hX : Prime X) : Multiset.count (span {X} : Ideal R) (nor
malizedFactors (span {r})) …
-/
theorem count_span_normalizedFactors_eq_of_normUnit {r X : R}
    (hr : r ≠ 0) (hX₁ : normUnit X = 1) (hX : Prime X) :
      Multiset.count (span {X} : Ideal R) (normalizedFactors (span {r})) =
        Multiset.count X (normalizedFactors r) := by
  simpa [hX₁, normalize_apply] using count_span_normalizedFactors_eq hr hX

@[deprecated (since := "2026-04-16")]
alias _root_.count_span_normalizedFactors_eq_of_normUnit :=
  count_span_normalizedFactors_eq_of_normUnit

end NormalizationMonoid

end Ideal

end PID

section primesOverFinset

open UniqueFactorizationMonoid Ideal

variable {A : Type*} [CommRing A] {p : Ideal A} (hpb : p ≠ ⊥) [hpm : p.IsMaximal]
  (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B] [IsDomain A] [IsTorsionFree A B]

namespace IsDedekindDomain

variable (p) in
/-- The finite set of all prime factors of the pushforward of `p`. -/
/-
**IsDedekindDomain.primesOverFinset** 是 Mathlib 中的一个缩写定义，位于命名空间 `IsDedekindDomai
n`。
形式化陈述：primesOverFinset : Finset (Ideal B)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The finite set of all prime factors of the pushforward of `p`.
-/
noncomputable abbrev primesOverFinset : Finset (Ideal B) :=
  (factors (p.map (algebraMap A B))).toFinset

@[deprecated (since := "2026-04-16")] alias _root_.primesOverFinset := primesOverFinset

include hpb in
/-
**IsDedekindDomain.coe_primesOverFinset** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDom
ain`。
形式化陈述：coe_primesOverFinset : primesOverFinset p B = primesOver p B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `UniqueFactorizationMonoid.factors_eq_normalizedFactors`：factors_eq_norma
lizedFactors {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M] [S
ubsingleton Mˣ] (x : M) : factors x = normal…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Ideal.mem_primesOver_iff_mem_normalizedFactors`：mem_primesOver_iff_mem_n
ormalizedFactors {p : Ideal R} [h : p.IsMaximal] [Algebra R A] [IsDomain R] [IsT
orsionFree R A] (hp : p != ⊥) {P : I…
-/
theorem coe_primesOverFinset : primesOverFinset p B = primesOver p B := by
  ext
  simpa using (mem_primesOver_iff_mem_normalizedFactors _ hpb).symm

@[deprecated (since := "2026-04-16")] alias _root_.coe_primesOverFinset := coe_primesOverFinset

include hpb in
/-
**IsDedekindDomain.mem_primesOverFinset_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekin
dDomain`。
形式化陈述：mem_primesOverFinset_iff {P : Ideal B} : P in primesOverFinset p B ↔ P in 
primesOver p B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `IsDedekindDomain.coe_primesOverFinset`：coe_primesOverFinset : primesOver
Finset p B = primesOver p B
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_primesOverFinset_iff {P : Ideal B} : P ∈ primesOverFinset p B ↔ P ∈ primesOver p B := by
  rw [← Finset.mem_coe, coe_primesOverFinset hpb]

@[deprecated (since := "2026-04-16")]
alias _root_.mem_primesOverFinset_iff := mem_primesOverFinset_iff

end IsDedekindDomain

set_option linter.overlappingInstances false in
variable {R} (A) in
/-
**IsLocalRing.primesOverFinset_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalRing.primesOverFinset_eq [IsLocalRing A] [IsDedekindDomain A] [Alge
bra R A] [FaithfulSMul R A] [Module.Finite R A] {p : Ideal R} [p.IsMaximal] (hp0
 : p != ⊥) : IsDedekindDomain.primesOverFinset p A = {IsLocalRing.maximalIdeal A
}
参数：hp0 : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDomain.of_faithfulSMul`：IsDomain.of_faithfulSMul [IsDomain A] : IsDoma
in R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_eq_singleton`：coe_eq_singleton {s : Finset α} {a : α} : (s : 
Set α) = {a} ↔ s = {a}
· 使用定理 `IsDedekindDomain.coe_primesOverFinset`：coe_primesOverFinset : primesOver
Finset p B = primesOver p B
· 使用定理 `FaithfulSMul.to_isTorsionFree`：∀ (R : Type u_1) (A : Type u_3) [inst : C
ommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] [FaithfulSMul R A]  
 [Nontrivial R] [Is…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsLocalRing.primesOver_eq`：IsLocalRing.primesOver_eq [IsLocalRing A] [Is
DedekindDomain A] [Algebra R A] [FaithfulSMul R A] [Module.Finite R A] {p : Idea
l R} [p.IsMaxim…
-/
theorem IsLocalRing.primesOverFinset_eq [IsLocalRing A] [IsDedekindDomain A]
    [Algebra R A] [FaithfulSMul R A] [Module.Finite R A] {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    IsDedekindDomain.primesOverFinset p A = {IsLocalRing.maximalIdeal A} := by
  have : IsDomain R := .of_faithfulSMul R A
  rw [← Finset.coe_eq_singleton, IsDedekindDomain.coe_primesOverFinset hp0,
    IsLocalRing.primesOver_eq A hp0]

namespace IsDedekindDomain.HeightOneSpectrum

/--
The bijection between the elements of the height one prime spectrum of `B` that divide the lift
of the maximal ideal `p` in `B` and the primes over `p` in `B`.
-/
/-
**IsDedekindDomain.HeightOneSpectrum.equivPrimesOver** 是 Mathlib 中的一个定义，位于命名空间 `
IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：equivPrimesOver (hp : p != 0) : {v : HeightOneSpectrum B // v.asIdeal ∣ ma
p (algebraMap A B) p} ≃ p.primesOver B
参数：hp : p != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between the elements of the height one prime spectrum of `B` that 
divide the lift
of the maximal ideal `p` in `B` and the primes over `p` in `B`.
-/
noncomputable def equivPrimesOver (hp : p ≠ 0) :
    {v : HeightOneSpectrum B // v.asIdeal ∣ map (algebraMap A B) p} ≃ p.primesOver B :=
  Set.BijOn.equiv HeightOneSpectrum.asIdeal
    ⟨fun v hv ↦ ⟨v.isPrime, by rwa [liesOver_iff_dvd_map v.isPrime.ne_top]⟩,
    fun _ _ _ _ h ↦ HeightOneSpectrum.ext_iff.mpr h,
    fun Q hQ ↦ ⟨⟨Q, hQ.1, ne_bot_of_mem_primesOver hp hQ⟩,
      (liesOver_iff_dvd_map hQ.1.ne_top).mp hQ.2, rfl⟩⟩

@[simp]
/-
**IsDedekindDomain.HeightOneSpectrum.equivPrimesOver_apply** 是 Mathlib 中的一个定理，位于
命名空间 `IsDedekindDomain.HeightOneSpectrum`。
形式化陈述：equivPrimesOver_apply (hp : p != 0) (v : {v : HeightOneSpectrum B // v.asI
deal ∣ map (algebraMap A B) p}) : equivPrimesOver B hp v = v.1.asIdeal
参数：hp : p != 0；v : {v : HeightOneSpectrum B // v.asIdeal ∣ map (algebraMap A B) 
p}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
theorem equivPrimesOver_apply (hp : p ≠ 0)
    (v : {v : HeightOneSpectrum B // v.asIdeal ∣ map (algebraMap A B) p}) :
    equivPrimesOver B hp v = v.1.asIdeal := rfl

variable (A) in
/-- The pullback of a height one prime in `B` to `A`. -/
@[simps]
/-
**IsDedekindDomain.HeightOneSpectrum.under** 是 Mathlib 中的一个定义，位于命名空间 `IsDedekind
Domain.HeightOneSpectrum`。
形式化陈述：under {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsInteg
ral A B] (w : HeightOneSpectrum B) : HeightOneSpectrum A where asIdeal
参数：w : HeightOneSpectrum B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The pullback of a height one prime in `B` to `A`.
-/
def under {B : Type*} [CommRing B] [IsDomain B] [Algebra A B] [Algebra.IsIntegral A B]
    (w : HeightOneSpectrum B) : HeightOneSpectrum A where
  asIdeal := w.asIdeal.under A
  isPrime := .under A w.asIdeal
  ne_bot := mt Ideal.eq_bot_of_comap_eq_bot w.ne_bot

end IsDedekindDomain.HeightOneSpectrum

variable (p) [Algebra.IsIntegral A B]

namespace IsDedekindDomain

/-
**IsDedekindDomain.primesOver_finite** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDomain
`。
形式化陈述：primesOver_finite : (primesOver p B).Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.of_bot_isPrime`：IsDomain.of_bot_isPrime (A : Type*) [Ring A] [h
bp : (⊥ : Ideal A).IsPrime] : IsDomain A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `Ideal.primesOver_bot`：primesOver_bot [Module.IsTorsionFree A B] [IsDomai
n A] [IsDomain B] : primesOver (⊥ : Ideal A) B = {⊥}
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDedekindDomain.coe_primesOverFinset`：coe_primesOverFinset : primesOver
Finset p B = primesOver p B
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
-/
theorem primesOver_finite : (primesOver p B).Finite := by
  by_cases hpb : p = ⊥
  · rw [hpb] at hpm ⊢
    have : IsDomain A := IsDomain.of_bot_isPrime A
    rw [primesOver_bot A B]
    exact Set.finite_singleton ⊥
  · rw [← coe_primesOverFinset hpb B]
    exact (primesOverFinset p B).finite_toSet

@[deprecated (since := "2026-04-16")] alias _root_.primesOver_finite := primesOver_finite
/-
**IsDedekindDomain.** 是 Mathlib 中的一个实例，位于命名空间 `IsDedekindDomain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Fintype (p.primesOver B) := Set.Finite.fintype (primesOver_finite p B)
/-
**IsDedekindDomain.primesOver_ncard_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekin
dDomain`。
形式化陈述：primesOver_ncard_ne_zero : (primesOver p B).ncard != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_maximal_ideal_liesOver_of_isIntegral`：exists_maximal_ideal_
liesOver_of_isIntegral [Algebra.IsIntegral R S] [FaithfulSMul R S] (P : Ideal R)
 [P.IsMaximal] : exists (Q : Ideal S), …
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Set.ncard_ne_zero_of_mem`：ncard_ne_zero_of_mem {a : α} (h : a in s) (hs 
: s.Finite
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `IsDedekindDomain.primesOver_finite`：primesOver_finite : (primesOver p B)
.Finite
-/
theorem primesOver_ncard_ne_zero : (primesOver p B).ncard ≠ 0 := by
  rcases exists_maximal_ideal_liesOver_of_isIntegral (S := B) p with ⟨P, hPm, hp⟩
  exact Set.ncard_ne_zero_of_mem ⟨hPm.isPrime, hp⟩ (primesOver_finite p B)

@[deprecated (since := "2026-04-16")]
alias _root_.primesOver_ncard_ne_zero := primesOver_ncard_ne_zero
/-
**IsDedekindDomain.one_le_primesOver_ncard** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekind
Domain`。
形式化陈述：one_le_primesOver_ncard : 1 <= (primesOver p B).ncard
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `IsDedekindDomain.primesOver_ncard_ne_zero`：primesOver_ncard_ne_zero : (p
rimesOver p B).ncard != 0
-/
theorem one_le_primesOver_ncard : 1 ≤ (primesOver p B).ncard :=
  Nat.one_le_iff_ne_zero.mpr (primesOver_ncard_ne_zero p B)

@[deprecated (since := "2026-04-16")]
alias _root_.one_le_primesOver_ncard := one_le_primesOver_ncard

end IsDedekindDomain

end primesOverFinset

open IsDedekindDomain in
/-
**Algebra.IsIntegral.nontrivial_heightOneSpectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsIntegral.nontrivial_heightOneSpectrum [IsDomain A] [Algebra R A]
 [FaithfulSMul R A] [Algebra.IsIntegral R A] [Nontrivial (HeightOneSpectrum R)] 
: Nontrivial (HeightOneSpectrum A)
参数：HeightOneSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain`：exists_ideal_ov
er_prime_of_isIntegral_of_isDomain [Algebra.IsIntegral R S] (P : Ideal R) [IsPri
me P] (hP : RingHom.ker (algebraMap R S) <= P…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FaithfulSMul.ker_algebraMap_eq_bot`：FaithfulSMul.ker_algebraMap_eq_bot (
R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [FaithfulSMul R A] : Ri
ngHom.ker (algebraMap R …
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Ideal.under_bot`：under_bot : under A (⊥ : Ideal B) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Surjective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontriv
ial β] {f : α → β}, Function.Surjective f → Nontrivial α
-/
lemma Algebra.IsIntegral.nontrivial_heightOneSpectrum [IsDomain A] [Algebra R A]
    [FaithfulSMul R A] [Algebra.IsIntegral R A] [Nontrivial (HeightOneSpectrum R)] :
    Nontrivial (HeightOneSpectrum A) := by
  have := (FaithfulSMul.algebraMap_injective R A).isDomain
  let f (p : HeightOneSpectrum A) : HeightOneSpectrum R := p.under R
  have : Function.Surjective f := fun ⟨p, _, hp⟩ ↦ by
    obtain ⟨P, hP, rfl⟩ := p.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := A) (by simp)
    exact ⟨⟨P, hP, by aesop⟩, rfl⟩
  exact this.nontrivial
