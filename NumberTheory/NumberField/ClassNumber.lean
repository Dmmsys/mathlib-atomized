/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
public import Mathlib.NumberTheory.ClassNumber.Finite
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Class numbers of number fields

This file defines the class number of a number field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
We denote by `M K` the Minkowski bound of a number field `K`, defined as
`(4 / π) ^ nrComplexPlaces K * ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)`.
- `NumberField.classNumber`: the class number of a number field is the (finite)
  cardinality of the class group of its ring of integers
- `isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`: let `K`
  be a number field. To show that `𝓞 K` is a PID it is enough to show that, for all (natural) primes
  `p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, all ideals `P` above `p` such that
  `p ^ (span ({p}).inertiaDeg P) ≤ ⌊(M K)⌋₊` are principal. This is the standard technique to prove
  that `𝓞 K` is principal, see [marcus1977number], discussion after Theorem 37.
  The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to use `fin_cases`
  to deal with the finite number of primes `p` in the interval.
- `isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`: let `K`
  be a number field such that `K/ℚ` is Galois. To show that `𝓞 K` is a PID it is enough to show
  that, for all (natural) primes `p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, there is an ideal `P` above `p` such
  that either `⌊(M K)⌋₊ < p ^ (span ({p}).inertiaDeg P)` or `P` is principal. This is the standard
  technique to prove that `𝓞 K` is principal in the Galois case, see [marcus1977number], discussion
  after Theorem 37.
  The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to use `fin_cases`
  to deal with the finite number of primes `p` in the interval.
-/

@[expose] public section

open scoped nonZeroDivisors Real

open Module NumberField InfinitePlace Ideal Nat

variable (K : Type*) [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

namespace NumberField

namespace RingOfIntegers

/-
**NumberField.RingOfIntegers.instFintypeClassGroup** 是 Mathlib 中的一个实例，位于命名空间 `Nu
mberField.RingOfIntegers`。
形式化陈述：instFintypeClassGroup : Fintype (ClassGroup (𝓞 K))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralClosureInt`：∀ {K : Type u_1} [i
nst : Field K], IsIntegralClosure (NumberField.RingOfIntegers K) ℤ K
-/
noncomputable instance instFintypeClassGroup : Fintype (ClassGroup (𝓞 K)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite ℚ K AbsoluteValue.absIsAdmissible

end RingOfIntegers

/-- The class number of a number field is the (finite) cardinality of the class group. -/
/-
**NumberField.classNumber** 是 Mathlib 中的一个定义，位于命名空间 `NumberField`。
形式化陈述：classNumber : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)

--- 原说明 ---
The class number of a number field is the (finite) cardinality of the class grou
p.
-/
noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (𝓞 K))
/-
**NumberField.classNumber_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：classNumber_ne_zero : classNumber K != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem classNumber_ne_zero : classNumber K ≠ 0 := Fintype.card_ne_zero
/-
**NumberField.classNumber_pos** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：classNumber_pos : 0 < classNumber K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem classNumber_pos : 0 < classNumber K := Fintype.card_pos

variable {K}

/-- The class number of a number field is `1` iff the ring of integers is a PID. -/
/-
**NumberField.classNumber_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `NumberField`。
形式化陈述：classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `card_classGroup_eq_one_iff`：card_classGroup_eq_one_iff [IsDedekindDomain
 R] [Fintype (ClassGroup R)] : Fintype.card (ClassGroup R) = 1 ↔ IsPrincipalIdea
lRing R
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)

--- 原说明 ---
The class number of a number field is `1` iff the ring of integers is a PID.
-/
theorem classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K) :=
  card_classGroup_eq_one_iff
/-
**NumberField.exists_ideal_in_class_of_norm_le** 是 Mathlib 中的一个定理，位于命名空间 `Number
Field`。
形式化陈述：exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) : exists I : (Idea
l (𝓞 K))⁰, ClassGroup.mk0 I = C ∧ absNorm (I : Ideal (𝓞 K)) <= M K
参数：C : ClassGroup (𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `ClassGroup.mk0_surjective`：ClassGroup.mk0_surjective [IsDedekindDomain R
] : Function.Surjective (ClassGroup.mk0 : (Ideal R)⁰ -> ClassGroup R)
· 使用定理 `NumberField.RingOfIntegers.instIsFractionRing`：∀ {K : Type u_1} [inst : 
Field K] [NumberField K], IsFractionRing (NumberField.RingOfIntegers K) K
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr`：exists_n
e_zero_mem_ideal_of_norm_le_mul_sqrt_discr (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : e
xists a in (I : FractionalIdeal (𝓞 K)⁰ K), a != 0 ∧ …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.dvd_iff_le`：Ideal.dvd_iff_le {I J : Ideal A} : I ∣ J ↔ J <= I
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.linearMap_apply`：linearMap_apply (r : R) : Algebra.linearMap R A
 r = algebraMap R A r
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `Submodule.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] {A : Ty
pe v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTow
er R A A] [NoZeroD…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `NumberField.instNontrivialRingOfIntegers`：∀ (K : Type u_1) [inst : Field
 K], Nontrivial (NumberField.RingOfIntegers K)
· 使用定理 `ClassGroup.mk0_eq_mk0_inv_iff`：ClassGroup.mk0_eq_mk0_inv_iff [IsDedekind
Domain R] {I J : (Ideal R)⁰} : ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ ↔ exists 
x != (0 : R), I * J…
（共 58 条，此处仅展示前 30 条）
-/
theorem exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      absNorm (I : Ideal (𝓞 K)) ≤ M K := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  obtain ⟨_, ⟨a, ha, rfl⟩, h_nz, h_nm⟩ :=
    exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K (FractionalIdeal.mk0 K J)
  obtain ⟨I₀, hI⟩ := dvd_iff_le.mpr ((span_singleton_le_iff_mem J).mpr (by exact ha))
  have : I₀ ≠ 0 := by
    contrapose h_nz
    rw [h_nz, mul_zero, zero_eq_bot, span_singleton_eq_bot] at hI
    rw [Algebra.linearMap_apply, hI, map_zero]
  let I := (⟨I₀, mem_nonZeroDivisors_iff_ne_zero.mpr this⟩ : (Ideal (𝓞 K))⁰)
  refine ⟨I, ?_, ?_⟩
  · suffices ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ by rw [this, hJ, inv_inv]
    exact ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨a, Subtype.coe_ne_coe.1 h_nz, by rw [mul_comm, hI]⟩
  · rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), Algebra.linearMap_apply,
      ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_absNorm, hI, map_mul,
      cast_mul, Rat.cast_mul, absNorm_apply, Rat.cast_natCast, Rat.cast_natCast,
      FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, mul_div_assoc,
      mul_assoc, mul_assoc] at h_nm
    refine le_of_mul_le_mul_of_pos_left h_nm ?_
    exact cast_pos.mpr <| pos_of_ne_zero <| absNorm_ne_zero_of_nonZeroDivisors J

end NumberField

namespace RingOfIntegers

variable {K}

open scoped NumberField

/-
**RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le** 是 Mathlib 中的一个
定理，位于命名空间 `RingOfIntegers`。
形式化陈述：isPrincipalIdealRing_of_isPrincipal_of_norm_le (h : forall ⦃I : (Ideal (𝓞 
K))⁰⦄, absNorm (I : Ideal (𝓞 K)) <= M K -> Submodule.IsPrincipal (I : Ideal (𝓞 K
))) : IsPrincipalIdealRing (𝓞 K)
参数：h : forall ⦃I : (Ideal (𝓞 K))⁰⦄, absNorm (I : Ideal (𝓞 K)) <= M K -> Submodul
e.IsPrincipal (I : Ideal (𝓞 K))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.classNumber_eq_one_iff`：classNumber_eq_one_iff : classNumber
 K = 1 ↔ IsPrincipalIdealRing (𝓞 K)
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.classNumber.eq_1`：∀ (K : Type u_1) [inst : Field K] [inst_1 
: NumberField K],   NumberField.classNumber K = Fintype.card (ClassGroup (Number
Field.RingOfIntege…
· 使用定理 `Fintype.card_eq_one_iff`：card_eq_one_iff : card α = 1 ↔ exists x : α, fo
rall y, y = x
· 使用定理 `NumberField.exists_ideal_in_class_of_norm_le`：exists_ideal_in_class_of_n
orm_le (C : ClassGroup (𝓞 K)) : exists I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C 
∧ absNorm (I : Ideal (𝓞 K)) <= M K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
-/
theorem isPrincipalIdealRing_of_isPrincipal_of_norm_le
    (h : ∀ ⦃I : (Ideal (𝓞 K))⁰⦄, absNorm (I : Ideal (𝓞 K)) ≤ M K →
      Submodule.IsPrincipal (I : Ideal (𝓞 K))) : IsPrincipalIdealRing (𝓞 K) := by
  rw [← classNumber_eq_one_iff, classNumber, Fintype.card_eq_one_iff]
  refine ⟨1, fun C ↦ ?_⟩
  obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C
  simpa [← ClassGroup.mk0_eq_one_iff] using h hI
/-
**RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime** 是 M
athlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime (h : forall ⦃I :
 (Ideal (𝓞 K))⁰⦄, (I : Ideal (𝓞 K)).IsPrime -> absNorm (I : Ideal (𝓞 K)) <= M K 
-> Submodule.IsPrincipal (I : Ideal (𝓞 K))) : IsPrincipalIdealRing (𝓞 K)
参数：h : forall ⦃I : (Ideal (𝓞 K))⁰⦄, (I : Ideal (𝓞 K)).IsPrime -> absNorm (I : Id
eal (𝓞 K)) <= M K -> Submodule.IsPrincipal (I : Ideal (𝓞 K))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le`：isPrincip
alIdealRing_of_isPrincipal_of_norm_le (h : forall ⦃I : (Ideal (𝓞 K))⁰⦄, absNorm 
(I : Ideal (𝓞 K)) <= M K -> Submodule.IsPrincipal (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_isPrincipalSubmonoid_iff`：mem_isPrincipalSubmonoid_iff {I : Id
eal R} : I in isPrincipalSubmonoid R ↔ IsPrincipal I
· 使用定理 `Ideal.prod_normalizedFactors_eq_self`：prod_normalizedFactors_eq_self (hI
 : I != ⊥) : (normalizedFactors I).prod = I
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `NumberField.instNontrivialRingOfIntegers`：∀ (K : Type u_1) [inst : Field
 K], Nontrivial (NumberField.RingOfIntegers K)
· 使用定理 `Submonoid.multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] (S : S
ubmonoid M) (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `Submodule.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] {A : Ty
pe v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : IsScalarTow
er R A A] [NoZeroD…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.mem_normalizedFactors_iff`：∀ {A : Type u_2} [inst : CommRing A] [i
nst_1 : IsDedekindDomain A] {p I : Ideal A},   I ≠ ⊥ → (p ∈ UniqueFactorizationM
onoid.normalizedFacto…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Ideal.absNorm_pos_of_nonZeroDivisors`：absNorm_pos_of_nonZeroDivisors (I 
: (Ideal S)⁰) : 0 < absNorm (I : Ideal S)
（共 35 条，此处仅展示前 30 条）
-/
theorem isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    (h : ∀ ⦃I : (Ideal (𝓞 K))⁰⦄, (I : Ideal (𝓞 K)).IsPrime →
      absNorm (I : Ideal (𝓞 K)) ≤ M K → Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI ↦ ?_)
  rw [← mem_isPrincipalSubmonoid_iff,
    ← Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)]
  refine Submonoid.multiset_prod_mem _ _ (fun J hJ ↦ mem_isPrincipalSubmonoid_iff.mp ?_)
  by_cases hJ0 : J = 0
  · simpa [hJ0] using! bot_isPrincipal
  rw [← Subtype.coe_mk J (mem_nonZeroDivisors_of_ne_zero hJ0)]
  refine h (((mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I)).mp hJ).1) ?_
  exact (cast_le.mpr <| le_of_dvd (absNorm_pos_of_nonZeroDivisors I) <|
    absNorm_dvd_absNorm_of_le <| le_of_dvd <|
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hJ).trans hI

set_option linter.style.longLine false in
/-- Let `K` be a number field and let `M K` be the Minkowski bound of `K`.
To show that `𝓞 K` is a PID it is enough to show that, for all (natural) primes
`p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, all ideals `P` above `p` such that
`p ^ (span ({p}).inertiaDeg P) ≤ ⌊(M K)⌋₊` are principal. This is the standard technique to prove
that `𝓞 K` is principal, see [marcus1977number], discussion after Theorem 37.
If `K/ℚ` is Galois, one can use the more convenient
`RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`
below.

The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to use `fin_cases`
to deal with the finite number of primes `p` in the interval. -/
/-
**RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver
_of_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
 (h : forall p in Finset.Icc 1 ⌊(M K)⌋₊, p.Prime -> forall (P : Ideal (𝓞 K)), P 
in primesOver (span {(p : Int)}) (𝓞 K) -> p ^ P.inertiaDeg Int <= ⌊(M K)⌋₊ -> Su
bmodule.IsPrincipal P) : IsPrincipalIdealRing (𝓞 K)
参数：h : forall p in Finset.Icc 1 ⌊(M K)⌋₊, p.Prime -> forall (P : Ideal (𝓞 K)), P
 in primesOver (span {(p : Int)}) (𝓞 K) -> p ^ P.inertiaDeg Int <= ⌊(M K)⌋₊ -> S
ubmodule.IsPrincipal P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
`：isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime (h : forall ⦃I : (Id
eal (𝓞 K))⁰⦄, (I : Ideal (𝓞 K)).IsPrime -> absNorm (I : Ideal …
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `nonZeroDivisors.coe_ne_zero`：nonZeroDivisors.coe_ne_zero (x : M₀⁰) : (x 
: M₀) != 0
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `NumberField.instNontrivialRingOfIntegers`：∀ (K : Type u_1) [inst : Field
 K], Nontrivial (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.eq_bot_of_comap_eq_bot`：eq_bot_of_comap_eq_bot [Nontrivial R] [IsD
omain S] [Algebra.IsIntegral R S] (hI : I.comap (algebraMap R S) = ⊥) : I = ⊥
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instIsIntegralInt`：∀ {K : Type u_1} [inst : F
ield K], Algebra.IsIntegral ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `abs_choice`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α
] (x : α), |x| = x ∨ |x| = -x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Ideal.span_singleton_neg`：span_singleton_neg : span {-x} = span {x}
· 使用定理 `Nat.le_floor`：le_floor (h : (n : α) <= a) : n <= ⌊a⌋₊
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `coe_nonZeroDivisorsRight_eq`：∀ (M₀ : Type u_1) [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀] [Nontrivial M₀],   ↑(nonZeroDivisorsRight M₀) = {x | x ≠ 0
}
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K` be a number field and let `M K` be the Minkowski bound of `K`.
To show that `𝓞 K` is a PID it is enough to show that, for all (natural) primes
`p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, all ideals `P` above `p` such that
`p ^ (span ({p}).inertiaDeg P) ≤ ⌊(M K)⌋₊` are principal. This is the standard t
echnique to prove
that `𝓞 K` is principal, see [marcus1977number], discussion after Theorem 37.
If `K/ℚ` is Galois, one can use the more convenient
`RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_
primesOver_of_mem_Icc`
below.

The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to u
se `fin_cases`
to deal with the finite number of primes `p` in the interval.
-/
theorem isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, p.Prime → ∀ (P : Ideal (𝓞 K)),
      P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) → p ^ P.inertiaDeg ℤ ≤ ⌊(M K)⌋₊ →
      Submodule.IsPrincipal P) : IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime <|
    fun ⟨P, HP⟩ hP hPN ↦ ?_
  obtain ⟨p, hp⟩ := IsPrincipalIdealRing.principal <| under ℤ P
  have hp0 : p ≠ 0 := fun h ↦ nonZeroDivisors.coe_ne_zero ⟨P, HP⟩ <|
    eq_bot_of_comap_eq_bot (R := ℤ) <| by simpa only [hp, submodule_span_eq, span_singleton_eq_bot]
  have hpprime := (span_singleton_prime hp0).mp
  simp only [← submodule_span_eq, ← hp] at hpprime
  have hlies : P.LiesOver (span {p}) := by
    rcases abs_choice p with h | h <;>
    simpa [h, span_singleton_neg p, ← submodule_span_eq, ← hp] using over_under P
  have hspan : span {↑p.natAbs} = span {p} := by
    rcases abs_choice p with h | h <;> simp [h]
  have hple : p.natAbs ^ P.inertiaDeg ℤ ≤ ⌊(M K)⌋₊ := by
    refine le_floor ?_
    have : P.IsMaximal := hP.isMaximal (by simpa using HP.2)
    have : (span {p}).IsMaximal := (hpprime (.under ℤ P)).isMaximal_span_singleton
    simpa only [hspan, ← cast_pow, ← natAbs_pow_inertiaDeg p P] using hPN
  have hpabsprime := Int.prime_iff_natAbs_prime.mp (hpprime (hP.under _))
  refine h _ ?_ hpabsprime _ ⟨hP, ?_⟩ hple
  · suffices 0 < P.inertiaDeg ℤ by
      exact Finset.mem_Icc.mpr ⟨hpabsprime.one_le, le_trans (le_pow this) hple⟩
    have := (isPrime_of_prime (prime_span_singleton_iff.mpr <|
      hpprime (hP.under _))).isMaximal <| by simp [((hpprime (hP.under _))).ne_zero]
    exact inertiaDeg_pos ..
  · exact hspan ▸ hlies

/-- Let `K` be a number field such that `K/ℚ` is Galois and let `M K` be the Minkowski bound of `K`.
To show that `𝓞 K` is a PID it is enough to show that, for all (natural) primes
`p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, there is an ideal `P` above `p` such that
either `⌊(M K)⌋₊ < p ^ (span ({p}).inertiaDeg P)` or `P` is principal. This is the standard
technique to prove that `𝓞 K` is principal in the Galois case, see [marcus1977number], discussion
after Theorem 37.

The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to use `fin_cases`
to deal with the finite number of primes `p` in the interval. -/
/-
**RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem
_primesOver_of_mem_Icc** 是 Mathlib 中的一个定理，位于命名空间 `RingOfIntegers`。
形式化陈述：isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver
_of_mem_Icc [IsGalois Rat K] (h : forall p in Finset.Icc 1 ⌊(M K)⌋₊, p.Prime -> 
exists P in primesOver (span {(p : Int)}) (𝓞 K), ⌊(M K)⌋₊ < p ^ P.inertiaDeg Int
 ∨ Submodule.IsPrincipal P) : IsPrincipalIdealRing (𝓞 K)
参数：h : forall p in Finset.Icc 1 ⌊(M K)⌋₊, p.Prime -> exists P in primesOver (spa
n {(p : Int)}) (𝓞 K), ⌊(M K)⌋₊ < p ^ P.inertiaDeg Int ∨ Submodule.IsPrincipal P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_prim
esOver_of_mem_Icc`：isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOv
er_of_mem_Icc (h : forall p in Finset.Icc 1 ⌊(M K)⌋₊, p.Prime -> forall (P : Id…
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.prime_span_singleton_iff`：prime_span_singleton_iff {a : A} : Prime
 (span {a}) ↔ Prime a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.prime_iff_prime_int`：prime_iff_prime_int {p : Nat} : p.Prime ↔ _root
_.Prime (p : Int)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 78 条，此处仅展示前 30 条）

--- 原说明 ---
Let `K` be a number field such that `K/ℚ` is Galois and let `M K` be the Minkows
ki bound of `K`.
To show that `𝓞 K` is a PID it is enough to show that, for all (natural) primes
`p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, there is an ideal `P` above `p` such that
either `⌊(M K)⌋₊ < p ^ (span ({p}).inertiaDeg P)` or `P` is principal. This is t
he standard
technique to prove that `𝓞 K` is principal in the Galois case, see [marcus1977nu
mber], discussion
after Theorem 37.

The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to u
se `fin_cases`
to deal with the finite number of primes `p` in the interval.
-/
theorem isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    [IsGalois ℚ K] (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, p.Prime →
      ∃ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K),
        ⌊(M K)⌋₊ < p ^ P.inertiaDeg ℤ ∨
          Submodule.IsPrincipal P) :
      IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hpmem hp P ⟨hP1, hP2⟩ hple ↦ ?_)
  obtain ⟨Q, ⟨hQ1, hQ2⟩, H⟩ := h p hpmem hp
  have := (isPrime_of_prime (prime_span_singleton_iff.mpr (prime_iff_prime_int.mp hp))).isMaximal
    (by simp [hp.ne_zero])
  by_cases h : ⌊(M K)⌋₊ < p ^ P.inertiaDeg ℤ
  · linarith
  rw [inertiaDeg_eq_of_isGaloisGroup (span {↑p}) Q P (K ≃ₐ[ℚ] K)] at H
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup (span ({↑p} : Set ℤ)) Q P (K ≃ₐ[ℚ] K)
  exact (H.resolve_left h).map_ringHom (MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ)
/-
**RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt** 是 Mathlib 中的一个定理，位于命名空间 
`RingOfIntegers`。
形式化陈述：isPrincipalIdealRing_of_abs_discr_lt (h : |discr K| < (2 * (π / 4) ^ nrCom
plexPlaces K * ((finrank Rat K) ^ (finrank Rat K) / (finrank Rat K)!)) ^ 2) : Is
PrincipalIdealRing (𝓞 K)
参数：h : |discr K| < (2 * (π / 4) ^ nrComplexPlaces K * ((finrank Rat K) ^ (finran
k Rat K) / (finrank Rat K)!)) ^ 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.to_finiteDimensional`：∀ {K : Type u_1} {inst : Field K} [sel
f : NumberField K], FiniteDimensional ℚ K
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `Algebra.IsSeparable.of_integral`：∀ (F : Type u_1) [inst : Field F] (K : 
Type u_2) [inst_1 : Ring K] [inst_2 : Algebra F K] [IsDomain K]   [Algebra.IsInt
egral F K] [CharZero …
· 使用定理 `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le`：isPrincip
alIdealRing_of_isPrincipal_of_norm_le (h : forall ⦃I : (Ideal (𝓞 K))⁰⦄, absNorm 
(I : Ideal (𝓞 K)) <= M K -> Submodule.IsPrincipal (…
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.absNorm_eq_one_iff`：absNorm_eq_one_iff {I : Ideal S} : absNorm I =
 1 ↔ I = ⊤
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
（共 61 条，此处仅展示前 30 条）
-/
theorem isPrincipalIdealRing_of_abs_discr_lt
    (h : |discr K| < (2 * (π / 4) ^ nrComplexPlaces K *
      ((finrank ℚ K) ^ (finrank ℚ K) / (finrank ℚ K)!)) ^ 2) :
    IsPrincipalIdealRing (𝓞 K) := by
  have : 0 < finrank ℚ K := finrank_pos -- Lean needs to know this for `positivity` to succeed
  rw [← Real.sqrt_lt (by positivity) (by positivity), mul_assoc, ← inv_mul_lt_iff₀' (by positivity),
    mul_inv, ← inv_pow, inv_div, inv_div, mul_assoc, Int.cast_abs] at h
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI ↦ ?_)
  rw [absNorm_eq_one_iff.mp <| le_antisymm (Nat.lt_succ_iff.mp (cast_lt.mp
    (lt_of_le_of_lt hI h))) <| one_le_iff_ne_zero.mpr (absNorm_ne_zero_of_nonZeroDivisors I)]
  exact top_isPrincipal

end RingOfIntegers

namespace Rat

open NumberField

/-
**Rat.classNumber_eq** 是 Mathlib 中的一个定理，位于命名空间 `Rat`。
形式化陈述：classNumber_eq : NumberField.classNumber Rat = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `NumberField.classNumber_eq_one_iff`：classNumber_eq_one_iff : classNumber
 K = 1 ↔ IsPrincipalIdealRing (𝓞 K)
· 使用定理 `IsPrincipalIdealRing.of_surjective`：IsPrincipalIdealRing.of_surjective [
IsPrincipalIdealRing R] (f : F) (hf : Function.Surjective f) : IsPrincipalIdealR
ing S
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `RingEquiv.surjective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [in
st_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Surjec
tive ⇑e
-/
theorem classNumber_eq : NumberField.classNumber ℚ = 1 :=
  classNumber_eq_one_iff.mpr <| IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective

end Rat

