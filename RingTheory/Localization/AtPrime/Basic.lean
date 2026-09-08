/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# Localizations of commutative rings at the complement of a prime ideal

## Main definitions

* `IsLocalization.AtPrime (P : Ideal R) [IsPrime P] (S : Type*)` expresses that `S` is a
  localization at (the complement of) a prime ideal `P`, as an abbreviation of
  `IsLocalization P.prime_compl S`

## Main results

* `IsLocalization.AtPrime.isLocalRing`: a theorem (not an instance) stating a localization at the
  complement of a prime ideal is a local ring

## Implementation notes

See `RingTheory.Localization.Basic` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

@[expose] public section

open Module

variable {R : Type*} [CommSemiring R] (S : Type*) [CommSemiring S]
variable [Algebra R S] {P : Type*} [CommSemiring P]

section AtPrime

variable (P : Ideal R) [hp : P.IsPrime]

/-- Given a prime ideal `P`, the typeclass `IsLocalization.AtPrime S P` states that `S` is
isomorphic to the localization of `R` at the complement of `P`. -/
/-
**IsLocalization.AtPrime** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     (S : Type u_2) → [inst_1 
: CommSemiring S] → [Algebra R S] → (P : Ideal R) → [hp : P.IsPrime] → Prop
参数：S : Type u_2；P : Ideal R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a prime ideal `P`, the typeclass `IsLocalization.AtPrime S P` states that 
`S` is
isomorphic to the localization of `R` at the complement of `P`.
-/
protected abbrev IsLocalization.AtPrime :=
  IsLocalization P.primeCompl S

/-- Given a prime ideal `P`, `Localization.AtPrime P` is a localization of
`R` at the complement of `P`, as a quotient type. -/
/-
**Localization.AtPrime** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：{R : Type u_1} → [inst : CommSemiring R] → (P : Ideal R) → [hp : P.IsPrime
] → Type u_1
参数：P : Ideal R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a prime ideal `P`, `Localization.AtPrime P` is a localization of
`R` at the complement of `P`, as a quotient type.
-/
protected abbrev Localization.AtPrime :=
  Localization P.primeCompl

namespace IsLocalization

/-
**IsLocalization.AtPrime.nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization.At
Prime`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Type u_2) [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S] (P : Ideal R)   [hp : P.IsPrime] [IsLocalization.
AtPrime S P], Nontrivial S
参数：S : Type u_2；P : Ideal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
-/
theorem AtPrime.nontrivial [IsLocalization.AtPrime S P] : Nontrivial S :=
  nontrivial_of_ne (0 : S) 1 fun hze => by
    rw [← (algebraMap R S).map_one, ← (algebraMap R S).map_zero] at hze
    obtain ⟨t, ht⟩ := (eq_iff_exists P.primeCompl S).1 hze
    have htz : (t : R) = 0 := by simpa using ht.symm
    exact t.2 (htz.symm ▸ P.zero_mem : ↑t ∈ P)
/-
**IsLocalization.AtPrime.isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization.A
tPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Type u_2) [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S] (P : Ideal R)   [hp : P.IsPrime] [IsLocalization.
AtPrime S P], IsLocalRing S
参数：S : Type u_2；P : Ideal R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_nonunits_add`：of_nonunits_add [Nontrivial R] (h : forall 
a b : R, a in nonunits R -> b in nonunits R -> a + b in nonunits R) : IsLocalRin
g R where isUnit_…
· 使用定理 `IsLocalization.AtPrime.nontrivial`：∀ {R : Type u_1} [inst : CommSemiring
 R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal R
)   [hp : P.IsPrime] [I…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.mk'_mul_mk'_eq_one'`：∀ {R : Type u_1} [inst : CommSemirin
g R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Alge
bra R S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `IsLocalization.eq`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submono
id R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 
: IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `IsLocalization.mk'_add`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
-/
theorem AtPrime.isLocalRing [IsLocalization.AtPrime S P] : IsLocalRing S :=
  letI := AtPrime.nontrivial S P -- Can't be a local instance because we can't figure out `P`.
  IsLocalRing.of_nonunits_add
    (by
      intro x y hx hy hu
      obtain ⟨z, hxyz⟩ := isUnit_iff_exists_inv.1 hu
      have : ∀ {r : R} {s : P.primeCompl}, mk' S r s ∈ nonunits S → r ∈ P := fun {r s} =>
        not_imp_comm.1 fun nr => isUnit_iff_exists_inv.2 ⟨mk' S ↑s (⟨r, nr⟩ : P.primeCompl),
          mk'_mul_mk'_eq_one' _ _ <| show r ∈ P.primeCompl from nr⟩
      rcases exists_mk'_eq P.primeCompl x with ⟨rx, sx, hrx⟩
      rcases exists_mk'_eq P.primeCompl y with ⟨ry, sy, hry⟩
      rcases exists_mk'_eq P.primeCompl z with ⟨rz, sz, hrz⟩
      rw [← hrx, ← hry, ← hrz, ← mk'_add, ← mk'_mul, ← mk'_self S P.primeCompl.one_mem] at hxyz
      rw [← hrx] at hx
      rw [← hry] at hy
      obtain ⟨t, ht⟩ := IsLocalization.eq.1 hxyz
      simp only [mul_one, one_mul, Submonoid.coe_mul] at ht
      suffices (t : R) * (sx * sy * sz) ∈ P from
        not_or_intro (mt hp.mem_or_mem <| not_or_intro sx.2 sy.2) sz.2
          (hp.mem_or_mem <| (hp.mem_or_mem this).resolve_left t.2)
      rw [← ht]
      exact
        P.mul_mem_left _ <| P.mul_mem_right _ <|
            P.add_mem (P.mul_mem_right _ <| this hx) <| P.mul_mem_right _ <| this hy)

variable {A : Type*} [CommRing A] [IsDomain A]

/-- The localization of an integral domain at the complement of a prime ideal is an integral domain.
-/
/-
**IsLocalization.isDomain_of_local_atPrime** 是 Mathlib 中的一个实例，位于命名空间 `IsLocaliza
tion`。
形式化陈述：isDomain_of_local_atPrime {P : Ideal A} (_ : P.IsPrime) : IsDomain (Locali
zation.AtPrime P)
参数：_ : P.IsPrime。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isDomain_localization`：isDomain_localization {M : Submono
id R} (hM : M <= nonZeroDivisors R) : IsDomain (Localization M)
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α

--- 原说明 ---
The localization of an integral domain at the complement of a prime ideal is an 
integral domain.
-/
instance isDomain_of_local_atPrime {P : Ideal A} (_ : P.IsPrime) :
    IsDomain (Localization.AtPrime P) :=
  isDomain_localization P.primeCompl_le_nonZeroDivisors

end IsLocalization

namespace Localization

/-- The localization of `R` at the complement of a prime ideal is a local ring. -/
/-
**Localization.AtPrime.isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 `Localization.AtPri
me`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (P : Ideal R) [hp : P.IsPrime], I
sLocalRing (Localization P.primeCompl)
参数：P : Ideal R；Localization P.primeCompl。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…

--- 原说明 ---
The localization of `R` at the complement of a prime ideal is a local ring.
-/
instance AtPrime.isLocalRing : IsLocalRing (Localization P.primeCompl) :=
  IsLocalization.AtPrime.isLocalRing (Localization P.primeCompl) P
/-
**Localization.** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S : Type*} [CommRing R] [IsDomain R] {P : Ideal R} [CommRing S] [Algebra R S]
    [IsTorsionFree R S] [IsDomain S] [P.IsPrime] :
    IsTorsionFree (Localization.AtPrime P) <|
      Localization <| Algebra.algebraMapSubmonoid S P.primeCompl :=
  .of_isLocalization R S P.primeCompl_le_nonZeroDivisors
/-
**Localization._root_.IsLocalization.AtPrime.faithfulSMul** 是 Mathlib 中的一个定理，位于命
名空间 `Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsLocalization.AtPrime.faithfulSMul (R : Type*) [CommRing R] [NoZeroDivisors R]
    [Algebra R S] (P : Ideal R) [hp : P.IsPrime] [IsLocalization.AtPrime S P] :
    FaithfulSMul R S := by
  rw [faithfulSMul_iff_algebraMap_injective, IsLocalization.injective_iff_isRegular P.primeCompl]
  exact fun ⟨_, h⟩ ↦ .of_ne_zero <| by aesop
/-
**Localization.** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [CommRing R] [NoZeroDivisors R] (P : Ideal R) [hp : P.IsPrime] :
    FaithfulSMul R (Localization.AtPrime P) := IsLocalization.AtPrime.faithfulSMul _ _ P

end Localization

end AtPrime

namespace IsLocalization

variable {A : Type*} [CommRing A] [IsDomain A]

/-- This is an `IsLocalization.AtPrime` version for `IsLocalization.isDomain_of_local_atPrime`. -/
/-
**IsLocalization.isDomain_of_atPrime** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalization`。
形式化陈述：isDomain_of_atPrime (S : Type*) [CommSemiring S] [Algebra A S] (P : Ideal 
A) [P.IsPrime] [IsLocalization.AtPrime S P] : IsDomain S
参数：S : Type*；P : Ideal A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isDomain_of_le_nonZeroDivisors`：isDomain_of_le_nonZeroDiv
isors (hM : M <= nonZeroDivisors R) : IsDomain S where __ : IsCancelMulZero S
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α

--- 原说明 ---
This is an `IsLocalization.AtPrime` version for `IsLocalization.isDomain_of_loca
l_atPrime`.
-/
theorem isDomain_of_atPrime (S : Type*) [CommSemiring S] [Algebra A S]
    (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime S P] : IsDomain S :=
  isDomain_of_le_nonZeroDivisors S P.primeCompl_le_nonZeroDivisors

namespace AtPrime

variable (I : Ideal R) [hI : I.IsPrime] [IsLocalization.AtPrime S I]

set_option backward.isDefEq.respectTransparency false in
/-- The prime ideals in the localization of a commutative ring at a prime ideal I are in
order-preserving bijection with the prime ideals contained in I. -/
@[simps!]
/-
**IsLocalization.AtPrime.orderIsoOfPrime** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalizati
on.AtPrime`。
形式化陈述：orderIsoOfPrime : { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPri
me ∧ p <= I }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime ideals in the localization of a commutative ring at a prime ideal I ar
e in
order-preserving bijection with the prime ideals contained in I.
-/
def orderIsoOfPrime : { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ p ≤ I } :=
  (IsLocalization.orderIsoOfPrime I.primeCompl S).trans <| .setCongr _ _ <|
    show Set.ofPred _ = Set.ofPred _
    by ext; simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left]

/-- The prime spectrum of the localization of a commutative ring R at a prime ideal I are in
order-preserving bijection with the interval $(-∞, I]$ in the prime spectrum of R. -/
/-
**IsLocalization.AtPrime.primeSpectrumOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `IsLoca
lization.AtPrime`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     (S : Type u_2) →       [i
nst_1 : CommSemiring S] →         [inst_2 : Algebra R S] →           (I : Ideal 
R) →             [hI : I.IsPrime] →               [IsLocalization.AtPrime S I] →
 PrimeSpectrum S ≃o ↑(Set.Iic { asIdeal := I, isPrime := hI })
参数：S : Type u_2；I : Ideal R；Set.Iic { asIdeal := I, isPrime := hI }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The prime spectrum of the localization of a commutative ring R at a prime ideal 
I are in
order-preserving bijection with the interval $(-∞, I]$ in the prime spectrum of 
R.
-/
@[simps!] def primeSpectrumOrderIso : PrimeSpectrum S ≃o Set.Iic (⟨I, hI⟩ : PrimeSpectrum R) :=
  (PrimeSpectrum.equivSubtype S).trans <| (orderIsoOfPrime S I).trans
    ⟨⟨fun p ↦ ⟨⟨p, p.2.1⟩, p.2.2⟩, fun p ↦ ⟨p.1.1, p.1.2, p.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩, .rfl⟩
/-
**IsLocalization.AtPrime.isUnit_to_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliza
tion.AtPrime`。
形式化陈述：isUnit_to_map_iff (x : R) : IsUnit ((algebraMap R S) x) ↔ x in I.primeComp
l
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
· 使用定理 `disjoint_compl_left`：disjoint_compl_left : Disjoint aᶜ a
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
-/
theorem isUnit_to_map_iff (x : R) : IsUnit ((algebraMap R S) x) ↔ x ∈ I.primeCompl :=
  ⟨fun h hx =>
    (isPrime_of_isPrime_disjoint I.primeCompl S I hI disjoint_compl_left).ne_top <|
      (Ideal.map (algebraMap R S) I).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem _ hx) h,
    fun h => map_units S ⟨x, h⟩⟩

-- Can't use typeclasses to infer the `IsLocalRing` instance, so use an `optParam` instead
-- (since `IsLocalRing` is a `Prop`, there should be no unification issues.)
/-
**IsLocalization.AtPrime.to_map_mem_maximal_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alization.AtPrime`。
形式化陈述：to_map_mem_maximal_iff (x : R) (h : IsLocalRing S
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.AtPrime.isUnit_to_map_iff`：isUnit_to_map_iff (x : R) : Is
Unit ((algebraMap R S) x) ↔ x in I.primeCompl
-/
theorem to_map_mem_maximal_iff (x : R) (h : IsLocalRing S := isLocalRing S I) :
    algebraMap R S x ∈ IsLocalRing.maximalIdeal S ↔ x ∈ I :=
  not_iff_not.mp <| by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using!
      isUnit_to_map_iff S I x
/-
**IsLocalization.AtPrime.under_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocaliz
ation.AtPrime`。
形式化陈述：under_maximalIdeal (h : IsLocalRing S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.AtPrime.to_map_mem_maximal_iff`：to_map_mem_maximal_iff (x
 : R) (h : IsLocalRing S
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
-/
theorem under_maximalIdeal (h : IsLocalRing S := isLocalRing S I) :
    (IsLocalRing.maximalIdeal S).under R = I :=
  Ideal.ext fun x => by simpa only [Ideal.mem_comap] using to_map_mem_maximal_iff _ I x

@[deprecated (since := "2026-04-09")] alias comap_maximalIdeal := under_maximalIdeal
/-
**IsLocalization.AtPrime.liesOver_maximalIdeal** 是 Mathlib 中的一个实例，位于命名空间 `IsLoca
lization.AtPrime`。
形式化陈述：liesOver_maximalIdeal (h : IsLocalRing S
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.liesOver_iff`：∀ {A : Type u_2} [inst : CommSemiring A] {B : Type u
_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   (p : Ideal A), 
P.LiesOv…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `IsLocalization.AtPrime.under_maximalIdeal`：under_maximalIdeal (h : IsLoc
alRing S
-/
instance liesOver_maximalIdeal (h : IsLocalRing S := isLocalRing S I) :
    (IsLocalRing.maximalIdeal S).LiesOver I :=
  (Ideal.liesOver_iff _ _).mpr (under_maximalIdeal _ _).symm
/-
**IsLocalization.AtPrime.isUnit_mk'_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalizatio
n.AtPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Type u_2) [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S] (I : Ideal R)   [hI : I.IsPrime] [inst_3 : IsLoca
lization.AtPrime S I] (x : R) (y : ↥I.primeCompl),   IsUnit (IsLocalization.mk' 
S x y) ↔ x ∈ I.primeCompl
参数：S : Type u_2；I : Ideal R；x : R；y : ↥I.primeCompl；IsLocalization.mk' S x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `IsLocalization.mk'_mem_iff`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S]
 [inst_3 : IsLoc…
· 使用定理 `IsLocalization.AtPrime.to_map_mem_maximal_iff`：to_map_mem_maximal_iff (x
 : R) (h : IsLocalRing S
· 使用定理 `isUnit_iff_exists_inv`：isUnit_iff_exists_inv [Monoid M] [IsDedekindFinit
eMonoid M] {a : M} : IsUnit a ↔ exists b, a * b = 1
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `IsLocalization.mk'_mul_mk'_eq_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…
-/
theorem isUnit_mk'_iff (x : R) (y : I.primeCompl) : IsUnit (mk' S x y) ↔ x ∈ I.primeCompl :=
  ⟨fun h hx => mk'_mem_iff.mpr ((to_map_mem_maximal_iff S I x).mpr hx) h, fun h =>
    isUnit_iff_exists_inv.mpr ⟨mk' S ↑y ⟨x, h⟩, mk'_mul_mk'_eq_one ⟨x, h⟩ y⟩⟩
/-
**IsLocalization.AtPrime.mk'_mem_maximal_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsLocali
zation.AtPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] (S : Type u_2) [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S] (I : Ideal R)   [hI : I.IsPrime] [inst_3 : IsLoca
lization.AtPrime S I] (x : R) (y : ↥I.primeCompl) (h : optParam (IsLocalRing S) 
⋯),   IsLocalization.mk' S x y ∈ IsLocalRing.maximalIdeal S ↔ x ∈ I
参数：S : Type u_2；I : Ideal R；x : R；y : ↥I.primeCompl；h : optParam (IsLocalRing S)
 ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLocalization.AtPrime.isUnit_mk'_iff`：∀ {R : Type u_1} [inst : CommSemi
ring R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (I : Ide
al R)   [hI : I.IsPrime] [i…
-/
theorem mk'_mem_maximal_iff (x : R) (y : I.primeCompl) (h : IsLocalRing S := isLocalRing S I) :
    mk' S x y ∈ IsLocalRing.maximalIdeal S ↔ x ∈ I :=
  not_iff_not.mp <| by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Classical.not_not] using!
      isUnit_mk'_iff S I x y

end AtPrime

end IsLocalization

namespace Localization

open IsLocalization

variable (I : Ideal R) [hI : I.IsPrime]
variable {I}

/-- The unique maximal ideal of the localization at `I.primeCompl` lies over the ideal `I`. -/
/-
**Localization.AtPrime.under_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Localizatio
n.AtPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {I : Ideal R} [hI : I.IsPrime],  
 Ideal.under R (IsLocalRing.maximalIdeal (Localization I.primeCompl)) = I
参数：IsLocalRing.maximalIdeal (Localization I.primeCompl)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.under_maximalIdeal`：under_maximalIdeal (h : IsLoc
alRing S
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…

--- 原说明 ---
The unique maximal ideal of the localization at `I.primeCompl` lies over the ide
al `I`.
-/
theorem AtPrime.under_maximalIdeal :
    (IsLocalRing.maximalIdeal (Localization I.primeCompl)).under R = I :=
  IsLocalization.AtPrime.under_maximalIdeal _ _

@[deprecated (since := "2026-04-09")] alias AtPrime.comap_maximalIdeal := AtPrime.under_maximalIdeal

/-- The image of `I` in the localization at `I.primeCompl` is a maximal ideal, and in particular
it is the unique maximal ideal given by the local ring structure `AtPrime.isLocalRing` -/
/-
**Localization.AtPrime.map_eq_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `Localizati
on.AtPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {I : Ideal R} [hI : I.IsPrime],  
 Ideal.map (algebraMap R (Localization.AtPrime I)) I = IsLocalRing.maximalIdeal 
(Localization I.primeCompl)
参数：algebraMap R (Localization.AtPrime I)；Localization I.primeCompl。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Localization.AtPrime.under_maximalIdeal`：∀ {R : Type u_1} [inst : CommSe
miring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.under R (IsLocalRing.maximalId
eal (Localization I.primeComp…

--- 原说明 ---
The image of `I` in the localization at `I.primeCompl` is a maximal ideal, and i
n particular
it is the unique maximal ideal given by the local ring structure `AtPrime.isLoca
lRing`
-/
theorem AtPrime.map_eq_maximalIdeal :
    Ideal.map (algebraMap R (Localization.AtPrime I)) I =
      IsLocalRing.maximalIdeal (Localization I.primeCompl) := by
  convert! congr_arg (Ideal.map _) AtPrime.under_maximalIdeal.symm
  rw [map_under I.primeCompl]
/-
**Localization.AtPrime.eq_maximalIdeal_iff_under_eq** 是 Mathlib 中的一个定理，位于命名空间 `L
ocalization.AtPrime`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {I : Ideal R} [hI : I.IsPrime] {J
 : Ideal (Localization.AtPrime I)},   Ideal.under R J = I ↔ J = IsLocalRing.maxi
malIdeal (Localization.AtPrime I)
参数：Localization.AtPrime I；Localization.AtPrime I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `Localization.AtPrime.under_maximalIdeal`：∀ {R : Type u_1} [inst : CommSe
miring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.under R (IsLocalRing.maximalId
eal (Localization I.primeComp…
-/
lemma AtPrime.eq_maximalIdeal_iff_under_eq {J : Ideal (Localization.AtPrime I)} :
    J.under R = I ↔ J = IsLocalRing.maximalIdeal (Localization.AtPrime I) where
  mp h := le_antisymm (IsLocalRing.le_maximalIdeal (fun hJ ↦ (hI.ne_top (h.symm ▸ hJ ▸ rfl)))) <| by
    simpa [← AtPrime.map_eq_maximalIdeal, ← h] using Ideal.map_comap_le
  mpr h := h.symm ▸ AtPrime.under_maximalIdeal

@[deprecated (since := "2026-04-09")] alias AtPrime.eq_maximalIdeal_iff_comap_eq :=
  AtPrime.eq_maximalIdeal_iff_under_eq
/-
**Localization.le_comap_primeCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：le_comap_primeCompl_iff {J : Ideal P} [J.IsPrime] {f : R ->+* P} : I.prime
Compl <= J.primeCompl.comap f ↔ J.comap f <= I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
-/
theorem le_comap_primeCompl_iff {J : Ideal P} [J.IsPrime] {f : R →+* P} :
    I.primeCompl ≤ J.primeCompl.comap f ↔ J.comap f ≤ I :=
  ⟨fun h x hx => by
    contrapose hx
    exact h hx,
   fun h _ hx hfxJ => hx (h hfxJ)⟩

variable (I)

/-- For a ring hom `f : R →+* S` and a prime ideal `J` in `S`, the induced ring hom from the
localization of `R` at `J.comap f` to the localization of `S` at `J`.

To make this definition more flexible, we allow any ideal `I` of `R` as input, together with a proof
that `I = J.comap f`. This can be useful when `I` is not definitionally equal to `J.comap f`.
-/
/-
**Localization.localRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：localRingHom (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.comap f
) : Localization.AtPrime I ->+* Localization.AtPrime J
参数：J : Ideal P；f : R ->+* P；hIJ : I = J.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a ring hom `f : R →+* S` and a prime ideal `J` in `S`, the induced ring hom 
from the
localization of `R` at `J.comap f` to the localization of `S` at `J`.

To make this definition more flexible, we allow any ideal `I` of `R` as input, t
ogether with a proof
that `I = J.comap f`. This can be useful when `I` is not definitionally equal to
 `J.comap f`.
-/
noncomputable def localRingHom (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f) :
    Localization.AtPrime I →+* Localization.AtPrime J :=
  IsLocalization.map (Localization.AtPrime J) f (le_comap_primeCompl_iff.mpr (ge_of_eq hIJ))

@[simp]
/-
**Localization.localRingHom_to_map** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：localRingHom_to_map (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.
comap f) (x : R) : localRingHom I J f hIJ (algebraMap _ _ x) = algebraMap _ _ (f
 x)
参数：J : Ideal P；f : R ->+* P；hIJ : I = J.comap f；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.map_eq`：map_eq (x) : map Q g hy ((algebraMap R S) x) = al
gebraMap P Q (g x)
-/
theorem localRingHom_to_map (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f)
    (x : R) : localRingHom I J f hIJ (algebraMap _ _ x) = algebraMap _ _ (f x) :=
  map_eq _ _

@[simp]
/-
**Localization.localRingHom_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：localRingHom_mk' (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.com
ap f) (x : R) (y : I.primeCompl) : localRingHom I J f hIJ (IsLocalization.mk' _ 
x y) = IsLocalization.mk' (Localization.AtPrime J) (f x) (⟨f y, le_comap_primeCo
mpl_iff.mpr (ge_of_eq hIJ) y.2⟩ : J.primeCompl)
参数：J : Ideal P；f : R ->+* P；hIJ : I = J.comap f；x : R；y : I.primeCompl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
-/
theorem localRingHom_mk' (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f) (x : R)
    (y : I.primeCompl) :
    localRingHom I J f hIJ (IsLocalization.mk' _ x y) =
      IsLocalization.mk' (Localization.AtPrime J) (f x)
        (⟨f y, le_comap_primeCompl_iff.mpr (ge_of_eq hIJ) y.2⟩ : J.primeCompl) :=
  map_mk' _ _ _

@[simp]
/-
**Localization.localRingHom_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：localRingHom_mk (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.coma
p f) (x : R) (y : I.primeCompl) : localRingHom I J f hIJ (mk x y) = mk (f x) ⟨f 
y, by aesop⟩
参数：J : Ideal P；f : R ->+* P；hIJ : I = J.comap f；x : R；y : I.primeCompl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Localization.le_comap_primeCompl_iff`：le_comap_primeCompl_iff {J : Ideal
 P} [J.IsPrime] {f : R ->+* P} : I.primeCompl <= J.primeCompl.comap f ↔ J.comap 
f <= I
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Localization.localRingHom_mk'`：localRingHom_mk' (J : Ideal P) [J.IsPrime
] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom
 I J f hIJ (IsLocal…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem localRingHom_mk (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f) (x : R)
    (y : I.primeCompl) :
    localRingHom I J f hIJ (mk x y) = mk (f x) ⟨f y, by aesop⟩ := by
  simp_rw [mk_eq_mk', localRingHom_mk']

@[instance]
/-
**Localization.isLocalHom_localRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：isLocalHom_localRingHom (J : Ideal P) [hJ : J.IsPrime] (f : R ->+* P) (hIJ
 : I = J.comap f) : IsLocalHom (localRingHom I J f hIJ)
参数：J : Ideal P；f : R ->+* P；hIJ : I = J.comap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.AtPrime.isUnit_mk'_iff`：∀ {R : Type u_1} [inst : CommSemi
ring R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (I : Ide
al R)   [hI : I.IsPrime] [i…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Localization.le_comap_primeCompl_iff`：le_comap_primeCompl_iff {J : Ideal
 P} [J.IsPrime] {f : R ->+* P} : I.primeCompl <= J.primeCompl.comap f ↔ J.comap 
f <= I
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Localization.localRingHom_mk'`：localRingHom_mk' (J : Ideal P) [J.IsPrime
] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom
 I J f hIJ (IsLocal…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
-/
theorem isLocalHom_localRingHom (J : Ideal P) [hJ : J.IsPrime] (f : R →+* P)
    (hIJ : I = J.comap f) : IsLocalHom (localRingHom I J f hIJ) :=
  IsLocalHom.mk fun x hx => by
    rcases IsLocalization.exists_mk'_eq I.primeCompl x with ⟨r, s, rfl⟩
    rw [localRingHom_mk'] at hx
    rw [AtPrime.isUnit_mk'_iff] at hx ⊢
    exact fun hr => hx ((SetLike.ext_iff.mp hIJ r).mp hr)
/-
**Localization.localRingHom_unique** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：localRingHom_unique (J : Ideal P) [J.IsPrime] (f : R ->+* P) (hIJ : I = J.
comap f) {j : Localization.AtPrime I ->+* Localization.AtPrime J} (hj : forall x
 : R, j (algebraMap _ _ x) = algebraMap _ _ (f x)) : localRingHom I J f hIJ = j
参数：J : Ideal P；f : R ->+* P；hIJ : I = J.comap f；hj : forall x : R, j (algebraMap
 _ _ x) = algebraMap _ _ (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.map_unique`：map_unique (j : S ->+* Q) (hj : forall x : R,
 j (algebraMap R S x) = algebraMap P Q (g x)) : map Q g hy = j
-/
theorem localRingHom_unique (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = J.comap f)
    {j : Localization.AtPrime I →+* Localization.AtPrime J}
    (hj : ∀ x : R, j (algebraMap _ _ x) = algebraMap _ _ (f x)) : localRingHom I J f hIJ = j :=
  map_unique _ _ hj

@[simp]
/-
**Localization.localRingHom_id** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：localRingHom_id : localRingHom I I (RingHom.id R) (Ideal.comap_id I).symm 
= RingHom.id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.localRingHom_unique`：localRingHom_unique (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) {j : Localization.AtPrime I ->+* Lo
calization.AtPrime J} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_id`：comap_id : I.comap (RingHom.id R) = I
-/
theorem localRingHom_id : localRingHom I I (RingHom.id R) (Ideal.comap_id I).symm = RingHom.id _ :=
  localRingHom_unique _ _ _ _ fun _ => rfl

-- `simp` can't figure out `J` so this can't be a `@[simp]` lemma.
/-
**Localization.localRingHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：localRingHom_comp {S : Type*} [CommSemiring S] (J : Ideal S) [hJ : J.IsPri
me] (K : Ideal P) [hK : K.IsPrime] (f : R ->+* S) (hIJ : I = J.comap f) (g : S -
>+* P) (hJK : J = K.comap g) : localRingHom I K (g.comp f) (by rw [hIJ, hJK, Ide
al.comap_comap f g]) = (localRingHom J K g hJK).comp (localRingHom I J f hIJ)
参数：J : Ideal S；K : Ideal P；f : R ->+* S；hIJ : I = J.comap f；g : S ->+* P；hJK : J
 = K.comap g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.localRingHom_unique`：localRingHom_unique (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) {j : Localization.AtPrime I ->+* Lo
calization.AtPrime J} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem localRingHom_comp {S : Type*} [CommSemiring S] (J : Ideal S) [hJ : J.IsPrime] (K : Ideal P)
    [hK : K.IsPrime] (f : R →+* S) (hIJ : I = J.comap f) (g : S →+* P) (hJK : J = K.comap g) :
    localRingHom I K (g.comp f) (by rw [hIJ, hJK, Ideal.comap_comap f g]) =
      (localRingHom J K g hJK).comp (localRingHom I J f hIJ) :=
  localRingHom_unique _ _ _ _ fun r => by
    simp only [Function.comp_apply, RingHom.coe_comp, localRingHom_to_map]

/-- Isomorphic rings have isomorphic localizations. -/
@[simps]
/-
**Localization.localRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：localRingEquiv (J : Ideal P) [J.IsPrime] (f : R ≃+* P) (hIJ : I = J.comap 
f) : Localization.AtPrime I ≃+* Localization.AtPrime J where __
参数：J : Ideal P；f : R ≃+* P；hIJ : I = J.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic rings have isomorphic localizations.
-/
noncomputable def localRingEquiv (J : Ideal P) [J.IsPrime] (f : R ≃+* P) (hIJ : I = J.comap f) :
    Localization.AtPrime I ≃+* Localization.AtPrime J where
  __ := localRingHom I J f hIJ
  invFun := localRingHom J I f.symm
    (by rw [hIJ, ← Ideal.comap_coe f, Ideal.comap_comap, RingEquiv.comp_symm, Ideal.comap_id])
  left_inv x := by simp [localRingHom, map_map]
  right_inv x := by simp [localRingHom, map_map]

variable {S} in
/-- For an `R`-algebra homomorphism `f : S →ₐ[R] P` and prime ideals `I = f⁻¹(J)`, the induced
`R`-algebra homomorphism from the localization of `S` at `I` to the localization of `P` at `J`.

See `localAlgHom'` for a variant where the base ring `R` is also localized. -/
/-
**Localization.localAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：localAlgHom [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPri
me] (f : S ->ₐ[R] P) (hIJ : I = J.comap f) : Localization.AtPrime I ->ₐ[R] Local
ization.AtPrime J where __
参数：I : Ideal S；J : Ideal P；f : S ->ₐ[R] P；hIJ : I = J.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an `R`-algebra homomorphism `f : S →ₐ[R] P` and prime ideals `I = f⁻¹(J)`, t
he induced
`R`-algebra homomorphism from the localization of `S` at `I` to the localization
 of `P` at `J`.

See `localAlgHom'` for a variant where the base ring `R` is also localized.
-/
noncomputable def localAlgHom [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
    (f : S →ₐ[R] P) (hIJ : I = J.comap f) :
    Localization.AtPrime I →ₐ[R] Localization.AtPrime J where
  __ := localRingHom I J f.toRingHom hIJ
  commutes' r := by
    simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime I),
      localRingHom_to_map, IsScalarTower.algebraMap_apply R P (Localization.AtPrime J)]

variable {S} in
/-
**Localization.localAlgHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {S : Type u_2} [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S] {P : Type u_3}   [inst_3 : CommSemiring P] [inst_
4 : Algebra R P] (I : Ideal S) [inst_5 : I.IsPrime] (J : Ideal P) [inst_6 : J.Is
Prime]   (f : S →ₐ[R] P) (hIJ : I = Ideal.comap f J) (x : Localization.AtPrime I
),   (Localization.localAlgHom I J f hIJ) x = (Localization.localRingHom I J f.t
oRingHom hIJ) x
参数：I : Ideal S；J : Ideal P；f : S →ₐ[R] P；hIJ : I = Ideal.comap f J；x : Localizat
ion.AtPrime I；Localization.localAlgHom I J f hIJ；Localization.localRingHom I J f
.toRingHom hIJ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
@[simp] lemma localAlgHom_apply [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
    (f : S →ₐ[R] P) (hIJ : I = J.comap f) (x) :
    localAlgHom I J f hIJ x = localRingHom I J f.toRingHom hIJ x := rfl

variable {S} in
/-- Isomorphic algebras have isomorphic localizations.

See `localAlgEquiv'` for a variant where the base ring is also localized. -/
@[simps]
/-
**Localization.localAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：localAlgEquiv [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsP
rime] (f : S ≃ₐ[R] P) (hIJ : I = J.comap f) : Localization.AtPrime I ≃ₐ[R] Local
ization.AtPrime J where __
参数：I : Ideal S；J : Ideal P；f : S ≃ₐ[R] P；hIJ : I = J.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic algebras have isomorphic localizations.

See `localAlgEquiv'` for a variant where the base ring is also localized.
-/
noncomputable def localAlgEquiv [Algebra R P] (I : Ideal S) [I.IsPrime] (J : Ideal P) [J.IsPrime]
    (f : S ≃ₐ[R] P) (hIJ : I = J.comap f) :
    Localization.AtPrime I ≃ₐ[R] Localization.AtPrime J where
  __ := localAlgHom I J f.toAlgHom hIJ
  __ := localRingEquiv I J f.toRingEquiv hIJ
/-
**Localization.localRingHom_bijective_of_saturated_inf_eq_top** 是 Mathlib 中的一个引理
，位于命名空间 `Localization`。
形式化陈述：localRingHom_bijective_of_saturated_inf_eq_top {P : Ideal S} [P.IsPrime] {
s : Subalgebra R S} (H : s.saturation (P.primeCompl ⊓ s.toSubmonoid) (by simp) =
 ⊤) (p : Ideal s) [p.IsPrime] [P.LiesOver p] : Function.Bijective (Localization.
localRingHom _ _ _ (P.over_def p))
参数：H : s.saturation (P.primeCompl ⊓ s.toSubmonoid) (by simp) = ⊤；p : Ideal s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Ideal.IsPrime.mul_notMem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x ∉ I → y ∉ I → x * y ∉ I
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.primeCompl.congr_simp`：∀ {α : Type u} [inst : Semiring α] (P P_1 :
 Ideal α) (e_P : P = P_1) [hp : P.IsPrime], P.primeCompl = P_1.primeCompl
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Localization.le_comap_primeCompl_iff`：le_comap_primeCompl_iff {J : Ideal
 P} [J.IsPrime] {f : R ->+* P} : I.primeCompl <= J.primeCompl.comap f ↔ J.comap 
f <= I
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `IsLocalization.mk'_surjective`：∀ {R : Type u_1} [inst : CommSemiring R] 
(M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R
 S] [inst_3 : IsLoc…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Localization.localRingHom_mk'`：localRingHom_mk' (J : Ideal P) [J.IsPrime
] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom
 I J f hIJ (IsLocal…
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
（共 55 条，此处仅展示前 30 条）
-/
lemma localRingHom_bijective_of_saturated_inf_eq_top
    {P : Ideal S} [P.IsPrime] {s : Subalgebra R S}
    (H : s.saturation (P.primeCompl ⊓ s.toSubmonoid) (by simp) = ⊤) (p : Ideal s)
    [p.IsPrime] [P.LiesOver p] :
    Function.Bijective (Localization.localRingHom _ _ _ (P.over_def p)) := by
  constructor
  · suffices ∀ a ∈ s, ∀ b ∈ s, b ∉ P → ∀ c ∈ s, ∀ d ∈ s, d ∉ P → ∀ x ∉ P,
        x * (a * d) = x * (c * b) → ∃ a_6 ∉ P, a_6 ∈ s ∧ a_6 * (a * d) = a_6 * (c * b) by
      simpa [Function.Injective, (IsLocalization.mk'_surjective p.primeCompl).forall, P.over_def p,
        Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq', Subtype.ext_iff, -map_mul,
        IsLocalization.eq_iff_exists P.primeCompl, IsLocalization.eq_iff_exists p.primeCompl]
    intro a _ b _ _ c _ d _ _ x hxP e
    obtain ⟨t, ⟨htP, -⟩, ht⟩ := H.ge (Set.mem_univ x)
    exact ⟨_, ‹P.IsPrime›.mul_notMem htP hxP, ht, by simp [mul_assoc, e]⟩
  · suffices ∀ y, ∀ z ∉ P, ∃ y' ∈ s, ∃ z' ∉ P, z' ∈ s ∧ ∃ t ∉ P, t * (z * y') = t * (z' * y) by
      simpa [(IsLocalization.mk'_surjective p.primeCompl).exists,
        (IsLocalization.mk'_surjective P.primeCompl).forall, P.over_def p,
        Localization.localRingHom_mk', IsLocalization.mk'_eq_iff_eq, -map_mul,
        IsLocalization.eq_iff_exists P.primeCompl, Function.Surjective] using this
    intro y z hzP
    obtain ⟨a, ⟨haP, has⟩, ha⟩ := H.ge (Set.mem_univ y)
    obtain ⟨b, ⟨hbP, hbs⟩, hb⟩ := H.ge (Set.mem_univ z)
    exact ⟨_, mul_mem ha hbs, _, P.primeCompl.mul_mem (mul_mem hbP hzP) haP, mul_mem hb has, 1,
      P.primeCompl.one_mem, by ring⟩

namespace AtPrime

section

variable {A B C : Type*} [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] [Algebra A B]
  [IsScalarTower R A B] [CommSemiring C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]

/-- If `P` lies over `p`, then `Localization.AtPrime P` is an algebra over `Localization.AtPrime p`.
This is not an instance for performance reasons and to avoid diamonds in the situation where the top
ring is already an algebra over `Localization.AtPrime p` (e.g., this happens for `Ideal.Fiber`). -/
@[instance_reducible]
/-
**Localization.AtPrime.algebraOfLiesOver** 是 Mathlib 中的一个定义，位于命名空间 `Localization
.AtPrime`。
形式化陈述：algebraOfLiesOver (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.L
iesOver p] : Algebra (Localization.AtPrime p) (Localization.AtPrime P)
参数：p : Ideal A；P : Ideal B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` lies over `p`, then `Localization.AtPrime P` is an algebra over `Localiza
tion.AtPrime p`.
This is not an instance for performance reasons and to avoid diamonds in the sit
uation where the top
ring is already an algebra over `Localization.AtPrime p` (e.g., this happens for
 `Ideal.Fiber`).
-/
noncomputable def algebraOfLiesOver
    (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
  (Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over).toAlgebra

@[deprecated (since := "2026-04-24")] alias instAlgebraOfLiesOver := algebraOfLiesOver

/-- A predicate expressing that `Localization.AtPrime P` is an algebra over `Localization.AtPrime p`
in the natural way when `P` lies over `p`. -/
/-
**Localization.AtPrime.IsLiesOverAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 `Localizati
on.AtPrime`。
形式化陈述：{A : Type u_4} →   {B : Type u_5} →     [inst : CommSemiring A] →       [i
nst_1 : CommSemiring B] →         [inst_2 : Algebra A B] →           (p : Ideal 
A) →             [inst_3 : p.IsPrime] →               (P : Ideal B) →           
      [inst_4 : P.IsPrime] →                   [P.LiesOver p] → [Algebra (Locali
zation.AtPrime p) (Localization.AtPrime P)] → Prop
参数：p : Ideal A；P : Ideal B；Localization.AtPrime p；Localization.AtPrime P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate expressing that `Localization.AtPrime P` is an algebra over `Localiz
ation.AtPrime p`
in the natural way when `P` lies over `p`.
-/
class IsLiesOverAlgebra (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)] : Prop where
  algebraMap_eq : algebraMap (Localization.AtPrime p) (Localization.AtPrime P) =
    Localization.localRingHom p P (algebraMap A B) Ideal.LiesOver.over
/-
**Localization.AtPrime.** 是 Mathlib 中的一个实例，位于命名空间 `Localization.AtPrime`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    letI := algebraOfLiesOver p P; IsLiesOverAlgebra p P :=
  letI := algebraOfLiesOver p P; ⟨rfl⟩
/-
**Localization.AtPrime.** 是 Mathlib 中的一个实例，位于命名空间 `Localization.AtPrime`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)] [IsLiesOverAlgebra p P] :
    IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P) :=
  .of_algebraMap_eq <| by
    simp [IsScalarTower.algebraMap_apply R A (Localization.AtPrime p),
      Localization.localRingHom_to_map, IsScalarTower.algebraMap_apply R B (Localization.AtPrime P),
      IsScalarTower.algebraMap_apply R A B, IsLiesOverAlgebra.algebraMap_eq]
/-
**Localization.AtPrime.** 是 Mathlib 中的一个实例，位于命名空间 `Localization.AtPrime`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p] (Q : Ideal C)
    [Q.IsPrime] [Q.LiesOver P] [Q.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)] [IsLiesOverAlgebra p P]
    [Algebra (Localization.AtPrime P) (Localization.AtPrime Q)] [IsLiesOverAlgebra P Q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime Q)] [IsLiesOverAlgebra p Q] :
    IsScalarTower (Localization.AtPrime p) (Localization.AtPrime P) (Localization.AtPrime Q) :=
  .of_algebraMap_eq' <| by
    simp [IsLiesOverAlgebra.algebraMap_eq, ← localRingHom_comp, ← IsScalarTower.algebraMap_eq]

end

variable {ι : Type*} {R : ι → Type*} [∀ i, CommSemiring (R i)]
variable {i : ι} (I : Ideal (R i)) [I.IsPrime]

/-- `Localization.localRingHom` specialized to a projection homomorphism from a product ring. -/
/-
**Localization.AtPrime.mapPiEvalRingHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `Localizatio
n.AtPrime`。
形式化陈述：mapPiEvalRingHom : Localization.AtPrime (I.comap <| Pi.evalRingHom R i) ->
+* Localization.AtPrime I
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Localization.localRingHom` specialized to a projection homomorphism from a prod
uct ring.
-/
noncomputable abbrev mapPiEvalRingHom :
    Localization.AtPrime (I.comap <| Pi.evalRingHom R i) →+* Localization.AtPrime I :=
  localRingHom _ _ _ rfl
/-
**Localization.AtPrime.mapPiEvalRingHom_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Loc
alization.AtPrime`。
形式化陈述：mapPiEvalRingHom_bijective : Function.Bijective (mapPiEvalRingHom I)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.mapPiEvalRingHom_bijective`：mapPiEvalRingHom_bijective : Bi
jective (mapPiEvalRingHom S)
-/
theorem mapPiEvalRingHom_bijective : Function.Bijective (mapPiEvalRingHom I) :=
  Localization.mapPiEvalRingHom_bijective _
/-
**Localization.AtPrime.mapPiEvalRingHom_comp_algebraMap** 是 Mathlib 中的一个定理，位于命名空
间 `Localization.AtPrime`。
形式化陈述：mapPiEvalRingHom_comp_algebraMap : (mapPiEvalRingHom I).comp (algebraMap _
 _) = (algebraMap _ _).comp (Pi.evalRingHom R i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.map_comp`：map_comp : (map Q g hy).comp (algebraMap R S) =
 (algebraMap P Q).comp g
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
-/
theorem mapPiEvalRingHom_comp_algebraMap :
    (mapPiEvalRingHom I).comp (algebraMap _ _) = (algebraMap _ _).comp (Pi.evalRingHom R i) :=
  IsLocalization.map_comp _
/-
**Localization.AtPrime.mapPiEvalRingHom_algebraMap_apply** 是 Mathlib 中的一个定理，位于命名
空间 `Localization.AtPrime`。
形式化陈述：mapPiEvalRingHom_algebraMap_apply {r : Π i, R i} : mapPiEvalRingHom I (alg
ebraMap _ _ r) = algebraMap _ _ (r i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
-/
theorem mapPiEvalRingHom_algebraMap_apply {r : Π i, R i} :
    mapPiEvalRingHom I (algebraMap _ _ r) = algebraMap _ _ (r i) :=
  localRingHom_to_map ..

end AtPrime

section localAlg

open AtPrime

variable {S} [Algebra R P] (J : Ideal S) (K : Ideal P) [J.IsPrime] [K.IsPrime]
  [J.LiesOver I] [Algebra (Localization.AtPrime I) (Localization.AtPrime J)] [IsLiesOverAlgebra I J]
  [K.LiesOver I] [Algebra (Localization.AtPrime I) (Localization.AtPrime K)] [IsLiesOverAlgebra I K]

/-- For an `R`-algebra homomorphism `f : S →ₐ[R] P` and prime ideals `J = f⁻¹(K)` lying over `I`,
the induced algebra homomorphism from the localization of `S` at `J` to the localization of `P` at
`K` over the localization of `R` at `I`.

See `localAlgHom` for a variant where the base ring `R` is not localized. -/
@[simps!]
/-
**Localization.localAlgHom'** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：localAlgHom' (f : S ->ₐ[R] P) (h : J = K.comap f) : Localization.AtPrime J
 ->ₐ[Localization.AtPrime I] Localization.AtPrime K
参数：f : S ->ₐ[R] P；h : J = K.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an `R`-algebra homomorphism `f : S →ₐ[R] P` and prime ideals `J = f⁻¹(K)` ly
ing over `I`,
the induced algebra homomorphism from the localization of `S` at `J` to the loca
lization of `P` at
`K` over the localization of `R` at `I`.

See `localAlgHom` for a variant where the base ring `R` is not localized.
-/
noncomputable def localAlgHom' (f : S →ₐ[R] P) (h : J = K.comap f) :
    Localization.AtPrime J →ₐ[Localization.AtPrime I] Localization.AtPrime K :=
  (localAlgHom J K f h).extendScalarsOfIsLocalization (Localization.AtPrime I) I.primeCompl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Isomorphic algebras have isomorphic localizations.

See `localAlgEquiv` for a variant where the base ring is not localized. -/
@[simps!]
/-
**Localization.localAlgEquiv'** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：localAlgEquiv' (f : S ≃ₐ[R] P) (h : J = K.comap f) : Localization.AtPrime 
J ≃ₐ[Localization.AtPrime I] Localization.AtPrime K
参数：f : S ≃ₐ[R] P；h : J = K.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Isomorphic algebras have isomorphic localizations.

See `localAlgEquiv` for a variant where the base ring is not localized.
-/
noncomputable def localAlgEquiv' (f : S ≃ₐ[R] P) (h : J = K.comap f) :
    Localization.AtPrime J ≃ₐ[Localization.AtPrime I] Localization.AtPrime K :=
  (localAlgEquiv J K f h).extendScalarsOfIsLocalization (Localization.AtPrime I) I.primeCompl

end localAlg

end Localization

section

variable (q : Ideal R) [q.IsPrime] (M : Submonoid R) {S : Type*} [CommSemiring S] [Algebra R S]
  [IsLocalization.AtPrime S q]

set_option backward.isDefEq.respectTransparency false in
/-
**Ideal.isPrime_map_of_isLocalizationAtPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.isPrime_map_of_isLocalizationAtPrime {p : Ideal R} [p.IsPrime] (hpq 
: p <= q) : (p.map (algebraMap R S)).IsPrime
参数：hpq : p <= q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
-/
lemma Ideal.isPrime_map_of_isLocalizationAtPrime {p : Ideal R} [p.IsPrime] (hpq : p ≤ q) :
    (p.map (algebraMap R S)).IsPrime := by
  have disj : Disjoint (q.primeCompl : Set R) p := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  apply IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p (by simpa) disj

set_option backward.isDefEq.respectTransparency false in
/-
**Ideal.under_map_of_isLocalizationAtPrime** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.under_map_of_isLocalizationAtPrime {p : Ideal R} [p.IsPrime] (hpq : 
p <= q) : (p.map (algebraMap R S)).under R = p
参数：hpq : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
-/
lemma Ideal.under_map_of_isLocalizationAtPrime {p : Ideal R} [p.IsPrime] (hpq : p ≤ q) :
    (p.map (algebraMap R S)).under R = p := by
  have disj : Disjoint (q.primeCompl : Set R) p := by
    simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hpq]
  exact IsLocalization.under_map_of_isPrime_disjoint _ _ (by simpa) disj
/-
**IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes** 是 Mathlib 中的一
个引理，位于命名空间 ``。
形式化陈述：IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes {R : Type*}
 [CommSemiring R] (p : Ideal R) (hp : p in minimalPrimes R) (S : Type*) [CommSem
iring S] [Algebra R S] [IsLocalization.AtPrime S p (hp
参数：p : Ideal R；hp : p in minimalPrimes R；S : Type*。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Minimal.eq_of_le`：Minimal.eq_of_le (hx : Minimal P x) (hy : P y) (hle : 
y <= x) : y = x
· 使用引理 `minimalPrimes_eq_minimals`：minimalPrimes_eq_minimals : minimalPrimes R =
 {x | Minimal Ideal.IsPrime x}
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes
    {R : Type*} [CommSemiring R] (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    Subsingleton (PrimeSpectrum S) :=
  have := hp.1.1
  have : Unique (Set.Iic (⟨p, hp.1.1⟩ : PrimeSpectrum R)) := ⟨⟨⟨p, hp.1.1⟩, by exact
    fun ⦃x⦄ a ↦ a⟩, fun i ↦ Subtype.ext <| PrimeSpectrum.ext <|
    (minimalPrimes_eq_minimals (R := R) ▸ hp).eq_of_le i.1.2 i.2⟩
  (IsLocalization.AtPrime.primeSpectrumOrderIso S p).subsingleton

open Ideal in
/-- If `R'` (resp. `S'`) is the localization of `R` (resp. `S`) and
`P` lies over `p` then the image of `P` in `S'` lies over the image of `p` in `R'`. -/
/-
**IsLocalization.liesOver_of_isPrime_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalization.liesOver_of_isPrime_of_disjoint {R' S' : Type*} (M : Submon
oid R) (T : Submonoid S) [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Alg
ebra S S'] [Algebra R' S'] [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower 
R R' S'] [IsLocalization M R'] [IsLocalization T S'] (p : Ideal R) {P : Ideal S}
 [P.IsPrime] [P.LiesOver p] (disj : Disjoint (T : Set S) (P : Set S)) : (P.map (
algebraMap S S')).LiesOver (p.map (algebraMap R R'))
参数：M : Submonoid R；T : Submonoid S；p : Ideal R；disj : Disjoint (T : Set S) (P : 
Set S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.under_under`：under_under : (𝔓.under B).under A = 𝔓.under A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J

--- 原说明 ---
If `R'` (resp. `S'`) is the localization of `R` (resp. `S`) and
`P` lies over `p` then the image of `P` in `S'` lies over the image of `p` in `R
'`.
-/
lemma IsLocalization.liesOver_of_isPrime_of_disjoint {R' S' : Type*}
    (M : Submonoid R) (T : Submonoid S)
    [CommSemiring R'] [CommSemiring S'] [Algebra R R'] [Algebra S S'] [Algebra R' S']
    [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']
    [IsLocalization M R'] [IsLocalization T S']
    (p : Ideal R) {P : Ideal S} [P.IsPrime] [P.LiesOver p]
    (disj : Disjoint (T : Set S) (P : Set S)) :
    (P.map (algebraMap S S')).LiesOver (p.map (algebraMap R R')) := by
  suffices h : Ideal.map (algebraMap R R') (under R (under R' (P.map (algebraMap S S')))) =
      Ideal.map (algebraMap R R') p from ⟨by rw [← h, IsLocalization.map_under (M := M)]⟩
  rw [under_under, ← under_under (B := S), under_map_of_isPrime_disjoint _ _ ‹_› disj,
    LiesOver.over (P := P) (p := p)]
/-
**Ideal.IsMaximal.of_isLocalization_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.IsMaximal.of_isLocalization_of_disjoint [IsLocalization M S] {J : Id
eal S} [(J.under R).IsMaximal] : J.IsMaximal
参数：J.under R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.comap_top`：comap_top : (⊤ : Ideal S).comap f = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.comap_mono`：comap_mono [RingHomClass F R S] (h : K <= L) : comap f
 K <= comap f L
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
-/
lemma Ideal.IsMaximal.of_isLocalization_of_disjoint [IsLocalization M S] {J : Ideal S}
    [(J.under R).IsMaximal] : J.IsMaximal := by
  obtain ⟨m, maxm, hm⟩ := exists_le_maximal J <| by
    rintro rfl
    exact Ideal.IsMaximal.ne_top ‹_› (by simp)
  replace hm : under R J ≤ under R m := comap_mono hm
  rwa [← IsLocalization.map_under M S J, IsMaximal.eq_of_le ‹_› (IsPrime.under R m).ne_top hm,
    IsLocalization.map_under M S m]

end

namespace IsLocalization.AtPrime

open Algebra IsLocalRing Ideal IsLocalization IsLocalization.AtPrime

variable (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommSemiring Rₚ] [Algebra R Rₚ]
  [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] (Sₚ : Type*) [CommSemiring Sₚ] [Algebra S Sₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ] [Algebra Rₚ Sₚ]
  (P : Ideal S)

/-
**IsLocalization.AtPrime.isPrime_map_of_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `IsLo
calization.AtPrime`。
形式化陈述：isPrime_map_of_liesOver [P.IsPrime] [P.LiesOver p] : (P.map (algebraMap S 
Sₚ)).IsPrime
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
· 使用定理 `Ideal.disjoint_primeCompl_of_liesOver`：disjoint_primeCompl_of_liesOver [
p.IsPrime] [hPp : 𝔓.LiesOver p] : Disjoint ((Algebra.algebraMapSubmonoid C p.pri
meCompl) : Set C) (𝔓 : Set …
-/
theorem isPrime_map_of_liesOver [P.IsPrime] [P.LiesOver p] : (P.map (algebraMap S Sₚ)).IsPrime :=
  isPrime_of_isPrime_disjoint _ _ _ inferInstance (Ideal.disjoint_primeCompl_of_liesOver P p)
/-
**IsLocalization.AtPrime.map_eq_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocali
zation.AtPrime`。
形式化陈述：map_eq_maximalIdeal : p.map (algebraMap R Rₚ) = maximalIdeal Rₚ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.map_under`：map_under (J : Ideal S) : Ideal.map (algebraMa
p R S) (J.under R) = J
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsLocalization.AtPrime.under_maximalIdeal`：under_maximalIdeal (h : IsLoc
alRing S
-/
theorem map_eq_maximalIdeal : p.map (algebraMap R Rₚ) = maximalIdeal Rₚ := by
  convert! congr_arg (Ideal.map (algebraMap R Rₚ)) (under_maximalIdeal Rₚ p).symm
  rw [map_under p.primeCompl]
/-
**IsLocalization.AtPrime.isMaximal_map** 是 Mathlib 中的一个实例，位于命名空间 `IsLocalization
.AtPrime`。
形式化陈述：isMaximal_map : (p.map (algebraMap R Rₚ)).IsMaximal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.AtPrime.map_eq_maximalIdeal`：map_eq_maximalIdeal : p.map 
(algebraMap R Rₚ) = maximalIdeal Rₚ
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
instance isMaximal_map : (p.map (algebraMap R Rₚ)).IsMaximal := by
  rw [map_eq_maximalIdeal]
  exact maximalIdeal.isMaximal Rₚ
/-
**IsLocalization.AtPrime.under_map_of_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alization.AtPrime`。
形式化陈述：under_map_of_isMaximal [P.IsMaximal] [P.LiesOver p] : (Ideal.map (algebraM
ap S Sₚ) P).under S = P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_map_eq_self_of_isMaximal`：comap_map_eq_self_of_isMaximal (f 
: R ->+* S) {p : Ideal R} [hP' : p.IsMaximal] (hP : Ideal.map f p != ⊤) : (map f
 p).comap f = p
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `IsLocalization.AtPrime.isPrime_map_of_liesOver`：isPrime_map_of_liesOver 
[P.IsPrime] [P.LiesOver p] : (P.map (algebraMap S Sₚ)).IsPrime
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
-/
theorem under_map_of_isMaximal [P.IsMaximal] [P.LiesOver p] :
    (Ideal.map (algebraMap S Sₚ) P).under S = P :=
  comap_map_eq_self_of_isMaximal _ (isPrime_map_of_liesOver S p Sₚ P).ne_top

@[deprecated (since := "2026-04-09")] alias comap_map_of_isMaximal := under_map_of_isMaximal
/-
**IsLocalization.AtPrime.under_maximalIdeal_pow** 是 Mathlib 中的一个引理，位于命名空间 `IsLoc
alization.AtPrime`。
形式化陈述：under_maximalIdeal_pow [p.IsMaximal] (n : Nat) : (IsLocalRing.maximalIdeal
 Rₚ ^ n).under R = p ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.AtPrime.map_eq_maximalIdeal`：map_eq_maximalIdeal : p.map 
(algebraMap R Rₚ) = maximalIdeal Rₚ
· 使用定理 `Ideal.map_pow`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : FunLike F R S]   [rc : RingHomClas
s F…
· 使用引理 `IsLocalization.algebraMap_mem_map_algebraMap_iff`：algebraMap_mem_map_alg
ebraMap_iff (I : Ideal R) (x : R) : algebraMap R S x in I.map (algebraMap R S) ↔
 exists m in M, m * x in I
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.IsMaximal.mul_mem_pow`：∀ {R : Type u} [inst : CommSemiring R] (I :
 Ideal R) [I.IsMaximal] {a b : R} {n : ℕ}, a * b ∈ I ^ n → a ∈ I ∨ b ∈ I ^ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_primeCompl_iff`：mem_primeCompl_iff {P : Ideal α} [P.IsPrime] {
x : α} : x in P.primeCompl ↔ x ∉ P
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma under_maximalIdeal_pow [p.IsMaximal] (n : ℕ) :
    (IsLocalRing.maximalIdeal Rₚ ^ n).under R = p ^ n := by
  ext
  rw [mem_comap, ← map_eq_maximalIdeal p Rₚ, ← Ideal.map_pow,
    algebraMap_mem_map_algebraMap_iff p.primeCompl Rₚ]
  refine ⟨fun ⟨m, hm, h⟩ ↦ ?_, fun h ↦ ⟨1, by simp, by simp [h]⟩⟩
  exact (IsMaximal.mul_mem_pow _ h).resolve_left (mem_primeCompl_iff.mp hm)

@[deprecated (since := "2026-04-09")] alias comap_maximalIdeal_pow := under_maximalIdeal_pow

section isomorphisms

attribute [local instance] Ideal.Quotient.field

variable {S R : Type*} [CommRing R] (p : Ideal R) [p.IsMaximal]
variable (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]

open IsLocalRing

/-- The isomorphism `R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ`, where `Rₚ` satisfies
`IsLocalization.AtPrime Rₚ p`. In particular, localization preserves the residue field. -/
noncomputable
/-
**IsLocalization.AtPrime.equivQuotMaximalIdeal** 是 Mathlib 中的一个定义，位于命名空间 `IsLoca
lization.AtPrime`。
形式化陈述：equivQuotMaximalIdeal : R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
def equivQuotMaximalIdeal : R ⧸ p ≃+* Rₚ ⧸ maximalIdeal Rₚ := by
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap R (Rₚ ⧸ maximalIdeal Rₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq R Rₚ, ← RingHom.comap_ker, ← under_def,
      Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, IsLocalization.AtPrime.under_maximalIdeal Rₚ p]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    obtain ⟨s', hs⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p s)⁻¹
    simp only [IsScalarTower.algebraMap_eq R Rₚ (Rₚ ⧸ _),
      Ideal.Quotient.algebraMap_eq, RingHom.comp_apply]
    use x * s'
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    have : algebraMap R Rₚ s ∉ maximalIdeal Rₚ := by
      rw [← Ideal.mem_under, IsLocalization.AtPrime.under_maximalIdeal Rₚ p]
      exact s.prop
    refine ((inferInstance : (maximalIdeal Rₚ).IsPrime).mem_or_mem ?_).resolve_left this
    rw [mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_mul_cancel_left,
      ← map_mul, ← map_sub, ← Ideal.mem_under, under_maximalIdeal Rₚ p,
      mul_left_comm, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul, hs,
      mul_inv_cancel₀, mul_one, sub_self]
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact s.prop

@[simp]
/-
**IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk** 是 Mathlib 中的一个定理，位于命名空
间 `IsLocalization.AtPrime`。
形式化陈述：equivQuotMaximalIdeal_apply_mk (x : R) : equivQuotMaximalIdeal p Rₚ (Ideal
.Quotient.mk _ x) = (Ideal.Quotient.mk _ (algebraMap R Rₚ x))
参数：x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem equivQuotMaximalIdeal_apply_mk (x : R) :
    equivQuotMaximalIdeal p Rₚ (Ideal.Quotient.mk _ x) =
      (Ideal.Quotient.mk _ (algebraMap R Rₚ x)) := rfl

@[simp]
/-
**IsLocalization.AtPrime.equivQuotMaximalIdeal_symm_apply_mk** 是 Mathlib 中的一个定理，
位于命名空间 `IsLocalization.AtPrime`。
形式化陈述：equivQuotMaximalIdeal_symm_apply_mk (x : R) (s : p.primeCompl) : (equivQuo
tMaximalIdeal p Rₚ).symm (Ideal.Quotient.mk _ (IsLocalization.mk' Rₚ x s)) = (Id
eal.Quotient.mk p x) * (Ideal.Quotient.mk p s)⁻¹
参数：x : R；s : p.primeCompl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_primeCompl_iff`：mem_primeCompl_iff {P : Ideal α} [P.IsPrime] {
x : α} : x in P.primeCompl ↔ x ∉ P
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `RingEquiv.map_ne_zero_iff`：map_ne_zero_iff : f x != 0 ↔ x != 0
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `RingEquiv.symm_apply_eq`：symm_apply_eq (e : R ≃+* S) {x : S} {y : R} : e
.symm x = y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
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
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk`：equivQuotMaximalI
deal_apply_mk (x : R) : equivQuotMaximalIdeal p Rₚ (Ideal.Quotient.mk _ x) = (Id
eal.Quotient.mk _ (algebraMap R Rₚ x))
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `IsLocalization.mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {M : S
ubmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [i
nst_3 : IsLoc…
· 使用定理 `Ideal.Quotient.mk_algebraMap`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : C
ommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst_
3 : I.IsTwoSided] …
-/
theorem equivQuotMaximalIdeal_symm_apply_mk (x : R) (s : p.primeCompl) :
    (equivQuotMaximalIdeal p Rₚ).symm (Ideal.Quotient.mk _ (IsLocalization.mk' Rₚ x s)) =
        (Ideal.Quotient.mk p x) * (Ideal.Quotient.mk p s)⁻¹ := by
  have h₁ : Ideal.Quotient.mk p ↑s ≠ 0 := by
    simpa [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using Ideal.mem_primeCompl_iff.mp s.prop
  have h₂ : equivQuotMaximalIdeal p Rₚ (Ideal.Quotient.mk p ↑s) ≠ 0 := by
    rwa [RingEquiv.map_ne_zero_iff]
  rw [RingEquiv.symm_apply_eq, ← mul_left_inj' h₂, map_mul, mul_assoc, ← map_mul,
    inv_mul_cancel₀ h₁, map_one, mul_one, equivQuotMaximalIdeal_apply_mk, ← map_mul,
    mk'_spec, Ideal.Quotient.mk_algebraMap, equivQuotMaximalIdeal_apply_mk,
    Ideal.Quotient.mk_algebraMap]

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism `R ⧸ p ^ n ≃ₐ[R] Rₚ ⧸ maximalIdeal Rₚ ^ n`, where `Rₚ` satisfies
`IsLocalization.AtPrime Rₚ p`. -/
noncomputable
/-
**IsLocalization.AtPrime.equivQuotMaximalIdealPow** 是 Mathlib 中的一个定义，位于命名空间 `IsL
ocalization.AtPrime`。
形式化陈述：equivQuotMaximalIdealPow (n : Nat) : (R ⧸ p ^ n) ≃ₐ[R] Rₚ ⧸ IsLocalRing.ma
ximalIdeal Rₚ ^ n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def equivQuotMaximalIdealPow (n : ℕ) : (R ⧸ p ^ n) ≃ₐ[R] Rₚ ⧸ IsLocalRing.maximalIdeal Rₚ ^ n := by
  refine AlgEquiv.ofAlgHom (Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) ?_) ?_ ?_ ?_
  · simp_rw [ofId_apply, ← RingHom.mem_ker, ← SetLike.le_def]
    rw [← Quotient.mk_comp_algebraMap, ← RingHom.comap_ker, mk_ker, ← under_def,
      under_maximalIdeal_pow p]
  · refine Ideal.Quotient.liftₐ _
      (IsLocalization.liftAlgHom (f := Ideal.Quotient.mkₐ R (p ^ n)) fun (u : p.primeCompl) ↦
        Ideal.Quotient.isUnit_mk_pow_of_notMem _ <| mem_primeCompl_iff.mp u.prop) fun x hx ↦ ?_
    obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl x
    rw [IsLocalization.mk'_mem_iff, ← Ideal.mem_under, under_maximalIdeal_pow p] at hx
    simpa [lift_mk', Quotient.eq_zero_iff_mem] using hx
  · rw [← AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective _ _)]
    exact IsLocalization.algHom_ext (W := p.primeCompl) (A := R) (by ext)
  · rw [← AlgHom.cancel_right (Ideal.Quotient.mkₐ_surjective _ _)]
    ext

@[simp]
/-
**IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk** 是 Mathlib 中的一个定理，位于
命名空间 `IsLocalization.AtPrime`。
形式化陈述：equivQuotMaximalIdealPow_apply_mk (n : Nat) (x : R) : equivQuotMaximalIdea
lPow p Rₚ n (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (algebraMap R Rₚ x)
参数：n : Nat；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem equivQuotMaximalIdealPow_apply_mk (n : ℕ) (x : R) :
    equivQuotMaximalIdealPow p Rₚ n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (algebraMap R Rₚ x) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**IsLocalization.AtPrime.equivQuotMaximalIdealPow_symm_apply_mk_mul** 是 Mathlib 
中的一个定理，位于命名空间 `IsLocalization.AtPrime`。
形式化陈述：equivQuotMaximalIdealPow_symm_apply_mk_mul (n : Nat) (x : R) (s : p.primeC
ompl) : (equivQuotMaximalIdealPow p Rₚ n).symm (Ideal.Quotient.mk _ (IsLocalizat
ion.mk' Rₚ x s)) * Ideal.Quotient.mk (p ^ n) s = Ideal.Quotient.mk (p ^ n) x
参数：n : Nat；x : R；s : p.primeCompl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquiv.ofAlgHom_symm_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `IsLocalization.lift_mk'`：lift_mk' (x y) : lift hg (mk' S x y) = g x * ↑(
IsUnit.liftRight (g.toMonoidHom.domRestrict M) hg y)⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivQuotMaximalIdealPow_symm_apply_mk_mul (n : ℕ) (x : R) (s : p.primeCompl) :
    (equivQuotMaximalIdealPow p Rₚ n).symm (Ideal.Quotient.mk _ (IsLocalization.mk' Rₚ x s)) *
      Ideal.Quotient.mk (p ^ n) s = Ideal.Quotient.mk (p ^ n) x := by
  simp [equivQuotMaximalIdealPow, lift_mk', IsUnit.liftRight_apply, mul_assoc]

variable {Sₚ : Type*} [CommRing S] [Algebra R S] [CommRing Sₚ] [Algebra S Sₚ] [Algebra R Sₚ]
variable [Algebra Rₚ Sₚ] [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
variable [IsScalarTower R S Sₚ]

local notation "pS" => Ideal.map (algebraMap R S) p
local notation "pSₚ" => Ideal.map (algebraMap Rₚ Sₚ) (maximalIdeal Rₚ)
/-
**IsLocalization.AtPrime.under_map_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizat
ion.AtPrime`。
形式化陈述：under_map_eq_map : (Ideal.map (algebraMap R Sₚ) p).under S = pS
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_map`：map_map {T : Type*} [Semiring T] {I : Ideal R} (f : R ->+
* S) (g : S ->+* T) : (I.map f).map g = I.map (g.comp f)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Ideal.le_comap_map`：le_comap_map : I <= (I.map f).comap f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.mem_map_algebraMap_iff`：mem_map_algebraMap_iff {I : Ideal
 R} {z} : z in Ideal.map (algebraMap R S) I ↔ exists x : I × M, z * algebraMap R
 S x.2 = algebraMap R S x.1
· 使用定理 `IsLocalization.eq_iff_exists`：eq_iff_exists {x y} : algebraMap R S x = a
lgebraMap R S y ↔ exists c : M, ↑c * x = ↑c * y
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Submonoid.coe_mul`：coe_mul (x y : S) : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
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
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
（共 39 条，此处仅展示前 30 条）
-/
lemma under_map_eq_map : (Ideal.map (algebraMap R Sₚ) p).under S = pS := by
  rw [IsScalarTower.algebraMap_eq R S Sₚ, ← Ideal.map_map, eq_comm]
  apply Ideal.le_comap_map.antisymm
  intro x hx
  obtain ⟨α, hα, hαx⟩ : ∃ α ∉ p, α • x ∈ pS := by
    have ⟨⟨y, s⟩, hy⟩ := (IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ).mp hx
    rw [← map_mul,
      IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid S p.primeCompl)] at hy
    obtain ⟨c, hc⟩ := hy
    obtain ⟨α, hα, e⟩ := (c * s).prop
    refine ⟨α, hα, ?_⟩
    rw [Algebra.smul_def, e, Submonoid.coe_mul, mul_assoc, mul_comm _ x, hc]
    exact Ideal.mul_mem_left _ _ y.prop
  obtain ⟨β, γ, hγ, hβ⟩ : ∃ β γ, γ ∈ p ∧ β * α = 1 + γ := by
    obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
    refine ⟨β, β * α - 1, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
        map_mul, hβ, inv_mul_cancel₀, sub_self]
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    · rw [add_sub_cancel]
  have := Ideal.mul_mem_left _ (algebraMap _ _ β) hαx
  rw [← Algebra.smul_def, smul_smul, hβ, add_smul, one_smul] at this
  refine (Submodule.add_mem_iff_left pS ?_).mp this
  rw [Algebra.smul_def]
  apply Ideal.mul_mem_right
  exact Ideal.mem_map_of_mem _ hγ

@[deprecated (since := "2026-04-09")] alias comap_map_eq_map := under_map_eq_map

variable [IsScalarTower R Rₚ Sₚ]

variable (S Sₚ) in
/--
The isomorphism `S ⧸ pS ≃+* Sₚ ⧸ p·Sₚ`, where `Sₚ` is the localization of `S` at the (image) of
the complement of `p`
-/
/-
**IsLocalization.AtPrime.equivQuotientMapMaximalIdeal** 是 Mathlib 中的一个定义，位于命名空间 
`IsLocalization.AtPrime`。
形式化陈述：equivQuotientMapMaximalIdeal : S ⧸ pS ≃+* Sₚ ⧸ pSₚ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism `S ⧸ pS ≃+* Sₚ ⧸ p·Sₚ`, where `Sₚ` is the localization of `S` at
 the (image) of
the complement of `p`
-/
noncomputable def equivQuotientMapMaximalIdeal : S ⧸ pS ≃+* Sₚ ⧸ pSₚ := by
  haveI h : pSₚ = Ideal.map (algebraMap S Sₚ) pS := by
    rw [← map_eq_maximalIdeal p, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  refine (Ideal.quotEquivOfEq ?_).trans
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap S (Sₚ ⧸ pSₚ)) ?_)
  · rw [IsScalarTower.algebraMap_eq S Sₚ, Ideal.Quotient.algebraMap_eq, ← RingHom.comap_ker,
      Ideal.mk_ker, h, Ideal.map_map, ← IsScalarTower.algebraMap_eq, ← under_def, under_map_eq_map]
  · intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
      (Algebra.algebraMapSubmonoid S p.primeCompl) x
    obtain ⟨α, hα : α ∉ p, e⟩ := s.prop
    obtain ⟨β, γ, hγ, hβ⟩ : ∃ β γ, γ ∈ p ∧ α * β = 1 + γ := by
      obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective (I := p) (Ideal.Quotient.mk p α)⁻¹
      refine ⟨β, α * β - 1, ?_, ?_⟩
      · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one,
          map_mul, hβ, mul_inv_cancel₀, sub_self]
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      · rw [add_sub_cancel]
    use β • x
    rw [IsScalarTower.algebraMap_eq S Sₚ (Sₚ ⧸ pSₚ), Ideal.Quotient.algebraMap_eq,
      RingHom.comp_apply, ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    rw [h, IsLocalization.mem_map_algebraMap_iff
      (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    refine ⟨⟨⟨γ • x, ?_⟩, s⟩, ?_⟩
    · rw [Algebra.smul_def]
      apply Ideal.mul_mem_right
      exact Ideal.mem_map_of_mem _ hγ
    simp only
    rw [mul_comm, mul_sub, IsLocalization.mul_mk'_eq_mk'_of_mul,
      IsLocalization.mk'_mul_cancel_left, ← map_mul, ← e, ← Algebra.smul_def, smul_smul,
      hβ, ← map_sub, add_smul, one_smul, add_comm x, add_sub_cancel_right]

end isomorphisms

/-
**IsLocalization.AtPrime.map_eq_top_of_not_le** 是 Mathlib 中的一个引理，位于命名空间 `IsLocal
ization.AtPrime`。
形式化陈述：map_eq_top_of_not_le {I : Ideal R} {p : Ideal R} [p.IsPrime] [IsLocalizati
on.AtPrime S p] (hle : ¬ I <= p) : Ideal.map (algebraMap R S) I = ⊤
参数：hle : ¬ I <= p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.map_eq_top_of_not_subset`：map_eq_top_of_not_subset {I : I
deal R} (hle : ¬ (I : Set R) subseteq Mᶜ) : Ideal.map (algebraMap R S) I = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
-/
lemma map_eq_top_of_not_le {I : Ideal R} {p : Ideal R} [p.IsPrime] [IsLocalization.AtPrime S p]
    (hle : ¬ I ≤ p) : Ideal.map (algebraMap R S) I = ⊤ := by
  apply IsLocalization.map_eq_top_of_not_subset p.primeCompl
  simpa [SetLike.le_def, Set.not_subset_iff_exists_mem_notMem] using hle

end IsLocalization.AtPrime

