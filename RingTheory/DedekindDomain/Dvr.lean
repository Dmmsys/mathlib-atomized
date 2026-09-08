/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio, Yongle Hu
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Dedekind domains

This file defines an equivalent notion of a Dedekind domain (or Dedekind ring),
namely a Noetherian integral domain where the localization at every nonzero prime ideal is a DVR.

## Main definitions

- `IsDedekindDomainDvr` alternatively defines a Dedekind domain as an integral domain that
  is Noetherian, and the localization at every nonzero prime ideal is a DVR.

## Main results
- `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` shows that
  `IsDedekindDomain` implies the localization at each nonzero prime ideal is a DVR.
- `IsDedekindDomain.isDedekindDomainDvr` is one direction of the equivalence of definitions
  of a Dedekind domain

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

public section


variable (A : Type*) [CommRing A] [IsDomain A]

open scoped nonZeroDivisors Polynomial

/-- A Dedekind domain is an integral domain that is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `IsDedekindDomain`.
-/
/-
**IsDedekindDomainDvr** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) → [inst : CommRing A] → [IsDomain A] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Dedekind domain is an integral domain that is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `IsDedekindDomain`.
-/
class IsDedekindDomainDvr : Prop extends IsNoetherian A A where
  is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : Ideal A), ∀ _ : P.IsPrime,
    IsDiscreteValuationRing (Localization.AtPrime P)

/-- Localizing a domain of Krull dimension `≤ 1` gives another ring of Krull dimension `≤ 1`.

Note that the same proof can/should be generalized to preserving any Krull dimension,
once we have a suitable definition.
-/
/-
**Ring.DimensionLEOne.localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ring.DimensionLEOne.localization {R : Type*} (Rₘ : Type*) [CommRing R] [Is
Domain R] [CommRing Rₘ] [Algebra R Rₘ] {M : Submonoid R} [IsLocalization M Rₘ] (
hM : M <= R⁰) [h : Ring.DimensionLEOne R] : Ring.DimensionLEOne Rₘ
参数：Rₘ : Type*；hM : M <= R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isMaximal_def`：isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoato
m I
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.maximal_of_no_maximal`：maximal_of_no_maximal {P : Ideal α} (hmax :
 forall m : Ideal α, P < m -> ¬IsMaximal m) (J : Ideal α) (hPJ : P < J) : J = ⊤
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Ring.DimensionLEOne.not_lt_lt`：∀ {R : Type u_1} [inst : CommRing R] [Rin
g.DimensionLEOne R] (p₀ p₁ p₂ : Ideal R) [hp₁ : p₁.IsPrime] [hp₂ : p₂.IsPrime], 
  ¬(p₀ < p₁ ∧ p₁ < …
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalization.bot_lt_under_prime`：bot_lt_under_prime [IsDomain R] (hM :
 M <= R⁰) (p : Ideal S) [hpp : p.IsPrime] (hp0 : p != ⊥) : ⊥ < p.under R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y

--- 原说明 ---
Localizing a domain of Krull dimension `≤ 1` gives another ring of Krull dimensi
on `≤ 1`.

Note that the same proof can/should be generalized to preserving any Krull dimen
sion,
once we have a suitable definition.
-/
theorem Ring.DimensionLEOne.localization {R : Type*} (Rₘ : Type*) [CommRing R] [IsDomain R]
    [CommRing Rₘ] [Algebra R Rₘ] {M : Submonoid R} [IsLocalization M Rₘ] (hM : M ≤ R⁰)
    [h : Ring.DimensionLEOne R] : Ring.DimensionLEOne Rₘ := ⟨by
  intro p hp0 hpp
  refine Ideal.isMaximal_def.mpr ⟨hpp.ne_top, Ideal.maximal_of_no_maximal fun P hpP hPm => ?_⟩
  have hpP' : (⟨p, hpp⟩ : { p : Ideal Rₘ // p.IsPrime }) < ⟨P, hPm.isPrime⟩ := hpP
  rw [← (IsLocalization.orderIsoOfPrime M Rₘ).lt_iff_lt] at hpP'
  refine h.not_lt_lt ⊥ (p.under R) (P.under R) ⟨?_, hpP'⟩
  exact IsLocalization.bot_lt_under_prime _ _ hM _ hp0⟩

set_option linter.overlappingInstances false

/-- The localization of a Dedekind domain is a Dedekind domain. -/
/-
**IsLocalization.isDedekindDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.isDedekindDomain [IsDedekindDomain A] {M : Submonoid A} (hM
 : M <= A⁰) (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalizat
ion M Aₘ] : IsDedekindDomain Aₘ
参数：hM : M <= A⁰；Aₘ : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsFractionRing.to_map_eq_zero_iff`：to_map_eq_zero_iff {x : R} : algebraM
ap R K x = 0 ↔ x = 0
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x
· 使用定理 `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization`：isFractionR
ing_of_isDomain_of_isLocalization [IsDomain R] (S T : Type*) [CommRing S] [CommR
ing T] [Algebra R S] [Algebra R T] [Algebra S T] …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isDedekindDomain_iff`：isDedekindDomain_iff (K : Type*) [CommRing K] [Alg
ebra A K] [IsFractionRing A K] : IsDedekindDomain A ↔ IsDomain A ∧ IsNoetherianR
ing A ∧ Di…
· 使用定理 `IsLocalization.isNoetherianRing`：isNoetherianRing (h : IsNoetherianRing 
R) : IsNoetherianRing S
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `Ring.DimensionLEOne.localization`：Ring.DimensionLEOne.localization {R : 
Type*} (Rₘ : Type*) [CommRing R] [IsDomain R] [CommRing Rₘ] [Algebra R Rₘ] {M : 
Submonoid R} [IsLocali…
· 使用定理 `IsDedekindRing.toDimensionLEOne`：∀ {A : Type u_2} {inst : CommRing A} [s
elf : IsDedekindRing A], Ring.DimensionLEOne A
· 使用定理 `IsIntegral.exists_multiple_integral_of_isLocalization`：IsIntegral.exists
_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsScalarTower R Rₘ S] (x : 
S) (hx : IsIntegral Rₘ x) : exists m : M, I…
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.lift_mk'_spec`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] {P : Type u_3} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x

--- 原说明 ---
The localization of a Dedekind domain is a Dedekind domain.
-/
theorem IsLocalization.isDedekindDomain [IsDedekindDomain A] {M : Submonoid A} (hM : M ≤ A⁰)
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ] :
    IsDedekindDomain Aₘ := by
  have h : ∀ y : M, IsUnit (algebraMap A (FractionRing A) y) := by
    rintro ⟨y, hy⟩
    exact IsUnit.mk0 _ (mt IsFractionRing.to_map_eq_zero_iff.mp (nonZeroDivisors.ne_zero (hM hy)))
  let : Algebra Aₘ (FractionRing A) := RingHom.toAlgebra (IsLocalization.lift h)
  have : IsScalarTower A Aₘ (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq h x).symm
  have : IsFractionRing Aₘ (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M _ _
  refine (isDedekindDomain_iff _ (FractionRing A)).mpr ⟨?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact IsLocalization.isNoetherianRing M _ inferInstance
  · exact Ring.DimensionLEOne.localization Aₘ hM
  · intro x hx
    obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization M _
    obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff _).mp IsDedekindRing.toIsIntegralClosure hy
    refine ⟨IsLocalization.mk' Aₘ z ⟨y, y_mem⟩, (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_⟩
    rw [hz, ← Algebra.smul_def]
    rfl

/-- The localization of a Dedekind domain at every nonzero prime ideal is a Dedekind domain. -/
/-
**IsLocalization.AtPrime.isDedekindDomain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.AtPrime.isDedekindDomain [IsDedekindDomain A] (P : Ideal A)
 [P.IsPrime] (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocaliza
tion.AtPrime Aₘ P] : IsDedekindDomain Aₘ
参数：P : Ideal A；Aₘ : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isDedekindDomain`：IsLocalization.isDedekindDomain [IsDede
kindDomain A] {M : Submonoid A} (hM : M <= A⁰) (Aₘ : Type*) [CommRing Aₘ] [IsDom
ain Aₘ] [Algebra A Aₘ…
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α

--- 原说明 ---
The localization of a Dedekind domain at every nonzero prime ideal is a Dedekind
 domain.
-/
theorem IsLocalization.AtPrime.isDedekindDomain [IsDedekindDomain A] (P : Ideal A) [P.IsPrime]
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] :
    IsDedekindDomain Aₘ :=
  IsLocalization.isDedekindDomain A P.primeCompl_le_nonZeroDivisors Aₘ
/-
**Localization.AtPrime.isDedekindDomain** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Localization.AtPrime.isDedekindDomain [IsDedekindDomain A] (P : Ideal A) [
P.IsPrime] : IsDedekindDomain (Localization.AtPrime P)
参数：P : Ideal A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.AtPrime.isDedekindDomain`：IsLocalization.AtPrime.isDedeki
ndDomain [IsDedekindDomain A] (P : Ideal A) [P.IsPrime] (Aₘ : Type*) [CommRing A
ₘ] [IsDomain Aₘ] [Algebra A A…
-/
instance Localization.AtPrime.isDedekindDomain [IsDedekindDomain A] (P : Ideal A) [P.IsPrime] :
    IsDedekindDomain (Localization.AtPrime P) :=
  IsLocalization.AtPrime.isDedekindDomain A P _
/-
**IsLocalization.AtPrime.not_isField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.AtPrime.not_isField {P : Ideal A} (hP : P != ⊥) [pP : P.IsP
rime] (Aₘ : Type*) [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : 
¬ IsField Aₘ
参数：hP : P != ⊥；Aₘ : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalization.AtPrime.to_map_mem_maximal_iff`：to_map_mem_maximal_iff (x
 : R) (h : IsLocalRing S
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem IsLocalization.AtPrime.not_isField {P : Ideal A} (hP : P ≠ ⊥) [pP : P.IsPrime] (Aₘ : Type*)
    [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : ¬ IsField Aₘ := by
  intro h
  let := h.toField
  obtain ⟨x, x_mem, x_ne⟩ := P.ne_bot_iff.mp hP
  exact
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Aₘ P _).mpr x_mem)
        (isUnit_iff_ne_zero.mpr
          ((map_ne_zero_iff (algebraMap A Aₘ)
                (IsLocalization.injective Aₘ P.primeCompl_le_nonZeroDivisors)).mpr
            x_ne)))

/-- In a Dedekind domain, the localization at every nonzero prime ideal is a DVR. -/
/-
**IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain [IsDedek
indDomain A] {P : Ideal A} (hP : P != ⊥) [pP : P.IsPrime] (Aₘ : Type*) [CommRing
 Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : IsDiscreteValu
ationRing Aₘ
参数：hP : P != ⊥；Aₘ : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalization.isNoetherianRing`：isNoetherianRing (h : IsNoetherianRing 
R) : IsNoetherianRing S
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `IsLocalization.AtPrime.not_isField`：IsLocalization.AtPrime.not_isField {
P : Ideal A} (hP : P != ⊥) [pP : P.IsPrime] (Aₘ : Type*) [CommRing Aₘ] [Algebra 
A Aₘ] [IsLocalization.At…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDiscreteValuationRing.TFAE`：IsDiscreteValuationRing.TFAE [IsNoetherian
Ring R] [IsLocalRing R] [IsDomain R] (h : ¬IsField R) : List.TFAE [IsDiscreteVal
uationRing R, Valu…
· 使用定理 `IsLocalization.AtPrime.isDedekindDomain`：IsLocalization.AtPrime.isDedeki
ndDomain [IsDedekindDomain A] (P : Ideal A) [P.IsPrime] (Aₘ : Type*) [CommRing A
ₘ] [IsDomain Aₘ] [Algebra A A…

--- 原说明 ---
In a Dedekind domain, the localization at every nonzero prime ideal is a DVR.
-/
theorem IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain [IsDedekindDomain A]
    {P : Ideal A} (hP : P ≠ ⊥) [pP : P.IsPrime] (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ]
    [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : IsDiscreteValuationRing Aₘ := by
  let : IsNoetherianRing Aₘ :=
    IsLocalization.isNoetherianRing P.primeCompl _ IsDedekindRing.toIsNoetherian
  let : IsLocalRing Aₘ := IsLocalization.AtPrime.isLocalRing Aₘ P
  have hnf := IsLocalization.AtPrime.not_isField A hP Aₘ
  exact
    ((IsDiscreteValuationRing.TFAE Aₘ hnf).out 0 2).mpr
      (IsLocalization.AtPrime.isDedekindDomain A P _)

/-- Dedekind domains, in the sense of Noetherian integrally closed domains of Krull dimension ≤ 1,
are also Dedekind domains in the sense of Noetherian domains where the localization at every
nonzero prime ideal is a DVR. -/
/-
**IsDedekindDomain.isDedekindDomainDvr** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsDedekindDomain.isDedekindDomainDvr [IsDedekindDomain A] : IsDedekindDoma
inDvr A where is_dvr_at_nonzero_prime
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`：IsLoc
alization.AtPrime.isDiscreteValuationRing_of_dedekind_domain [IsDedekindDomain A
] {P : Ideal A} (hP : P != ⊥) [pP : P.IsPrime] (Aₘ : Ty…

--- 原说明 ---
Dedekind domains, in the sense of Noetherian integrally closed domains of Krull 
dimension ≤ 1,
are also Dedekind domains in the sense of Noetherian domains where the localizat
ion at every
nonzero prime ideal is a DVR.
-/
instance IsDedekindDomain.isDedekindDomainDvr [IsDedekindDomain A] : IsDedekindDomainDvr A where
  is_dvr_at_nonzero_prime := fun _ hP _ =>
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _
/-
**IsDedekindDomainDvr.ring_dimensionLEOne** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsDedekindDomainDvr.ring_dimensionLEOne [h : IsDedekindDomainDvr A] : Ring
.DimensionLEOne A where maximalOfPrime
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `LE.le.disjoint_compl_left`：LE.le.disjoint_compl_left (h : b <= a) : Disj
oint aᶜ b
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `IsLocalization.injective`：∀ {R : Type u_1} [inst : CommRing R] {M : Subm
onoid R} (S : Type u_2) [inst_1 : CommRing S] [inst_2 : Algebra R S]   [IsLocali
zation M S], M…
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用定理 `ne_bot_of_le_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Or
derBot α] {a b : α}, b ≠ ⊥ → b ≤ a → a ≠ ⊥
· 使用定理 `IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime`：iff_pid_with_one
_nonzero_prime (R : Type u) [CommRing R] [IsDomain R] : IsDiscreteValuationRing 
R ↔ IsPrincipalIdealRing R ∧ exists! P : Ide…
· 使用定理 `IsDedekindDomainDvr.is_dvr_at_nonzero_prime`：∀ {A : Type u_1} {inst : Co
mmRing A} {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A] (P : Ideal A),   
P ≠ ⊥ → ∀ (x : P.IsPrime), IsDisc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.val_inj`：val_inj {a b : Subtype p} : a.val = b.val ↔ a = b
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance IsDedekindDomainDvr.ring_dimensionLEOne [h : IsDedekindDomainDvr A] :
    Ring.DimensionLEOne A where
  maximalOfPrime := by
    intro p hp hpp
    rcases p.exists_le_maximal (Ideal.IsPrime.ne_top hpp) with ⟨q, hq, hpq⟩
    let f := (IsLocalization.orderIsoOfPrime q.primeCompl (Localization.AtPrime q)).symm
    let P := f ⟨p, hpp, hpq.disjoint_compl_left⟩
    let Q := f ⟨q, hq.isPrime, Set.disjoint_left.mpr fun _ a => a⟩
    have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
      IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors
    have hp1 : P.1 ≠ ⊥ := fun x => hp ((p.map_eq_bot_iff_of_injective hinj).mp x)
    have hq1 : Q.1 ≠ ⊥ :=
      fun x => (ne_bot_of_le_ne_bot hp hpq) ((q.map_eq_bot_iff_of_injective hinj).mp x)
    rcases (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime (Localization.AtPrime q)).mp
      (h.is_dvr_at_nonzero_prime q (ne_bot_of_le_ne_bot hp hpq) hq.isPrime) with ⟨_, huq⟩
    rw [show p = q from Subtype.val_inj.mpr <| f.injective <|
      Subtype.val_inj.mp (huq.unique ⟨hp1, P.2⟩ ⟨hq1, Q.2⟩)]
    exact hq
/-
**IsDedekindDomainDvr.isIntegrallyClosed** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsDedekindDomainDvr.isIntegrallyClosed [h : IsDedekindDomainDvr A] : IsInt
egrallyClosed A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegrallyClosed.of_localization_maximal`：IsIntegrallyClosed.of_locali
zation_maximal [IsDomain R] (h : forall p : Ideal R, p != ⊥ -> [p.IsMaximal] -> 
IsIntegrallyClosed (Localization…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime`：iff_pid_with_one
_nonzero_prime (R : Type u) [CommRing R] [IsDomain R] : IsDiscreteValuationRing 
R ↔ IsPrincipalIdealRing R ∧ exists! P : Ide…
· 使用定理 `IsDedekindDomainDvr.is_dvr_at_nonzero_prime`：∀ {A : Type u_1} {inst : Co
mmRing A} {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A] (P : Ideal A),   
P ≠ ⊥ → ∀ (x : P.IsPrime), IsDisc…
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `IsDedekindRing.toIsIntegralClosure`：∀ {A : Type u_2} {inst : CommRing A}
 [self : IsDedekindRing A], IsIntegralClosure A A (FractionRing A)
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
-/
instance IsDedekindDomainDvr.isIntegrallyClosed [h : IsDedekindDomainDvr A] :
    IsIntegrallyClosed A :=
  IsIntegrallyClosed.of_localization_maximal <| fun p hp0 hpm ↦
    let ⟨_, _⟩ := (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
      (Localization.AtPrime p)).mp (h.is_dvr_at_nonzero_prime p hp0 hpm.isPrime)
    inferInstance

/-- If an integral domain is Noetherian, and the localization at every nonzero prime is
a discrete valuation ring, then it is a Dedekind domain. -/
/-
**IsDedekindDomainDvr.isDedekindDomain** 是 Mathlib 中的一个定理，位于命名空间 `IsDedekindDoma
inDvr`。
形式化陈述：∀ (A : Type u_1) [inst : CommRing A] [inst_1 : IsDomain A] [IsDedekindDoma
inDvr A], IsDedekindDomain A
参数：A : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A

--- 原说明 ---
If an integral domain is Noetherian, and the localization at every nonzero prime
 is
a discrete valuation ring, then it is a Dedekind domain.
-/
instance IsDedekindDomainDvr.isDedekindDomain [IsDedekindDomainDvr A] : IsDedekindDomain A where
