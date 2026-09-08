/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
module

public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Kummer-Dedekind theorem

This file proves the Kummer-Dedekind theorem on the splitting of prime ideals in an extension of
the ring of integers. This states the following: assume we are given
  - A prime ideal `I` of Dedekind domain `R`
  - An `R`-algebra `S` that is a Dedekind Domain
  - An `α : S` that is integral over `R` with minimal polynomial `f`

If the conductor `𝓒` of `x` is such that `𝓒 ∩ R` is coprime to `I` then the prime
factorisations of `I * S` and `f mod I` have the same shape, i.e. they have the same number of
prime factors, and each prime factors of `I * S` can be paired with a prime factor of `f mod I` in
a way that ensures multiplicities match (in fact, this pairing can be made explicit
with a formula).

## Main definitions

* `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` : The bijection in the Kummer-Dedekind
  theorem. This is the pairing between the prime factors of `I * S` and the prime factors of
  `f mod I`.

## Main results

* `normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map` : The Kummer-Dedekind
  theorem.
* `Ideal.irreducible_map_of_irreducible_minpoly` : `I.map (algebraMap R S)` is irreducible if
  `(map (Ideal.Quotient.mk I) (minpoly R pb.gen))` is irreducible, where `pb` is a power basis
  of `S` over `R`.
  * `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span` : Let `Q` be a lift of
    factor of the minimal polynomial of `x`, a generator of `S` over `R`, taken
    `mod I`. Then (the reduction of) `Q` corresponds via
    `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` to
    `span (I.map (algebraMap R S) ∪ {Q.aeval x})`.

## TODO

* Prove the converse of `Ideal.irreducible_map_of_irreducible_minpoly`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/

@[expose] public section


variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : S} {I : Ideal R}

open Ideal Polynomial DoubleQuot UniqueFactorizationMonoid Algebra RingHom

namespace KummerDedekind

variable [IsDomain R] [IsIntegrallyClosed R]
variable [IsDedekindDomain S]
variable [Module.IsTorsionFree R S]

attribute [local instance] Ideal.Quotient.field

/--
The isomorphism of rings between `S / I` and `(R / I)[X] / minpoly x` when `I`
and `(conductor R x) ∩ R` are coprime.
-/
/-
**KummerDedekind.quotMapEquivQuotQuotMap** 是 Mathlib 中的一个定义，位于命名空间 `KummerDedeki
nd`。
形式化陈述：quotMapEquivQuotQuotMap (hx : (conductor R x).comap (algebraMap R S) ⊔ I =
 ⊤) (hx' : IsIntegral R x) : S ⧸ I.map (algebraMap R S) ≃+* (R ⧸ I)[X] ⧸ span {(
minpoly R x).map (Ideal.Quotient.mk I)}
参数：hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤；hx' : IsIntegral R x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.adjoin.powerBasis'`：Algebra.adjoin.powerBasis'_minpoly_gen [IsDo
main R] [IsDomain S] [IsTorsionFree R S] [IsIntegrallyClosed R] {x : S} (hx' : I
sIntegral R x) :…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A

--- 原说明 ---
The isomorphism of rings between `S / I` and `(R / I)[X] / minpoly x` when `I`
and `(conductor R x) ∩ R` are coprime.
-/
noncomputable def quotMapEquivQuotQuotMap (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    S ⧸ I.map (algebraMap R S) ≃+* (R ⧸ I)[X] ⧸ span {(minpoly R x).map (Ideal.Quotient.mk I)} :=
  (quotAdjoinEquivQuotMap hx (FaithfulSMul.algebraMap_injective
    (Algebra.adjoin R {x}) S)).symm.trans <|
    ((Algebra.adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap I).toRingEquiv.trans <|
    quotEquivOfEq (by rw [Algebra.adjoin.powerBasis'_minpoly_gen hx'])
/-
**KummerDedekind.quotMapEquivQuotQuotMap_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `K
ummerDedekind`。
形式化陈述：quotMapEquivQuotQuotMap_symm_apply (hx : (conductor R x).comap (algebraMap
 R S) ⊔ I = ⊤) (hx' : IsIntegral R x) (Q : R[X]) : (quotMapEquivQuotQuotMap hx h
x').symm (Q.map (Ideal.Quotient.mk I)) = Q.aeval x
参数：hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤；hx' : IsIntegral R x；Q : 
R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.injective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Injecti
ve ⇑e
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Algebra.adjoin.powerBasis'`：Algebra.adjoin.powerBasis'_minpoly_gen [IsDo
main R] [IsDomain S] [IsTorsionFree R S] [IsIntegrallyClosed R] {x : S} (hx' : I
sIntegral R x) :…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `KummerDedekind.quotMapEquivQuotQuotMap.eq_1`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {x : S} {I
 : Ideal R}   [inst_3 : IsDomain …
· 使用定理 `RingEquiv.symm_trans_apply`：symm_trans_apply (e₁ : R ≃+* S) (e₂ : S ≃+* 
S') (a : S') : (e₁.trans e₂).symm a = e₁.symm (e₂.symm a)
· 使用定理 `RingEquiv.symm_symm`：symm_symm (e : R ≃+* S) : e.symm.symm = e
· 使用定理 `RingEquiv.coe_trans`：coe_trans (e₁ : R ≃+* S) (e₂ : S ≃+* S') : (e₁.tran
s e₂ : R -> S') = e₂ ∘ e₁
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.quotEquivOfEq_symm`：quotEquivOfEq_symm (h : I = J) : (Ideal.quotEq
uivOfEq h).symm = Ideal.quotEquivOfEq h.symm
· 使用定理 `Ideal.quotEquivOfEq_mk`：quotEquivOfEq_mk (h : I = J) (x : R) : quotEquiv
OfEq h (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Subalgebra.instFaithfulSMulSubtypeMem`：∀ {R : Type u} {A : Type v} [inst
 : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {α : Type u_1}  
 [inst_3 : SMul A α] [Faith…
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.adjoin.powerBasis'_gen`：∀ {R : Type u_1} {S : Type u_2} [inst : 
CommRing R] [inst_1 : CommRing S] [inst_2 : IsDomain R] [inst_3 : Algebra R S]  
 [inst_4 : IsIntegra…
（共 33 条，此处仅展示前 30 条）
-/
lemma quotMapEquivQuotQuotMap_symm_apply (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) (Q : R[X]) :
    (quotMapEquivQuotQuotMap hx hx').symm (Q.map (Ideal.Quotient.mk I)) = Q.aeval x := by
  apply (quotMapEquivQuotQuotMap hx hx').injective
  rw [quotMapEquivQuotQuotMap, RingEquiv.symm_trans_apply,
    RingEquiv.symm_symm, RingEquiv.coe_trans, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_trans_apply, quotEquivOfEq_symm, quotEquivOfEq_mk]
  congr
  convert! (adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap_symm_apply_mk I Q
  apply (quotAdjoinEquivQuotMap hx
    (FaithfulSMul.algebraMap_injective ((adjoin R {x})) S)).injective
  simp only [RingEquiv.apply_symm_apply, adjoin.powerBasis'_gen, quotAdjoinEquivQuotMap_apply_mk,
    coe_aeval_mk_apply]

open scoped Classical in
/-- The first half of the **Kummer-Dedekind Theorem**, stating that the prime
factors of `I*S` are in bijection with those of the minimal polynomial of the generator of `S`
over `R`, taken `mod I`. -/
/-
**KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk** 是 Mathlib
 中的一个定义，位于命名空间 `KummerDedekind`。
形式化陈述：normalizedFactorsMapEquivNormalizedFactorsMinPolyMk (hI : IsMaximal I) (hI
' : I != ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsInteg
ral R x) : {J : Ideal S | J in normalizedFactors (I.map (algebraMap R S))} ≃ {d 
: (R ⧸ I)[X] | d in normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (min
poly R x))}
参数：hI : IsMaximal I；hI' : I != ⊥；hx : (conductor R x).comap (algebraMap R S) ⊔ I
 = ⊤；hx' : IsIntegral R x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The first half of the **Kummer-Dedekind Theorem**, stating that the prime
factors of `I*S` are in bijection with those of the minimal polynomial of the ge
nerator of `S`
over `R`, taken `mod I`.
-/
noncomputable def normalizedFactorsMapEquivNormalizedFactorsMinPolyMk (hI : IsMaximal I)
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    {J : Ideal S | J ∈ normalizedFactors (I.map (algebraMap R S))} ≃
      {d : (R ⧸ I)[X] |
        d ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))} := by
  refine (IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv (quotMapEquivQuotQuotMap hx hx')
    ?_ ?_).trans ?_
  · rwa [Ne, map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S), ← Ne]
  · by_contra h
    exact (show Polynomial.map (Ideal.Quotient.mk I) (minpoly R x) ≠ 0 from
      Polynomial.map_monic_ne_zero (minpoly.monic hx')) (span_singleton_eq_bot.mp h)
  · refine (Ideal.normalizedFactorsEquivSpanNormalizedFactors ?_).symm
    exact Polynomial.map_monic_ne_zero (minpoly.monic hx')

/-- The second half of the **Kummer-Dedekind Theorem**, stating that the
bijection `FactorsEquiv'` defined in the first half preserves multiplicities. -/
/-
**KummerDedekind.emultiplicity_factors_map_eq_emultiplicity** 是 Mathlib 中的一个定理，位
于命名空间 `KummerDedekind`。
形式化陈述：emultiplicity_factors_map_eq_emultiplicity (hI : IsMaximal I) (hI' : I != 
⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) 
{J : Ideal S} (hJ : J in normalizedFactors (I.map (algebraMap R S))) : emultipli
city J (I.map (algebraMap R S)) = emultiplicity (↑(normalizedFactorsMapEquivNorm
alizedFactorsMinPolyMk hI hI' hx hx' ⟨J, hJ⟩)) (Polynomial.map (Ideal.Quotient.m
k I) (minpoly R x))
参数：hI : IsMaximal I；hI' : I != ⊥；hx : (conductor R x).comap (algebraMap R S) ⊔ I
 = ⊤；hx' : IsIntegral R x；hJ : J in normalizedFactors (I.map (algebraMap R S))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk.eq_1`
：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst
_2 : Algebra R S] {x : S} {I : Ideal R}   [inst_3 : IsDomain …
· 使用定理 `Equiv.coe_trans`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} (f : α ≃ β) (g
 : β ≃ γ), ⇑(f.trans g) = ⇑g ∘ ⇑f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_
emultiplicity`：emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq
_emultiplicity {r : R} (hr : r != 0) (I : { I : Ideal R | I in normalizedFa…
· 使用定理 `IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emul
tiplicity`：normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity (hI 
: I != ⊥) (hJ : J != ⊥) (L : Ideal R) (hL : L in normalizedFactors I) :…

--- 原说明 ---
The second half of the **Kummer-Dedekind Theorem**, stating that the
bijection `FactorsEquiv'` defined in the first half preserves multiplicities.
-/
theorem emultiplicity_factors_map_eq_emultiplicity
    (hI : IsMaximal I) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) {J : Ideal S}
    (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
    emultiplicity J (I.map (algebraMap R S)) =
      emultiplicity (↑(normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' ⟨J, hJ⟩))
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
  classical
  rw [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk, Equiv.coe_trans, Function.comp_apply,
    Ideal.emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity,
    IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/-- The **Kummer-Dedekind Theorem**. -/
/-
**KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_ma
p** 是 Mathlib 中的一个定理，位于命名空间 `KummerDedekind`。
形式化陈述：normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map (hI : IsM
aximal I) (hI' : I != ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (
hx' : IsIntegral R x) : normalizedFactors (I.map (algebraMap R S)) = Multiset.ma
p (fun f => ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx')
.symm f : Ideal S)) (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (mi
npoly R x))).attach
参数：hI : IsMaximal I；hI' : I != ⊥；hx : (conductor R x).comap (algebraMap R S) ⊔ I
 = ⊤；hx' : IsIntegral R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `KummerDedekind.emultiplicity_factors_map_eq_emultiplicity`：emultiplicity
_factors_map_eq_emultiplicity (hI : IsMaximal I) (hI' : I != ⊥) (hx : (conductor
 R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : Is…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `UniqueFactorizationMonoid.normalize_normalized_factor`：normalize_normali
zed_factor {a : α} : forall x : α, x in normalizedFactors a -> normalize x = x
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors`：emul
tiplicity_eq_count_normalizedFactors {a b : R} (ha : Irreducible a) (hb : b != 0
) : emultiplicity a b = (normalizedFactors b).count (nor…
· 使用定理 `UniqueFactorizationMonoid.irreducible_of_normalized_factor`：irreducible_
of_normalized_factor {a : α} : forall x : α, x in normalizedFactors a -> Irreduc
ible x
· 使用定理 `Polynomial.map_monic_ne_zero`：map_monic_ne_zero (hp : p.Monic) [Nontrivi
al S] : p.map f != 0
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The **Kummer-Dedekind Theorem**.
-/
theorem normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map (hI : IsMaximal I)
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    normalizedFactors (I.map (algebraMap R S)) =
      Multiset.map
        (fun f =>
          ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f : Ideal S))
        (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))).attach := by
  ext J
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J ∈ normalizedFactors (I.map (algebraMap R S))
  swap
  · rw [Multiset.count_eq_zero.mpr hJ, eq_comm, Multiset.count_eq_zero, Multiset.mem_map]
    simp only [not_exists]
    rintro J' ⟨_, rfl⟩
    exact
      hJ ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm J').prop
  -- Then we just have to compare the multiplicities, which we already proved are equal.
  have := emultiplicity_factors_map_eq_emultiplicity hI hI' hx hx' hJ
  rw [emultiplicity_eq_count_normalizedFactors, emultiplicity_eq_count_normalizedFactors,
    UniqueFactorizationMonoid.normalize_normalized_factor _ hJ,
    UniqueFactorizationMonoid.normalize_normalized_factor, Nat.cast_inj] at this
  · refine this.trans ?_
    -- Get rid of the `map` by applying the equiv to both sides.
    generalize hJ' :
      (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx') ⟨J, hJ⟩ = J'
    have : ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm J' : Ideal S) =
        J := by
      rw [← hJ', Equiv.symm_apply_apply _ _, Subtype.coe_mk]
    subst this
    -- Get rid of the `attach` by applying the subtype `coe` to both sides.
    rw [Multiset.count_map_eq_count' fun f =>
        ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f :
          Ideal S),
      Multiset.count_attach]
    · exact Subtype.coe_injective.comp (Equiv.injective _)
  · exact (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' _).prop
  · exact irreducible_of_normalized_factor _
        (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' _).prop
  · exact Polynomial.map_monic_ne_zero (minpoly.monic hx')
  · exact irreducible_of_normalized_factor _ hJ
  · rwa [← bot_eq_zero, Ne,
      map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)]

set_option backward.isDefEq.respectTransparency false in
/-
**KummerDedekind.Ideal.irreducible_map_of_irreducible_minpoly** 是 Mathlib 中的一个定理
，位于命名空间 `KummerDedekind.Ideal`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] {x : S} {I : Ideal R}   [IsDomain R] [IsIntegrallyClosed 
R] [IsDedekindDomain S] [Module.IsTorsionFree R S],   I.IsMaximal →     I ≠ ⊥ → 
      Ideal.comap (algebraMap R S) (conductor R x) ⊔ I = ⊤ →         IsIntegral 
R x →           Irreducible (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))
 → Irreducible (Ideal.map (algebraMap R S) I)
参数：algebraMap R S；conductor R x；Polynomial.map (Ideal.Quotient.mk I) (minpoly R 
x)；Ideal.map (algebraMap R S) I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_irreducible`：normalizedFacto
rs_irreducible {a : α} (ha : Irreducible a) : normalizedFactors a = {normalize a
}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly
_mk_map`：normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map (hI : 
IsMaximal I) (hI' : I != ⊥) (hx : (conductor R x).comap (algebraMap R…
· 使用定理 `Multiset.map_eq_singleton`：map_eq_singleton {f : α -> β} {s : Multiset α
} {b : β} : map f s = {b} ↔ exists a : α, s = {a} ∧ f a = b
· 使用定理 `Multiset.map_injective`：map_injective {f : α -> β} (hf : Function.Inject
ive f) : Function.Injective (Multiset.map f)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `Multiset.attach_map_val`：attach_map_val (s : Multiset α) : s.attach.map 
Subtype.val = s
· 使用定理 `Multiset.map_singleton`：map_singleton (f : α -> β) (a : α) : ({a} : Mult
iset α).map f = {f a}
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `UniqueFactorizationMonoid.prod_normalizedFactors`：prod_normalizedFactors
 {a : α} (ane0 : a != 0) : Associated (normalizedFactors a).prod a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_eq_zero`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero α] 
[IsBotZeroClass α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Submodule.instCanonicallyOrderedAdd`：∀ {R : Type u_2} {M : Type u_3} [in
st : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Cano
nicallyOrderedAdd (Submod…
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.map_eq_bot_iff_of_injective`：map_eq_bot_iff_of_injective {I : Idea
l R} {f : F} (hf : Function.Injective f) : I.map f = ⊥ ↔ I = ⊥
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
（共 35 条，此处仅展示前 30 条）
-/
theorem Ideal.irreducible_map_of_irreducible_minpoly (hI : IsMaximal I) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x)
    (hf : Irreducible (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
    Irreducible (I.map (algebraMap R S)) := by
  classical
  have mem_norm_factors : normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) ∈
      normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
    simp [normalizedFactors_irreducible hf]
  suffices ∃ y, normalizedFactors (I.map (algebraMap R S)) = {y} by
    obtain ⟨y, hy⟩ := this
    have h := prod_normalizedFactors (show I.map (algebraMap R S) ≠ 0 by
          rwa [← bot_eq_zero, Ne,
            map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)])
    rw [associated_iff_eq, hy, Multiset.prod_singleton] at h
    rw [← h]
    exact
      irreducible_of_normalized_factor y
        (show y ∈ normalizedFactors (I.map (algebraMap R S)) by simp [hy])
  rw [normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map hI hI' hx hx']
  use ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm
        ⟨normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)), mem_norm_factors⟩ :
      Ideal S)
  rw [Multiset.map_eq_singleton]
  use ⟨normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)), mem_norm_factors⟩
  refine ⟨?_, rfl⟩
  apply Multiset.map_injective Subtype.coe_injective
  rw [Multiset.attach_map_val, Multiset.map_singleton, Subtype.coe_mk]
  exact normalizedFactors_irreducible hf

set_option backward.isDefEq.respectTransparency.types false in
open Set Classical in
/-- Let `Q` be a lift of factor of the minimal polynomial of `x`, a generator of `S` over `R`, taken
`mod I`. Then (the reduction of) `Q` corresponds via
`normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` to
`span (I.map (algebraMap R S) ∪ {Q.aeval x})`. -/
/-
**KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_
eq_span** 是 Mathlib 中的一个定理，位于命名空间 `KummerDedekind`。
形式化陈述：normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span (hI
 : I.IsMaximal) {Q : R[X]} (hQ : Q.map (Ideal.Quotient.mk I) in normalizedFactor
s ((minpoly R x).map (Ideal.Quotient.mk I))) (hI' : I != ⊥) (hx : (conductor R x
).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) : ((normalizedFactorsMa
pEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm ⟨_, hQ⟩).val = span (I.map 
(algebraMap R S) union {Q.aeval x})
参数：hI : I.IsMaximal；hQ : Q.map (Ideal.Quotient.mk I) in normalizedFactors ((minp
oly R x).map (Ideal.Quotient.mk I))；hI' : I != ⊥；hx : (conductor R x).comap (alg
ebraMap R S) ⊔ I = ⊤；hx' : IsIntegral R x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_trans_apply`：symm_trans_apply (f : α ≃ β) (g : β ≃ γ) (a : γ)
 : (f.trans g).symm a = f.symm (g.symm a)
· 使用定理 `IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_symm`：normalizedFacto
rsEquivOfQuotEquiv_symm (hI : I != ⊥) (hJ : J != ⊥) : (normalizedFactorsEquivOfQ
uotEquiv f hI hJ).symm = normalizedFactorsEqu…
· 使用定理 `Equiv.coe_fn_mk`：∀ {α : Sort u} {β : Sort v} (f : α → β) (g : β → α) (l 
: Function.LeftInverse g f) (r : Function.RightInverse g f),   ⇑{ toFun := f, in
vFun …
· 使用定理 `Equiv.symm_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.symm.symm = 
e
· 使用定理 `Equiv.ofBijective_apply`：∀ {α : Sort u} {β : Sort v} (f : α → β) (hf : F
unction.Bijective f) (a : α), (Equiv.ofBijective f hf) a = f a
· 使用定理 `OrderIso.ofHomInv_apply`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α →o β) (g : β →o α)   (h₁ : f.comp g = OrderHom
.id) (h₂ : g.…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDedekindDomain.idealFactorsFunOfQuotHom_coe_coe`：∀ {R : Type u_1} {A :
 Type u_2} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : IsDedekindDomain 
A] {I : Ideal R}   {J : Ideal A} {f : R…
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `RingHom.coe_coe`：coe_coe {F : Type*} [FunLike F α β] [RingHomClass F α β
] (f : F) : ((f : α ->+* β) : α -> β) = f
· 使用引理 `KummerDedekind.quotMapEquivQuotQuotMap_symm_apply`：quotMapEquivQuotQuotM
ap_symm_apply (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsInt
egral R x) (Q : R[X]) : (quotMapEquivQu…
· 使用定理 `Ideal.span_union`：span_union (s t : Set α) : span (s union t) = span s ⊔
 span t
· 使用定理 `Ideal.span_eq`：span_eq : span (I : Set α) = I
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Ideal.comap_map_of_surjective'`：comap_map_of_surjective' (f : F) (hf : F
unction.Surjective f) (I : Ideal R) : (I.map f).comap f = I ⊔ RingHom.ker f
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I

--- 原说明 ---
Let `Q` be a lift of factor of the minimal polynomial of `x`, a generator of `S`
 over `R`, taken
`mod I`. Then (the reduction of) `Q` corresponds via
`normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` to
`span (I.map (algebraMap R S) ∪ {Q.aeval x})`.
-/
theorem normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span
    (hI : I.IsMaximal) {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I)))
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm ⟨_, hQ⟩).val =
    span (I.map (algebraMap R S) ∪ {Q.aeval x}) := by
  unfold normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    Ideal.normalizedFactorsEquivSpanNormalizedFactors
  rw [Equiv.symm_trans_apply, IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv_symm]
  unfold IsDedekindDomain.normalizedFactorsEquivOfQuotEquiv
  rw [Equiv.coe_fn_mk, Equiv.symm_symm, Equiv.ofBijective_apply]
  dsimp only
  unfold IsDedekindDomain.idealFactorsEquivOfQuotEquiv
  rw [OrderIso.ofHomInv_apply]
  erw [IsDedekindDomain.idealFactorsFunOfQuotHom_coe_coe]
  dsimp only
  rw [map_span, image_singleton, map_span, image_singleton, coe_coe,
    quotMapEquivQuotQuotMap_symm_apply, span_union, span_eq, sup_comm,
    ← image_singleton, ← map_span, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]

end KummerDedekind

