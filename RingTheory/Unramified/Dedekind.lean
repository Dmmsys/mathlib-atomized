/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Unramified.Field

/-!
# Unramified algebras over Dedekind domains

We prove that a domain finite and unramified over a Dedekind domain is a Dedekind domain.
-/

public section

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsDedekindDomain A] [IsDomain B] [Algebra.FormallyUnramified A B]

include A in
/-
**isDedekindDomainDvr.of_formallyUnramified** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDedekindDomainDvr.of_formallyUnramified : IsDedekindDomainDvr B where __
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherianRing.of_finite`：IsNoetherianRing.of_finite (R S) [Ring R] [R
ing S] [Module R S] [IsScalarTower R S S] [IsNoetherianRing R] [Module.Finite R 
S] : IsNoetheria…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDedekindDomainDvr.toIsNoetherian`：∀ {A : Type u_1} {inst : CommRing A}
 {inst_1 : IsDomain A} [self : IsDedekindDomainDvr A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Ideal.IsPrime.isMaximal`：Ideal.IsPrime.isMaximal {R : Type*} [CommRing R
] [DimensionLEOne R] {p : Ideal R} (h : p.IsPrime) (hp : p != ⊥) : p.IsMaximal
· 使用定理 `Ideal.under_ne_bot`：under_ne_bot [Nontrivial A] [IsDomain B] (hP : P != 
⊥) : under A P != ⊥
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsArtinianRing.of_finite`：IsArtinianRing.of_finite (R S) [Ring R] [Ring 
S] [Module R S] [IsScalarTower R S S] [IsArtinianRing R] [Module.Finite R S] : I
sArtinianRing …
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsRadical.radical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ide
al R}, I.IsRadical → I.radical = I
· 使用定理 `Algebra.FormallyUnramified.isRadical_map_isMaximal`：isRadical_map_isMaxi
mal (B : Type*) [CommRing B] [Algebra A B] [Algebra.EssFiniteType A B] [Algebra.
FormallyUnramified A B] (p : Ideal A) [p…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `Module.Finite.finiteType`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [hRA : Module.Finite R 
A], Algebra.Fi…
· 使用引理 `IsLocalization.map_radical`：map_radical (I : Ideal R) : I.radical.map (a
lgebraMap R S) = (I.map (algebraMap R S)).radical
· 使用定理 `IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`：IsLocalization.
AtPrime.radical_map_of_mem_minimalPrimes (q : Ideal R) [hqp : q.IsPrime] [IsLoca
lization.AtPrime A q] (I : Ideal R) (hIq : q …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.minimalPrimes_eq_comap`：Ideal.minimalPrimes_eq_comap : I.minimalPr
imes = Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (R ⧸ I)
· 使用定理 `IsArtinianRing.mem_minimalPrimes`：mem_minimalPrimes {I p : Ideal R} [hp 
: p.IsPrime] (hIp : I <= p) : p in I.minimalPrimes
· 使用定理 `Ideal.Quotient.instIsPrimeQuotientMapRingHomAlgebraMapMkOfLiesOver`：∀ (R
 : Type u_2) [inst : CommSemiring R] {A : Type u_3} [inst_1 : CommRing A] [inst_
2 : Algebra R A] (p : Ideal R)   (P : Ideal A) [P.IsPrim…
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用引理 `Ideal.comap_map_mk`：comap_map_mk {I J : Ideal R} [I.IsTwoSided] (h : I <
= J) : Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) = J
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `Localization.AtPrime.map_eq_maximalIdeal`：∀ {R : Type u_1} [inst : CommS
emiring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.map (algebraMap R (Localizati
on.AtPrime I)) I = IsLocalRing…
（共 43 条，此处仅展示前 30 条）
-/
theorem isDedekindDomainDvr.of_formallyUnramified : IsDedekindDomainDvr B where
  __ := IsNoetherianRing.of_finite A B
  is_dvr_at_nonzero_prime := by
    intro q hq hqp
    let q' := IsLocalRing.maximalIdeal (Localization.AtPrime q)
    suffices q'.IsPrincipal from ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q)
      (IsLocalization.AtPrime.not_isField B hq (Localization.AtPrime q))).out 4 0).mp this
    let p := q.under A
    let := Localization.AtPrime.algebraOfLiesOver p q
    have : p.IsMaximal := (hqp.under A).isMaximal (q.under_ne_bot A hq)
    let : Field (A ⧸ p) := Ideal.Quotient.field p
    have := IsArtinianRing.of_finite (A ⧸ p) (B ⧸ p.map (algebraMap A B))
    suffices q' = (p.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q)) by
      rw [this, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq A (Localization.AtPrime p) (Localization.AtPrime q),
        ← Ideal.map_map]
      infer_instance
    rw [← (Algebra.FormallyUnramified.isRadical_map_isMaximal A B p).radical,
      IsLocalization.map_radical q.primeCompl,
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime q) q,
      Localization.AtPrime.map_eq_maximalIdeal]
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q.map (Ideal.Quotient.mk (p.map (algebraMap A B))),
      IsArtinianRing.mem_minimalPrimes bot_le, Ideal.comap_map_mk Ideal.map_comap_le⟩

include A in
/-- A domain finite and unramified over a Dedekind domain is a Dedekind domain. -/
/-
**isDedekindDomain.of_formallyUnramified** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isDedekindDomain.of_formallyUnramified : IsDedekindDomain B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isDedekindDomainDvr.of_formallyUnramified`：isDedekindDomainDvr.of_formal
lyUnramified : IsDedekindDomainDvr B where __
· 使用定理 `IsDedekindDomainDvr.isDedekindDomain`：∀ (A : Type u_1) [inst : CommRing 
A] [inst_1 : IsDomain A] [IsDedekindDomainDvr A], IsDedekindDomain A

--- 原说明 ---
A domain finite and unramified over a Dedekind domain is a Dedekind domain.
-/
theorem isDedekindDomain.of_formallyUnramified : IsDedekindDomain B :=
  have := isDedekindDomainDvr.of_formallyUnramified A B
  inferInstance
