/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# A finite flat module `M` is locally free if `rankAtStalk M` is constant
-/

public section

namespace Module

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
  [Module.Flat R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Flat R N]

open LocalizedModule

attribute [local instance] Module.free_of_flat_of_isLocalRing

/-
**Module.bijective_of_surjective_of_rankAtStalk_eq** 是 Mathlib 中的一个引理，位于命名空间 `Mo
dule`。
形式化陈述：bijective_of_surjective_of_rankAtStalk_eq {φ : M ->ₗ[R] N} (hs : Function.
Surjective φ) (h : forall (m : Ideal R) [m.IsMaximal], rankAtStalk M ⟨m, inferIn
stance⟩ = rankAtStalk N ⟨m, inferInstance⟩) : Function.Bijective φ
参数：hs : Function.Surjective φ；h : forall (m : Ideal R) [m.IsMaximal], rankAtStal
k M ⟨m, inferInstance⟩ = rankAtStalk N ⟨m, inferInstance⟩。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `bijective_of_localized_maximal`：bijective_of_localized_maximal (h : fora
ll (J : Ideal R) [J.IsMaximal], Function.Bijective (map J.primeCompl f)) : Funct
ion.Bijective f
· 使用定理 `OrzechProperty.bijective_of_surjective_of_finrank_le`：∀ {R : Type u} {M 
: Type v} {M' : Type v'} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 
: _root_.Module R M]   [Module.Free R M] […
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
· 使用定理 `CommRing.orzechProperty`：∀ (R : Type u_1) [inst : CommRing R], OrzechPro
perty R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用引理 `LocalizedModule.map_surjective`：LocalizedModule.map_surjective (l : M ->
ₗ[R] N) (hl : Function.Surjective l) : Function.Surjective (map S l)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma bijective_of_surjective_of_rankAtStalk_eq {φ : M →ₗ[R] N} (hs : Function.Surjective φ)
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk N ⟨m, inferInstance⟩) :
    Function.Bijective φ :=
  bijective_of_localized_maximal φ fun m _ ↦
    OrzechProperty.bijective_of_surjective_of_finrank_le (map m.primeCompl φ)
      (map_surjective m.primeCompl φ hs) (h m).le

variable (M) in
/-- Let `M` be a finite flat `R`-module, `p` be a prime ideal of `R`. If `rankAtStalk M` is
constant, then there exists `a ∉ p` such that `M` is free after localization away from `a`. -/
/-
**Module.Free.away_of_finite_of_flat_of_rankAtStalk_constant** 是 Mathlib 中的一个定理，
位于命名空间 `Module.Free`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] (M : Type u_2) [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   [Module.Finite R M] [Module.Flat R M] (p : Id
eal R) [inst_5 : p.IsPrime],   (∀ (m : Ideal R) [inst_6 : m.IsMaximal],       Mo
dule.rankAtStalk M { asIdeal := m, isPrime := ⋯ } = Module.rankAtStalk M { asIde
al := p, isPrime := ⋯ }) →     ∃ a ∉ p, Module.Free (Localization.Away a) (Local
izedModule.Away a M)
参数：M : Type u_2；p : Ideal R；∀ (m : Ideal R) [inst_6 : m.IsMaximal],       Module
.rankAtStalk M { asIdeal := m, isPrime := ⋯ } = Module.rankAtStalk M { asIdeal :
= p, isPrime := ⋯ }；Localization.Away a；LocalizedModule.Away a M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Ideal.IsPrime.one_notMem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → 1 ∉ I
· 使用引理 `Module.Free.of_subsingleton'`：of_subsingleton' [Subsingleton R] : Module
.Free R N
· 使用定理 `LocalizedModule.instSubsingleton`：∀ {R : Type u_1} {M : Type u_2} [inst 
: CommRing R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Subsing
leton M] (S : Submonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleFinsuppLinearMap`：∀ (R : Type u_1) [inst : CommSemi
ring R] (S : Submonoid R) (M : Type u_3) [inst_1 : AddCommMonoid M]   [inst_2 : 
_root_.Module R M] {M' : Ty…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `LinearMap.CompatibleSMul.finsupp_cod`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `Module.free_of_flat_of_isLocalRing`：free_of_flat_of_isLocalRing [Module.
Finite R P] [Flat R P] : Free R P
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.Finite.instLocalizationLocalizedModule`：∀ {R : Type u} [inst : Co
mmSemiring R] (S : Submonoid R) {M : Type w} [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] [Module.Fini…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用引理 `Module.exists_localizedMap_surjective_of_surjective`：Module.exists_local
izedMap_surjective_of_surjective [Module.FinitePresentation R M] (S : Submonoid 
R) {Mₚ : Type*} [AddCommGroup Mₚ] [Module…
· 使用定理 `instFinitePresentationFinsupp`：∀ {R : Type u_1} [inst : Ring R] {ι : Typ
e u_2} [Finite ι], Module.FinitePresentation R (ι →₀ R)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用引理 `Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surje
ctive`：Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjec
tive (p : Ideal R) [p.IsPrime] (φ : N ->ₗ[R] M) (hφ : Function.Surj…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LocalizedModule.coe_map_eq`：LocalizedModule.coe_map_eq {M' N' : Type*} [
AddCommMonoid M'] [AddCommMonoid N'] [Module R M'] [Module R N'] (g₁ : M ->ₗ[R] 
M') (g₂ : N ->ₗ[…
· 使用定理 `Module.free_of_isLocalizedModule`：Module.free_of_isLocalizedModule {Rₛ M
ₛ} [AddCommGroup Mₛ] [Module R Mₛ] [CommRing Rₛ] [Algebra R Rₛ] [Module Rₛ Mₛ] [
IsScalarTower R Rₛ Mₛ]…
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用引理 `Module.bijective_of_surjective_of_rankAtStalk_eq`：bijective_of_surjectiv
e_of_rankAtStalk_eq {φ : M ->ₗ[R] N} (hs : Function.Surjective φ) (h : forall (m
 : Ideal R) [m.IsMaximal], rankAtStalk…
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
Let `M` be a finite flat `R`-module, `p` be a prime ideal of `R`. If `rankAtStal
k M` is
constant, then there exists `a ∉ p` such that `M` is free after localization awa
y from `a`.
-/
theorem Free.away_of_finite_of_flat_of_rankAtStalk_constant (p : Ideal R) [p.IsPrime]
    (h : ∀ (m : Ideal R) [m.IsMaximal],
      rankAtStalk M ⟨m, inferInstance⟩ = rankAtStalk M ⟨p, inferInstance⟩) :
    ∃ a ∉ p, Module.Free (Localization.Away a) (LocalizedModule.Away a M) := by
  rcases subsingleton_or_nontrivial R with _ | _
  · use 1, Ideal.IsPrime.one_notMem ‹_›
    exact Module.Free.of_subsingleton' (Localization.Away 1) (LocalizedModule.Away 1 M)
  · let Rₚ := Localization.AtPrime p
    let n := rankAtStalk M ⟨p, inferInstance⟩
    let f : (Fin n →₀ R) →ₗ[R] Fin n →₀ Rₚ := Finsupp.mapRange.linearMap (Algebra.linearMap R Rₚ)
    let g : M →ₗ[R] LocalizedModule.AtPrime p M := LocalizedModule.mkLinearMap p.primeCompl M
    obtain ⟨φ, -, -, hφps⟩ := exists_localizedMap_surjective_of_surjective p.primeCompl f g
      ((finBasis Rₚ (LocalizedModule.AtPrime p M)).repr.restrictScalars R).symm.surjective
    obtain ⟨a, hap, hφas⟩ := by
      refine exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective p φ ?_
      simpa [LocalizedModule.coe_map_eq f g]
    have : Module.Free (Localization.Away a) (LocalizedModule.Away a (Fin n →₀ R)) :=
      free_of_isLocalizedModule (Submonoid.powers a) (mkLinearMap (Submonoid.powers a) (Fin n →₀ R))
    let φₐ : LocalizedModule.Away a (Fin n →₀ R) →ₗ[Localization.Away a] LocalizedModule.Away a M :=
      LocalizedModule.map (Submonoid.powers a) φ
    refine ⟨a, hap, Module.Free.of_equiv <| LinearEquiv.ofBijective φₐ <|
      bijective_of_surjective_of_rankAtStalk_eq hφas <| fun m _ ↦ ?_⟩
    obtain ⟨𝔪, _, hm𝔪⟩ : ∃ 𝔪 : Ideal R, 𝔪.IsMaximal ∧ PrimeSpectrum.comap
        (algebraMap R (Localization (Submonoid.powers a))) ⟨m, inferInstance⟩ ≤ 𝔪 :=
      (m.comap (algebraMap R (Localization.Away a))).exists_le_maximal Ideal.IsPrime.ne_top'
    simp [rankAtStalk_isBaseChange (LocalizedModule.isBaseChange (Submonoid.powers a) _),
      rankAtStalk_eq_of_le_of_finite_of_flat' M hm𝔪, h 𝔪, n]

end Module

