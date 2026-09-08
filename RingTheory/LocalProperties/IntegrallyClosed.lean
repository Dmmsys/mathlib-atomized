/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# `IsIntegrallyClosed` is a local property

In this file, we prove that `IsIntegrallyClosed` is a local property.

## Main results

* `IsIntegrallyClosed.of_localization_maximal` : An integral domain `R` is integral closed
  if `Rₘ` is integral closed for any maximal ideal `m` of `R`.
-/

public section

open scoped nonZeroDivisors

open Localization Ideal IsLocalization

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

/-
**IsIntegrallyClosed.iInf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegrallyClosed.iInf {ι : Type*} (S : ι -> Subalgebra R K) (h : forall 
i, IsIntegrallyClosed (S i)) : IsIntegrallyClosed (⨅ i, S i : Subalgebra R K)
参数：S : ι -> Subalgebra R K；h : forall i, IsIntegrallyClosed (S i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIntegrallyClosed_iff`：isIntegrallyClosed_iff : IsIntegrallyClosed R ↔ 
forall {x : K}, IsIntegral R x -> exists y, algebraMap R K y = x
· 使用定理 `Localization.subalgebra.instIsFractionRingSubtypeMemSubalgebra`：∀ {A : T
ype u_1} (K : Type u_2) [inst : CommRing A] [inst_1 : Field K] [inst_2 : Algebra
 A K] [IsFractionRing A K]   (S : Subalgebra A K), I…
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Algebra.mem_iInf`：mem_iInf {ι : Sort*} {S : ι -> Subalgebra R A} {x : A}
 : x in ⨅ i, S i ↔ forall i, x in S i
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `Subalgebra.inclusion.isScalarTower_right`：∀ {R : Type u} {A : Type v} [i
nst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A] {S T : Subalg
ebra R A}   (h : S ≤ T) (X : T…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsIntegrallyClosed.iInf {ι : Type*} (S : ι → Subalgebra R K)
    (h : ∀ i, IsIntegrallyClosed (S i)) :
    IsIntegrallyClosed (⨅ i, S i : Subalgebra R K) := by
  refine (isIntegrallyClosed_iff K).mpr (fun {x} hx ↦ CanLift.prf x (Algebra.mem_iInf.mpr ?_))
  intro i
  have le : (⨅ i : ι, S i : Subalgebra R K) ≤ S i := iInf_le S i
  algebraize [(Subalgebra.inclusion le).toRingHom]
  have : IsScalarTower ↥(⨅ i, S i) (S i) K := Subalgebra.inclusion.isScalarTower_right le K
  rcases (isIntegrallyClosed_iff K).mp (h i) hx.tower_top with ⟨⟨_, hin⟩, hy⟩
  rwa [← hy]
/-
**IsIntegrallyClosed.of_iInf_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegrallyClosed.of_iInf_eq_bot {ι : Type*} (S : ι -> Subalgebra R K) (h
 : forall i : ι, IsIntegrallyClosed (S i)) (hs : ⨅ i : ι, S i = ⊥) : IsIntegrall
yClosed R
参数：S : ι -> Subalgebra R K；h : forall i : ι, IsIntegrallyClosed (S i)；hs : ⨅ i :
 ι, S i = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsIntegrallyClosed.of_equiv`：of_equiv (f : R ≃+* S) [h : IsIntegrallyClo
sed R] : IsIntegrallyClosed S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsIntegrallyClosed.iInf`：IsIntegrallyClosed.iInf {ι : Type*} (S : ι -> S
ubalgebra R K) (h : forall i, IsIntegrallyClosed (S i)) : IsIntegrallyClosed (⨅ 
i, S i : Suba…
-/
theorem IsIntegrallyClosed.of_iInf_eq_bot {ι : Type*} (S : ι → Subalgebra R K)
    (h : ∀ i : ι, IsIntegrallyClosed (S i)) (hs : ⨅ i : ι, S i = ⊥) : IsIntegrallyClosed R :=
  have f : (⊥ : Subalgebra R K) ≃ₐ[R] R :=
    Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective R K)
  (IsIntegrallyClosed.iInf S h).of_equiv (hs ▸ f).toRingEquiv
/-
**IsIntegrallyClosed.of_localization_submonoid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegrallyClosed.of_localization_submonoid [IsDomain R] {ι : Type*} (S :
 ι -> Submonoid R) (h : forall i : ι, S i <= R⁰) (hi : forall i : ι, IsIntegrall
yClosed (Localization (S i))) (hs : ⨅ i : ι, Localization.subalgebra (FractionRi
ng R) (S i) (h i) = ⊥) : IsIntegrallyClosed R
参数：S : ι -> Submonoid R；h : forall i : ι, S i <= R⁰；hi : forall i : ι, IsIntegra
llyClosed (Localization (S i))；hs : ⨅ i : ι, Localization.subalgebra (FractionRi
ng R) (S i) (h i) = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegrallyClosed.of_iInf_eq_bot`：IsIntegrallyClosed.of_iInf_eq_bot {ι 
: Type*} (S : ι -> Subalgebra R K) (h : forall i : ι, IsIntegrallyClosed (S i)) 
(hs : ⨅ i : ι, S i = ⊥)…
· 使用定理 `IsIntegrallyClosed.of_equiv`：of_equiv (f : R ≃+* S) [h : IsIntegrallyClo
sed R] : IsIntegrallyClosed S
-/
theorem IsIntegrallyClosed.of_localization_submonoid [IsDomain R] {ι : Type*} (S : ι → Submonoid R)
    (h : ∀ i : ι, S i ≤ R⁰) (hi : ∀ i : ι, IsIntegrallyClosed (Localization (S i)))
    (hs : ⨅ i : ι, Localization.subalgebra (FractionRing R) (S i) (h i) = ⊥) :
    IsIntegrallyClosed R :=
  IsIntegrallyClosed.of_iInf_eq_bot (fun i ↦ Localization.subalgebra (FractionRing R) (S i) (h i))
    (fun i ↦ (hi i).of_equiv (IsLocalization.algEquiv (S i) (Localization (S i)) _).toRingEquiv) hs

/-- An integral domain $R$ is integrally closed if there exists a set of prime ideals $S$ such that
  $\bigcap_{\mathfrak{p} \in S} R_{\mathfrak{p}} = R$ and for every $\mathfrak{p} \in S$,
  $R_{\mathfrak{p}}$ is integrally closed. -/
/-
**IsIntegrallyClosed.of_localization** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegrallyClosed.of_localization [IsDomain R] (S : Set (PrimeSpectrum R)
) (h : forall p in S, IsIntegrallyClosed (Localization.AtPrime p.1)) (hs : ⨅ p i
n S, (Localization.subalgebra (FractionRing R) p.1.primeCompl p.1.primeCompl_le_
nonZeroDivisors) = ⊥) : IsIntegrallyClosed R
参数：S : Set (PrimeSpectrum R)；h : forall p in S, IsIntegrallyClosed (Localization
.AtPrime p.1)；hs : ⨅ p in S, (Localization.subalgebra (FractionRing R) p.1.prime
Compl p.1.primeCompl_le_nonZeroDivisors) = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsIntegrallyClosed.of_localization_submonoid`：IsIntegrallyClosed.of_loca
lization_submonoid [IsDomain R] {ι : Type*} (S : ι -> Submonoid R) (h : forall i
 : ι, S i <= R⁰) (hi : forall i : …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subalgebra.ext`：ext {S T : Subalgebra R A} (h : forall x : A, x in S ↔ x
 in T) : S = T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An integral domain $R$ is integrally closed if there exists a set of prime ideal
s $S$ such that
  $\bigcap_{\mathfrak{p} \in S} R_{\mathfrak{p}} = R$ and for every $\mathfrak{p
} \in S$,
  $R_{\mathfrak{p}}$ is integrally closed.
-/
theorem IsIntegrallyClosed.of_localization [IsDomain R] (S : Set (PrimeSpectrum R))
    (h : ∀ p ∈ S, IsIntegrallyClosed (Localization.AtPrime p.1))
    (hs : ⨅ p ∈ S, (Localization.subalgebra (FractionRing R) p.1.primeCompl
      p.1.primeCompl_le_nonZeroDivisors) = ⊥) : IsIntegrallyClosed R := by
  apply IsIntegrallyClosed.of_localization_submonoid (fun p : S ↦ p.1.1.primeCompl)
    (fun p ↦ p.1.1.primeCompl_le_nonZeroDivisors) (fun p ↦ h p.1 p.2)
  ext x
  simp only [← hs, Algebra.mem_iInf, Subtype.forall]

/-- An integral domain `R` is integral closed if `Rₘ` is integral closed
  for any maximal ideal `m` of `R`. -/
/-
**IsIntegrallyClosed.of_localization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegrallyClosed.of_localization_maximal [IsDomain R] (h : forall p : Id
eal R, p != ⊥ -> [p.IsMaximal] -> IsIntegrallyClosed (Localization.AtPrime p)) :
 IsIntegrallyClosed R
参数：h : forall p : Ideal R, p != ⊥ -> [p.IsMaximal] -> IsIntegrallyClosed (Locali
zation.AtPrime p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsIntegrallyClosed.of_localization`：IsIntegrallyClosed.of_localization [
IsDomain R] (S : Set (PrimeSpectrum R)) (h : forall p in S, IsIntegrallyClosed (
Localization.AtPrime p.1…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Ring.ne_bot_of_isMaximal_of_not_isField`：ne_bot_of_isMaximal_of_not_isFi
eld [Nontrivial R] {M : Ideal R} (max : M.IsMaximal) (not_field : ¬IsField R) : 
M != ⊥
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `Ideal.primeCompl_le_nonZeroDivisors`：Ideal.primeCompl_le_nonZeroDivisors
 {R : Type*} [CommSemiring R] [NoZeroDivisors R] (P : Ideal R) [P.IsPrime] : P.p
rimeCompl <= nonZeroDivis…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf_range`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} [inst : Compl
eteLattice α] {g : β → α} {f : ι → β},   ⨅ b ∈ Set.range f, g b = ⨅ i, g (f i)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Localization.subalgebra.ofField_eq`：ofField_eq : ofField K S hS = subalg
ebra K S hS
· 使用定理 `MaximalSpectrum.toPrimeSpectrum.eq_1`：∀ {R : Type u_1} [inst : CommSemir
ing R] (x : MaximalSpectrum R),   x.toPrimeSpectrum = { asIdeal := x.asIdeal, is
Prime := ⋯ }
· 使用定理 `MaximalSpectrum.iInf_localization_eq_bot`：iInf_localization_eq_bot : (⨅ 
v : MaximalSpectrum R, Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_
le_nonZeroDivisors) = ⊥

--- 原说明 ---
An integral domain `R` is integral closed if `Rₘ` is integral closed
  for any maximal ideal `m` of `R`.
-/
theorem IsIntegrallyClosed.of_localization_maximal [IsDomain R]
    (h : ∀ p : Ideal R, p ≠ ⊥ → [p.IsMaximal] → IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed R := by
  by_cases hf : IsField R
  · exact hf.toField.instIsIntegrallyClosed
  refine of_localization (.range MaximalSpectrum.toPrimeSpectrum) (fun _ ↦ ?_) ?_
  · rintro ⟨p, rfl⟩
    exact h p.asIdeal (Ring.ne_bot_of_isMaximal_of_not_isField p.isMaximal hf)
  · rw [iInf_range]
    convert! MaximalSpectrum.iInf_localization_eq_bot R (FractionRing R)
    rw [subalgebra.ofField_eq, MaximalSpectrum.toPrimeSpectrum]
/-
**isIntegrallyClosed_ofLocalizationMaximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIntegrallyClosed_ofLocalizationMaximal : OfLocalizationMaximal fun R _ =
> ([IsDomain R] -> IsIntegrallyClosed R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegrallyClosed.of_localization_maximal`：IsIntegrallyClosed.of_locali
zation_maximal [IsDomain R] (h : forall p : Ideal R, p != ⊥ -> [p.IsMaximal] -> 
IsIntegrallyClosed (Localization…
-/
theorem isIntegrallyClosed_ofLocalizationMaximal :
    OfLocalizationMaximal fun R _ => ([IsDomain R] → IsIntegrallyClosed R) :=
  fun _ _ h _ ↦ IsIntegrallyClosed.of_localization_maximal fun p _ hpm ↦ h p hpm

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
/-
**IsIntegrallyClosed.of_isLocalization_maximal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIntegrallyClosed.of_isLocalization_maximal [IsDomain R] (h : forall (P :
 Ideal R) [P.IsMaximal], IsIntegrallyClosed (Rₚ P)) : IsIntegrallyClosed R
参数：h : forall (P : Ideal R) [P.IsMaximal], IsIntegrallyClosed (Rₚ P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsIntegrallyClosed.of_localization_maximal`：IsIntegrallyClosed.of_locali
zation_maximal [IsDomain R] (h : forall p : Ideal R, p != ⊥ -> [p.IsMaximal] -> 
IsIntegrallyClosed (Localization…
· 使用定理 `IsIntegrallyClosed.of_equiv`：of_equiv (f : R ≃+* S) [h : IsIntegrallyClo
sed R] : IsIntegrallyClosed S
· 使用定理 `Submonoid.map_id`：map_id (S : Submonoid M) : S.map (MonoidHom.id M) = S
-/
theorem IsIntegrallyClosed.of_isLocalization_maximal [IsDomain R]
    (h : ∀ (P : Ideal R) [P.IsMaximal], IsIntegrallyClosed (Rₚ P)) :
    IsIntegrallyClosed R := .of_localization_maximal
  (fun P _ _ ↦ .of_equiv <| ringEquivOfRingEquiv (Rₚ P) _ (RingEquiv.refl R) P.primeCompl.map_id)
