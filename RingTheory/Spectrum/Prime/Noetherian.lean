/-
Copyright (c) 2020 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Andrew Yang
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.NoetherianSpace

/-!
This file proves additional properties of the prime spectrum a ring is Noetherian.
-/

public section


universe u v

namespace PrimeSpectrum

open TopologicalSpace

section IsNoetherianRing

variable (R : Type u) [CommSemiring R] [IsNoetherianRing R]

/-
**PrimeSpectrum.** 是 Mathlib 中的一个实例，位于命名空间 `PrimeSpectrum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NoetherianSpace (PrimeSpectrum R) :=
  ((noetherianSpace_TFAE <| PrimeSpectrum R).out 0 1).mpr (closedsEmbedding R).dual.wellFoundedLT
/-
**PrimeSpectrum.finite_setOfPred_isMin** 是 Mathlib 中的一个引理，位于命名空间 `PrimeSpectrum`
。
形式化陈述：finite_setOfPred_isMin : {x : PrimeSpectrum R | IsMin x}.Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Set.Finite.of_finite_image`：∀ {α : Type u} {β : Type v} {s : Set α} {f :
 α → β}, (f '' s).Finite → Set.InjOn f s → s.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用引理 `minimalPrimes.finite_of_isNoetherianRing`：minimalPrimes.finite_of_isNoet
herianRing : (minimalPrimes R).Finite
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
lemma finite_setOfPred_isMin :
    {x : PrimeSpectrum R | IsMin x}.Finite := by
  have : Function.Injective (asIdeal (R := R)) := @PrimeSpectrum.ext _ _
  refine Set.Finite.of_finite_image (f := asIdeal) ?_ this.injOn
  simp_rw [isMin_iff]
  exact (minimalPrimes.finite_of_isNoetherianRing R).subset (Set.image_preimage_subset _ _)

@[deprecated (since := "2026-07-09")] alias finite_setOf_isMin := finite_setOfPred_isMin

end IsNoetherianRing

end PrimeSpectrum

namespace IsArtinianRing

open PrimeSpectrum

variable (R : Type*) [CommRing R] [IsArtinianRing R]

/-
**IsArtinianRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsArtinianRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Ring.KrullDimLE 0 R := .mk₀ fun _ _ ↦ inferInstance
/-
**IsArtinianRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsArtinianRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology (PrimeSpectrum R) :=
  discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨inferInstance, inferInstance⟩

variable {R} in
/-
**IsArtinianRing.exists_not_mem_forall_mem_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `IsAr
tinianRing`。
形式化陈述：exists_not_mem_forall_mem_of_ne (p : Ideal R) [p.IsPrime] : exists r ∉ p, 
IsIdempotentElem r ∧ forall q : Ideal R, q.IsPrime -> q != p -> r in q
参数：p : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `PrimeSpectrum.toPiLocalization_bijective`：toPiLocalization_bijective : F
unction.Bijective (toPiLocalization R)
· 使用定理 `IsArtinianRing.instDiscreteTopologyPrimeSpectrum`：∀ (R : Type u_1) [inst
 : CommRing R] [IsArtinianRing R], DiscreteTopology (PrimeSpectrum R)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `IsLocalization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemirin
g R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (P : Ideal 
R)   [hp : P.IsPrime] [I…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.AtPrime.to_map_mem_maximal_iff`：to_map_mem_maximal_iff (x
 : R) (h : IsLocalRing S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
lemma exists_not_mem_forall_mem_of_ne (p : Ideal R) [p.IsPrime] :
    ∃ r ∉ p, IsIdempotentElem r ∧ ∀ q : Ideal R, q.IsPrime → q ≠ p → r ∈ q := by
  classical
  obtain ⟨r, hr⟩ := PrimeSpectrum.toPiLocalization_bijective.2 (Pi.single ⟨p, inferInstance⟩ 1)
  have : algebraMap R (Localization p.primeCompl) r = 1 := by
    simpa [PrimeSpectrum.toPiLocalization,
      -FaithfulSMul.algebraMap_eq_one_iff] using funext_iff.mp hr ⟨p, inferInstance⟩
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, this]
    simp
  · apply PrimeSpectrum.toPiLocalization_bijective.injective
    simp [map_mul, hr, ← Pi.single_mul]
  · intro q hq e
    have : PrimeSpectrum.mk q inferInstance ≠ ⟨p, inferInstance⟩ := ne_of_apply_ne (·.1) e
    have : (algebraMap R (Localization.AtPrime q)) r = 0 := by
      simpa [PrimeSpectrum.toPiLocalization, this,
        -FaithfulSMul.algebraMap_eq_zero_iff] using funext_iff.mp hr ⟨q, inferInstance⟩
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q, this]
    simp

variable (F : Type*) [Field F] [Algebra F R] [Module.Finite F R]
/-
**IsArtinianRing.finrank_eq_sum_primeSpectrum** 是 Mathlib 中的一个定理，位于命名空间 `IsArtin
ianRing`。
形式化陈述：finrank_eq_sum_primeSpectrum [Fintype (PrimeSpectrum R)] : Module.finrank 
F R = ∑ p : PrimeSpectrum R, Module.finrank F (Localization.AtPrime p.asIdeal)
参数：PrimeSpectrum R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsArtinianRing.localization_surjective`：localization_surjective : Functi
on.Surjective (algebraMap R L)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
· 使用定理 `IsArtinianRing.instDiscreteTopologyPrimeSpectrum`：∀ (R : Type u_1) [inst
 : CommRing R] [IsArtinianRing R], DiscreteTopology (PrimeSpectrum R)
· 使用定理 `Module.finrank_pi_fintype`：Module.finrank_pi_fintype {ι : Type v} [Finty
pe ι] {M : ι -> Type w} [forall i : ι, AddCommMonoid (M i)] [forall i : ι, Modul
e R (M i)] [for…
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
-/
theorem finrank_eq_sum_primeSpectrum [Fintype (PrimeSpectrum R)] :
    Module.finrank F R = ∑ p : PrimeSpectrum R, Module.finrank F (Localization.AtPrime p.asIdeal) :=
  have (p : Ideal R) [p.IsPrime] : Module.Finite F (Localization.AtPrime p) :=
    Module.Finite.of_surjective (Algebra.algHom F R (Localization.AtPrime p)).toLinearMap
      (localization_surjective p.primeCompl (Localization.AtPrime p))
  ((toPiLocalizationEquiv R).restrictScalars F).toLinearEquiv.finrank_eq.trans
    (Module.finrank_pi_fintype F)

end IsArtinianRing

