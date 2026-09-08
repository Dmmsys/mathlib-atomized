/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Finiteness.NilpotentKer
public import Mathlib.RingTheory.Jacobson.Artinian
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Quasi-finite algebras

In this file, we define the notion of quasi-finite algebras and prove basic properties about them

## Main definition and results
- `Algebra.QuasiFinite`: The class of quasi-finite algebras.
  We say that an `R`-algebra `S` is quasi-finite
  if `κ(p) ⊗[R] S` is finite-dimensional over `κ(p)` for all primes `p` of `R`.
- `Algebra.QuasiFinite.finite_comap_preimage_singleton`:
  Quasi-finite algebras have finite fibers.
- `Algebra.QuasiFinite.iff_of_isArtinianRing`:
  Over an artinian ring, an algebra is quasi-finite iff it is module-finite.
- `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton`: For a finite-type `R`-algebra `S`,
  `S` is quasi-finite if and only if `Spec S → Spec R` has finite fibers.
- `Algebra.QuasiFiniteAt`: If `S` is an `R`-algebra and `p` a prime of `S`,
  we say that `S` is `R`-quasi-finite at `p` if `Sₚ` is `R`-quasi-finite.

-/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

-- See `Mathlib/RingTheory/QuasiFinite/Polynomial.lean`
assert_not_exists RatFunc

open TensorProduct

-- for performance reasons
attribute [-instance] Module.Free.instFaithfulSMulOfNontrivial Algebra.IsIntegral.isLocalHom

namespace Algebra

variable (R S) in
/--
We say that an `R`-algebra `S` is quasi-finite
if `κ(p) ⊗[R] S` is finite-dimensional over `κ(p)` for all primes `p` of `R`.

This is slightly different from the
[stacks projects definition](https://stacks.math.columbia.edu/tag/00PL),
which requires `S` to be of finite type over `R`.

Also see `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton` that
this is equivalent to having finite fibers for finite-type algebras.
-/
@[mk_iff, stacks 00PL]
/-
**Algebra.QuasiFinite** 是 Mathlib 中的一个类，位于命名空间 `Algebra`。
形式化陈述：QuasiFinite : Prop where finite_fiber (P : Ideal R) [P.IsPrime] : Module.F
inite P.ResidueField (P.Fiber S)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that an `R`-algebra `S` is quasi-finite
if `κ(p) ⊗[R] S` is finite-dimensional over `κ(p)` for all primes `p` of `R`.

This is slightly different from the
[stacks projects definition](https://stacks.math.columbia.edu/tag/00PL),
which requires `S` to be of finite type over `R`.

Also see `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton` that
this is equivalent to having finite fibers for finite-type algebras.
-/
class QuasiFinite : Prop where
  finite_fiber (P : Ideal R) [P.IsPrime] :
    Module.Finite P.ResidueField (P.Fiber S) := by infer_instance

attribute [stacks 00PM] quasiFinite_iff

namespace QuasiFinite

attribute [instance] finite_fiber

/-
**Algebra.QuasiFinite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.QuasiFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiFinite R S] (P : Ideal R) [P.IsPrime] : IsArtinianRing (P.Fiber S) :=
  .of_finite P.ResidueField _
/-
**Algebra.QuasiFinite.finite_comap_preimage_singleton** 是 Mathlib 中的一个引理，位于命名空间 
`Algebra.QuasiFinite`。
形式化陈述：finite_comap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) : 
(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}).Finite
参数：P : PrimeSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `finite_of_compact_of_discrete`：finite_of_compact_of_discrete [CompactSpa
ce X] [DiscreteTopology X] : Finite X
· 使用定理 `IsArtinianRing.instDiscreteTopologyPrimeSpectrum`：∀ (R : Type u_1) [inst
 : CommRing R] [IsArtinianRing R], DiscreteTopology (PrimeSpectrum R)
· 使用定理 `Algebra.QuasiFinite.instIsArtinianRingFiber`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.QuasiFinite R S] (P : Ideal R) […
-/
lemma finite_comap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) :
    (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}).Finite :=
  (PrimeSpectrum.preimageEquivFiber R S P).finite_iff.mpr finite_of_compact_of_discrete
/-
**Algebra.QuasiFinite.finite_primesOver** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Quasi
Finite`。
形式化陈述：finite_primesOver [QuasiFinite R S] (I : Ideal R) : (I.primesOver S).Finit
e
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用引理 `Algebra.QuasiFinite.finite_comap_preimage_singleton`：finite_comap_preima
ge_singleton [QuasiFinite R S] (P : PrimeSpectrum R) : (PrimeSpectrum.comap (alg
ebraMap R S) ⁻¹' {P}).Finite
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.LiesOver.over`：∀ {A : Type u_2} {inst : CommSemiring A} {B : Type 
u_3} {inst_1 : Semiring B} {inst_2 : Algebra A B} {P : Ideal B}   {p : Ideal A} 
[self : P…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
-/
lemma finite_primesOver [QuasiFinite R S] (I : Ideal R) : (I.primesOver S).Finite := by
  by_cases h : I.IsPrime
  · refine ((finite_comap_preimage_singleton ⟨I, h⟩).image PrimeSpectrum.asIdeal).subset ?_
    exact fun J hJ ↦ ⟨⟨_, hJ.1⟩, PrimeSpectrum.ext hJ.2.1.symm, rfl⟩
  · convert! Set.finite_empty
    by_contra!
    obtain ⟨J, h₁, ⟨rfl⟩⟩ := this
    exact h inferInstance
/-
**Algebra.QuasiFinite.finite_comap_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Q
uasiFinite`。
形式化陈述：finite_comap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)} (hs : 
s.Finite) : (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s).Finite
参数：PrimeSpectrum R；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.preimage'`：∀ {α : Type u} {β : Type v} {f : α → β} {s : Set β
}, s.Finite → (∀ b ∈ s, (f ⁻¹' {b}).Finite) → (f ⁻¹' s).Finite
· 使用引理 `Algebra.QuasiFinite.finite_comap_preimage_singleton`：finite_comap_preima
ge_singleton [QuasiFinite R S] (P : PrimeSpectrum R) : (PrimeSpectrum.comap (alg
ebraMap R S) ⁻¹' {P}).Finite
-/
lemma finite_comap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)} (hs : s.Finite) :
    (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s).Finite :=
  hs.preimage' fun _ _ ↦ finite_comap_preimage_singleton _
/-
**Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton** 是 Mathlib 中的一个引理，位于命
名空间 `Algebra.QuasiFinite`。
形式化陈述：isDiscrete_comap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R
) : IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P})
参数：P : PrimeSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Homeomorph.discreteTopology`：∀ {X : Type u_1} {Y : Type u_2} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y] [DiscreteTopology X]   (h : X ≃ₜ 
Y), DiscreteTopol…
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `IsArtinianRing.instDiscreteTopologyPrimeSpectrum`：∀ (R : Type u_1) [inst
 : CommRing R] [IsArtinianRing R], DiscreteTopology (PrimeSpectrum R)
· 使用定理 `Algebra.QuasiFinite.instIsArtinianRingFiber`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.QuasiFinite R S] (P : Ideal R) […
-/
lemma isDiscrete_comap_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) :
    IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {P}) :=
  ⟨(PrimeSpectrum.preimageHomeomorphFiber R S P).symm.discreteTopology⟩
/-
**Algebra.QuasiFinite.isDiscrete_comap_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
ra.QuasiFinite`。
形式化陈述：isDiscrete_comap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)} (h
s : IsDiscrete s) : IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s)
参数：PrimeSpectrum R；hs : IsDiscrete s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDiscrete.preimage'`：IsDiscrete.preimage' {s : Set Y} (hs : IsDiscrete 
s) (hf : ContinuousOn f (f ⁻¹' s)) (H : forall x, IsDiscrete (f ⁻¹' {x})) : IsDi
screte (f …
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用引理 `PrimeSpectrum.continuous_comap`：continuous_comap (f : R ->+* S) : Contin
uous (comap f)
· 使用引理 `Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton`：isDiscrete_coma
p_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) : IsDiscrete (Prime
Spectrum.comap (algebraMap R S) ⁻¹' {P})
-/
lemma isDiscrete_comap_preimage [QuasiFinite R S] {s : Set (PrimeSpectrum R)}
    (hs : IsDiscrete s) :
    IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' s) :=
  hs.preimage' (PrimeSpectrum.continuous_comap _).continuousOn
    fun _ ↦ isDiscrete_comap_preimage_singleton _
/-
**Algebra.QuasiFinite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.QuasiFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [Module.Finite R S] : QuasiFinite R S where

@[stacks 00PP "(3)"]
/-
**Algebra.QuasiFinite.baseChange** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.QuasiFinite`
。
形式化陈述：baseChange [QuasiFinite R S] {A : Type*} [CommRing A] [Algebra R A] : Quas
iFinite A (A otimes[R] S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用定理 `instIsLocalHomAtPrimeRingHomAlgebraMap`：∀ {R : Type u_1} {A : Type u_3} 
[inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal R)  
 [inst_3 : I.IsPrime] (J : I…
· 使用定理 `Localization.AtPrime.instIsLiesOverAlgebra`：∀ {A : Type u_4} {B : Type u
_5} [inst : CommSemiring A] [inst_1 : CommSemiring B] [inst_2 : Algebra A B] (p 
: Ideal A)   [inst_3 : p.IsPrime…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsLocalRing.ResidueField.instIsScalarTower`：∀ {R : Type u_1} {S : Type u
_2} [inst : CommRing R] [inst_1 : IsLocalRing R] [inst_2 : CommRing S]   [inst_3
 : IsLocalRing S] [inst_4 : Alge…
· 使用定理 `Localization.AtPrime.instIsScalarTowerOfIsLiesOverAlgebra`：∀ {R : Type u
_1} [inst : CommSemiring R] {A : Type u_4} {B : Type u_5} [inst_1 : CommSemiring
 A]   [inst_2 : CommSemiring B] [inst_3 : Algeb…
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Algebra.QuasiFinite.finite_fiber`：∀ {R : Type u_1} {S : Type u_2} {inst 
: CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : Algebra.Qua
siFinite R S] (P : Ide…
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
instance baseChange [QuasiFinite R S] {A : Type*} [CommRing A] [Algebra R A] :
    QuasiFinite A (A ⊗[R] S) := by
  refine ⟨fun P hP ↦ ?_⟩
  let p := P.under R
  let := Localization.AtPrime.algebraOfLiesOver p P
  let e : P.Fiber (A ⊗[R] S) ≃ₐ[P.ResidueField] P.ResidueField ⊗[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  exact .of_surjective e.symm.toLinearMap e.symm.surjective

open IsLocalRing in
-- See `Module.Finite.of_quasiFinite` instead
/-
**Algebra.QuasiFinite.finite_of_isArtinianRing_of_isLocalRing** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.QuasiFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma finite_of_isArtinianRing_of_isLocalRing
    [QuasiFinite R S] [IsArtinianRing R] [IsLocalRing R] : Module.Finite R S := by
  let e : (maximalIdeal R).Fiber S ≃ₐ[R] S ⧸ (maximalIdeal R).map (algebraMap R S) :=
    (Algebra.TensorProduct.congr (.symm <| .ofBijective _
      (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal R))) .refl).trans <|
    (Algebra.TensorProduct.comm _ _ _).trans
    ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).symm.restrictScalars _)
  have : Module.Finite R (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    have : Module.Finite R ((maximalIdeal R).Fiber S) :=
      .trans (maximalIdeal R).ResidueField _
    .of_surjective e.toLinearMap e.surjective
  refine Module.finite_of_surjective_of_ker_le_nilradical (Ideal.Quotient.mkₐ R
    ((maximalIdeal R).map (algebraMap R S))) Ideal.Quotient.mk_surjective ?_ ?_
  · refine Ideal.mk_ker.trans_le ?_
    rw [Ideal.map_le_iff_le_comap, ← Ring.KrullDimLE.nilradical_eq_maximalIdeal]
    exact fun x hx ↦ IsNilpotent.map hx _
  · rw [← RingHom.ker_coe_toRingHom, Ideal.Quotient.mkₐ_ker]
    exact Ideal.FG.map (IsNoetherian.noetherian _) _
/-
**Algebra.QuasiFinite._root_.Module.Finite.of_quasiFinite** 是 Mathlib 中的一个引理，位于命
名空间 `Algebra.QuasiFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Module.Finite.of_quasiFinite [IsArtinianRing R] [QuasiFinite R S] :
    Module.Finite R S := by
  classical
  let e : R ≃ₐ[R] PrimeSpectrum.PiLocalization R :=
    .ofBijective (IsScalarTower.toAlgHom _ _ _)
      (PrimeSpectrum.discreteTopology_iff_toPiLocalization_bijective.mp inferInstance)
  have : Fintype (PrimeSpectrum R) := .ofFinite _
  let e' : S ≃ₐ[R] Π p : PrimeSpectrum R, Localization p.asIdeal.primeCompl ⊗[R] S :=
    (Algebra.TensorProduct.rid R R S).symm.trans <| (Algebra.TensorProduct.congr .refl e).trans <|
      (Algebra.TensorProduct.piRight _ _ _ _).trans <| AlgEquiv.piCongrRight
      fun _ ↦ Algebra.TensorProduct.comm _ _ _
  have (p : PrimeSpectrum R) : Module.Finite R (Localization p.asIdeal.primeCompl ⊗[R] S) :=
    have : Module.Finite R (Localization.AtPrime p.asIdeal) :=
      .of_surjective (Algebra.linearMap _ _)
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)
    have : Module.Finite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] S) := finite_of_isArtinianRing_of_isLocalRing
    .trans (Localization.AtPrime p.asIdeal) _
  exact .of_surjective e'.symm.toLinearMap e'.symm.surjective
/-
**Algebra.QuasiFinite.iff_of_isArtinianRing** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Q
uasiFinite`。
形式化陈述：iff_of_isArtinianRing [IsArtinianRing R] : QuasiFinite R S ↔ Module.Finite
 R S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_quasiFinite`：∀ {R : Type u_1} {S : Type u_2} [inst : Co
mmRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [IsArtinianRing R]   [Alg
ebra.QuasiFinite R…
· 使用定理 `Algebra.QuasiFinite.instOfFinite`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Finite R S], 
  Algebra.QuasiFinite …
-/
lemma iff_of_isArtinianRing [IsArtinianRing R] :
    QuasiFinite R S ↔ Module.Finite R S :=
  ⟨fun _ ↦ .of_quasiFinite, fun _ ↦ inferInstance⟩

attribute [local instance] TensorProduct.rightAlgebra in
variable (R S T) in
@[stacks 00PO]
/-
**Algebra.QuasiFinite.trans** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.QuasiFinite`。
形式化陈述：trans [QuasiFinite R S] [QuasiFinite S T] : QuasiFinite R T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Algebra.QuasiFinite.iff_of_isArtinianRing`：iff_of_isArtinianRing [IsArti
nianRing R] : QuasiFinite R S ↔ Module.Finite R S
· 使用定理 `Algebra.QuasiFinite.instIsArtinianRingFiber`：∀ {R : Type u_1} {S : Type 
u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra
.QuasiFinite R S] (P : Ideal R) […
· 使用定理 `Algebra.TensorProduct.instSMulCommClassTensorProduct_1`：∀ {R : Type uR} 
{A : Type uA} {B : Type uB} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_
2 : Algebra R A]   [inst_3 : CommSemiring B]…
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.QuasiFinite.finite_fiber`：∀ {R : Type u_1} {S : Type u_2} {inst 
: CommRing R} {inst_1 : CommRing S} {inst_2 : Algebra R S}   [self : Algebra.Qua
siFinite R S] (P : Ide…
· 使用定理 `AlgEquiv.map_mul'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `AlgEquiv.map_add'`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : Comm
Semiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A]
 [inst_…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.TensorProduct.cancelBaseChange_tmul`：cancelBaseChange_tmul (a : 
A) (s : S) (b : B) : Algebra.TensorProduct.cancelBaseChange R S T A B (a otimesₜ
 (s otimesₜ b)) = (s • a) otimesₜ…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
lemma trans [QuasiFinite R S] [QuasiFinite S T] : QuasiFinite R T := by
  refine ⟨fun P hP ↦ ?_⟩
  have : Module.Finite (P.Fiber S) ((P.Fiber S) ⊗[S] T) :=
    iff_of_isArtinianRing.mp inferInstance
  have : Module.Finite P.ResidueField ((P.Fiber S) ⊗[S] T) :=
    .trans (P.Fiber S) _
  let e : P.Fiber S ≃ₐ[S] S ⊗[R] P.ResidueField :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e' : (P.Fiber S) ⊗[S] T ≃ₐ[R] P.Fiber T :=
    ((Algebra.TensorProduct.congr e .refl).restrictScalars R).trans <|
    ((Algebra.TensorProduct.comm _ _ _).restrictScalars R).trans <|
    ((Algebra.TensorProduct.cancelBaseChange _ _ T _ _).restrictScalars R).trans
    (Algebra.TensorProduct.comm _ _ _)
  let e'' : (P.Fiber S) ⊗[S] T ≃ₐ[P.ResidueField] P.Fiber T :=
    { __ := e', commutes' _ := by simp [e', e] }
  exact .of_surjective e''.toLinearMap e''.surjective

omit [Algebra S T] in
/-
**Algebra.QuasiFinite.of_surjective_algHom** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Qu
asiFinite`。
形式化陈述：of_surjective_algHom [QuasiFinite R S] (f : S ->ₐ[R] T) (hf : Function.Sur
jective f) : QuasiFinite R T
参数：f : S ->ₐ[R] T；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用引理 `Algebra.QuasiFinite.trans`：trans [QuasiFinite R S] [QuasiFinite S T] : Q
uasiFinite R T
· 使用定理 `Algebra.QuasiFinite.instOfFinite`：∀ {R : Type u_1} {S : Type u_2} [inst 
: CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [Module.Finite R S], 
  Algebra.QuasiFinite …
-/
lemma of_surjective_algHom [QuasiFinite R S] (f : S →ₐ[R] T) (hf : Function.Surjective f) :
    QuasiFinite R T :=
  let := f.toRingHom.toAlgebra
  let := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : Module.Finite S T := .of_surjective (Algebra.linearMap _ _) hf
  trans R S T
/-
**Algebra.QuasiFinite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.QuasiFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : Ideal S) [QuasiFinite R S] : QuasiFinite R (S ⧸ I) :=
  of_surjective_algHom (Ideal.Quotient.mkₐ _ _) Ideal.Quotient.mk_surjective

omit [Algebra S T] in
/-
**Algebra.QuasiFinite.iff_of_algEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.QuasiFi
nite`。
形式化陈述：iff_of_algEquiv (e : S ≃ₐ[R] T) : Algebra.QuasiFinite R S ↔ Algebra.QuasiF
inite R T
参数：e : S ≃ₐ[R] T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.QuasiFinite.of_surjective_algHom`：of_surjective_algHom [QuasiFin
ite R S] (f : S ->ₐ[R] T) (hf : Function.Surjective f) : QuasiFinite R T
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
lemma iff_of_algEquiv (e : S ≃ₐ[R] T) :
    Algebra.QuasiFinite R S ↔ Algebra.QuasiFinite R T :=
  ⟨fun _ ↦ .of_surjective_algHom e.toAlgHom e.surjective,
    fun _ ↦ .of_surjective_algHom e.symm.toAlgHom e.symm.surjective⟩
/-
**Algebra.QuasiFinite.of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Quasi
Finite`。
形式化陈述：of_isLocalization (M : Submonoid S) [IsLocalization M T] [QuasiFinite R S]
 : QuasiFinite R T
参数：M : Submonoid S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.QuasiFinite.trans`：trans [QuasiFinite R S] [QuasiFinite S T] : Q
uasiFinite R T
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `TensorProduct.span_tmul_eq_top`：span_tmul_eq_top : Submodule.span R { t 
: M otimes[R] N | exists m n, m otimesₜ n = t } = ⊤
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsUnit.mul_left_injective`：∀ {M : Type u_1} [inst : Monoid M] {b : M}, I
sUnit b → Function.Injective fun x => x * b
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
（共 41 条，此处仅展示前 30 条）
-/
lemma of_isLocalization (M : Submonoid S) [IsLocalization M T] [QuasiFinite R S] :
    QuasiFinite R T :=
  letI : QuasiFinite S T := by
    refine ⟨fun P hP ↦ .of_surjective (Algebra.linearMap P.ResidueField (P.Fiber T)) ?_⟩
    rw [← LinearMap.coe_restrictScalars (R := S), ← LinearMap.range_eq_top,
      ← top_le_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨p, s, rfl⟩
    obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
    use s • p / algebraMap _ _ t.1
    apply ((IsLocalization.map_units T t).map
      Algebra.TensorProduct.includeRight).mul_left_injective
    by_cases ht : algebraMap _ P.ResidueField t.1 = 0
    · simp [ht]
    trans (s • p) ⊗ₜ[S] 1
    · simp [div_mul_cancel₀ _ ht]
    · dsimp; simp [Algebra.algebraMap_eq_smul_one, smul_tmul]
  trans R S T
/-
**Algebra.QuasiFinite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.QuasiFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Submonoid S) [QuasiFinite R S] : QuasiFinite R (Localization M) := of_isLocalization M
/-
**Algebra.QuasiFinite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.QuasiFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [IsFractionRing R S] : QuasiFinite R S :=
  of_isLocalization (nonZeroDivisors R)
/-
**Algebra.QuasiFinite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.QuasiFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiFinite R S] (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime] :
    Module.Finite p.ResidueField (Localization.AtPrime q) :=
  .of_quasiFinite
/-
**Algebra.QuasiFinite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.QuasiFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P : Ideal S) [P.IsPrime] [QuasiFinite R S] : QuasiFinite R P.ResidueField :=
  .trans _ (S ⧸ P) _

variable (R S T) in
/-
**Algebra.QuasiFinite.of_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Quas
iFinite`。
形式化陈述：of_restrictScalars [QuasiFinite R T] : QuasiFinite S T
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_restrictScalars'`：coe_restrictScalars' (f : A ->ₐ[S] B) : (re
strictScalars R f : A -> B) = f
· 使用引理 `AlgHom.coe_toLinearMap`：coe_toLinearMap : ⇑φ.toLinearMap = φ
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `TensorProduct.span_tmul_eq_top`：span_tmul_eq_top : Submodule.span R { t 
: M otimes[R] N | exists m n, m otimesₜ n = t } = ⊤
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Finite.of_quasiFinite`：∀ {R : Type u_1} {S : Type u_2} [inst : Co
mmRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [IsArtinianRing R]   [Alg
ebra.QuasiFinite R…
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
-/
lemma of_restrictScalars [QuasiFinite R T] : QuasiFinite S T := by
  refine ⟨fun P hP ↦ ?_⟩
  let f : P.ResidueField ⊗[R] T →ₐ[P.ResidueField] P.Fiber T :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (Algebra.TensorProduct.includeRight.restrictScalars R) fun _ _ ↦ .all _ _
  have hf : Function.Surjective f := by
    rw [← AlgHom.coe_restrictScalars' (R := S), ← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top,
      ← top_le_iff, ← TensorProduct.span_tmul_eq_top, Submodule.span_le]
    rintro _ ⟨a, b, rfl⟩
    exact ⟨a ⊗ₜ b, by simp [f]⟩
  have : Module.Finite P.ResidueField (P.ResidueField ⊗[R] T) := .of_quasiFinite
  exact .of_surjective f.toLinearMap hf

variable (R S) in
/-
**Algebra.QuasiFinite.discreteTopology_primeSpectrum** 是 Mathlib 中的一个引理，位于命名空间 `
Algebra.QuasiFinite`。
形式化陈述：discreteTopology_primeSpectrum [DiscreteTopology (PrimeSpectrum R)] [Quasi
Finite R S] : DiscreteTopology (PrimeSpectrum S)
参数：PrimeSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isDiscrete_univ_iff`：isDiscrete_univ_iff : IsDiscrete (Set.univ : Set X)
 ↔ DiscreteTopology X
· 使用引理 `Algebra.QuasiFinite.isDiscrete_comap_preimage`：isDiscrete_comap_preimage
 [QuasiFinite R S] {s : Set (PrimeSpectrum R)} (hs : IsDiscrete s) : IsDiscrete 
(PrimeSpectrum.comap (algebraMap R …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma discreteTopology_primeSpectrum [DiscreteTopology (PrimeSpectrum R)] [QuasiFinite R S] :
    DiscreteTopology (PrimeSpectrum S) :=
  isDiscrete_univ_iff.mp
    (isDiscrete_comap_preimage (R := R) (S := S) (isDiscrete_univ_iff.mpr ‹_›))

variable (R S) in
/-
**Algebra.QuasiFinite.finite_primeSpectrum** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Qu
asiFinite`。
形式化陈述：finite_primeSpectrum [Finite (PrimeSpectrum R)] [QuasiFinite R S] : Finite
 (PrimeSpectrum S)
参数：PrimeSpectrum R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_univ_iff`：finite_univ_iff : (@univ α).Finite ↔ Finite α
· 使用引理 `Algebra.QuasiFinite.finite_comap_preimage`：finite_comap_preimage [QuasiF
inite R S] {s : Set (PrimeSpectrum R)} (hs : s.Finite) : (PrimeSpectrum.comap (a
lgebraMap R S) ⁻¹' s).Finite
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma finite_primeSpectrum [Finite (PrimeSpectrum R)] [QuasiFinite R S] :
    Finite (PrimeSpectrum S) :=
  Set.finite_univ_iff.mp
    (finite_comap_preimage (Set.finite_univ (α := PrimeSpectrum R)))

omit [Algebra S T] in
/-
**Algebra.QuasiFinite.of_forall_exists_mul_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `
Algebra.QuasiFinite`。
形式化陈述：of_forall_exists_mul_mem_range [QuasiFinite R S] (f : S ->ₐ[R] T) (H : for
all x : T, exists s : S, IsUnit (f s) ∧ x * f s in f.range) : QuasiFinite R T
参数：f : S ->ₐ[R] T；H : forall x : T, exists s : S, IsUnit (f s) ∧ x * f s in f.ra
nge。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.lift_mk'`：lift_mk' (x y) : lift hg (mk' S x y) = g x * ↑(
IsUnit.liftRight (g.toMonoidHom.domRestrict M) hg y)⁻¹
· 使用引理 `Algebra.QuasiFinite.of_surjective_algHom`：of_surjective_algHom [QuasiFin
ite R S] (f : S ->ₐ[R] T) (hf : Function.Surjective f) : QuasiFinite R T
· 使用定理 `Algebra.QuasiFinite.instLocalization`：∀ {R : Type u_1} {S : Type u_2} [i
nst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (M : Submonoid S)
   [Algebra.QuasiFinite R …
-/
lemma of_forall_exists_mul_mem_range [QuasiFinite R S] (f : S →ₐ[R] T)
    (H : ∀ x : T, ∃ s : S, IsUnit (f s) ∧ x * f s ∈ f.range) :
    QuasiFinite R T := by
  let φ : Localization ((IsUnit.submonoid T).comap f) →ₐ[R] T :=
    IsLocalization.liftAlgHom (M := (IsUnit.submonoid T).comap f) (f := f)
      (by simp [IsUnit.mem_submonoid_iff])
  suffices Function.Surjective φ from .of_surjective_algHom φ this
  intro x
  obtain ⟨s, hs, t, ht⟩ := H x
  refine ⟨IsLocalization.mk' (M := (IsUnit.submonoid T).comap f) _ t ⟨s, hs⟩, ?_⟩
  simpa [φ, IsLocalization.lift_mk', Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]

omit [Algebra S T] in
/-
**Algebra.QuasiFinite.eq_of_le_of_under_eq** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Qu
asiFinite`。
形式化陈述：eq_of_le_of_under_eq [QuasiFinite R S] (P Q : Ideal S) [P.IsPrime] [Q.IsPr
ime] (h₁ : P <= Q) (h₂ : P.under R = Q.under R) : P = Q
参数：P Q : Ideal S；h₁ : P <= Q；h₂ : P.under R = Q.under R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsDiscrete.eq_of_specializes`：IsDiscrete.eq_of_specializes (hs : IsDiscr
ete s) {a b : X} (hab : a ⤳ b) (ha : a in s) (hb : b in s) : a = b
· 使用定理 `Ideal.IsPrime.under`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type 
u_3} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B)   [hP : P.IsPrim
e], (Idea…
· 使用引理 `Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton`：isDiscrete_coma
p_preimage_singleton [QuasiFinite R S] (P : PrimeSpectrum R) : IsDiscrete (Prime
Spectrum.comap (algebraMap R S) ⁻¹' {P})
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma eq_of_le_of_under_eq [QuasiFinite R S] (P Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (h₁ : P ≤ Q) (h₂ : P.under R = Q.under R) : P = Q :=
  congr($((isDiscrete_comap_preimage_singleton ⟨_, inferInstance⟩).eq_of_specializes
    (a := ⟨P, ‹_›⟩) (b := ⟨Q, ‹_›⟩) (by simpa [← PrimeSpectrum.le_iff_specializes]) rfl
    (PrimeSpectrum.ext h₂.symm)).1)
/-
**Algebra.QuasiFinite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.QuasiFinite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiFinite R S] (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsPrime] [Q.LiesOver P]
    [Algebra (Localization.AtPrime P) (Localization.AtPrime Q)]
    [Localization.AtPrime.IsLiesOverAlgebra P Q] :
    Module.Finite P.ResidueField Q.ResidueField :=
  have : QuasiFinite P.ResidueField Q.ResidueField := .of_restrictScalars R _ _
  .of_quasiFinite

section Finite

/-
**Algebra.QuasiFinite.iff_finite_comap_preimage_singleton** 是 Mathlib 中的一个引理，位于命
名空间 `Algebra.QuasiFinite`。
形式化陈述：iff_finite_comap_preimage_singleton [FiniteType R S] : QuasiFinite R S ↔ f
orall x, (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}).Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.QuasiFinite.finite_comap_preimage_singleton`：finite_comap_preima
ge_singleton [QuasiFinite R S] (P : PrimeSpectrum R) : (PrimeSpectrum.comap (alg
ebraMap R S) ⁻¹' {P}).Finite
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.finite_iff_isArtinianRing`：Module.finite_iff_isArtinianRing [IsAr
tinianRing R] : Module.Finite R A ↔ IsArtinianRing A
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `isArtinianRing_iff_isNoetherianRing_krullDimLE_zero`：∀ {R : Type u_3} [i
nst : CommRing R], IsArtinianRing R ↔ IsNoetherianRing R ∧ Ring.KrullDimLE 0 R
· 使用引理 `isJacobsonRing_of_finiteType`：isJacobsonRing_of_finiteType {A B : Type*}
 [CommRing A] [CommRing B] [Algebra A B] [IsJacobsonRing A] [Algebra.FiniteType 
A B] : IsJacobsonR…
· 使用定理 `instIsJacobsonRingOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : CommRin
g R] [Ring.KrullDimLE 0 R], IsJacobsonRing R
· 使用定理 `IsArtinianRing.instKrullDimLEOfNatNat`：∀ (R : Type u_1) [inst : CommRing
 R] [IsArtinianRing R], Ring.KrullDimLE 0 R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Equiv.finite_iff`：Equiv.finite_iff (f : α ≃ β) : Finite α ↔ Finite β
· 使用定理 `Algebra.FiniteType.isNoetherianRing`：isNoetherianRing (R S : Type*) [Com
mRing R] [CommRing S] [Algebra R S] [h : Algebra.FiniteType R S] [IsNoetherianRi
ng R] : IsNoetherianRing …
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero`：discreteT
opology_iff_finite_and_krullDimLE_zero : DiscreteTopology (PrimeSpectrum R) ↔ Fi
nite (PrimeSpectrum R) ∧ Ring.KrullDimLE 0 R
· 使用定理 `instDiscreteTopologyOfFiniteOfJacobsonSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [Finite X] [JacobsonSpace X], DiscreteTopology X
· 使用定理 `PrimeSpectrum.instJacobsonSpaceOfIsJacobsonRing`：∀ {R : Type u_1} [inst 
: CommRing R] [IsJacobsonRing R], JacobsonSpace (PrimeSpectrum R)
-/
lemma iff_finite_comap_preimage_singleton [FiniteType R S] :
    QuasiFinite R S ↔ ∀ x, (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}).Finite := by
  refine ⟨fun H _ ↦ finite_comap_preimage_singleton _, fun H ↦ ⟨fun P _ ↦ ?_⟩⟩
  rw [Module.finite_iff_isArtinianRing, isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
  have : IsJacobsonRing (P.Fiber S) := isJacobsonRing_of_finiteType (A := P.ResidueField)
  have : Finite (PrimeSpectrum (P.Fiber S)) :=
    (PrimeSpectrum.preimageEquivFiber R S ⟨P, ‹_›⟩).finite_iff.mp (H ⟨P, ‹_›⟩)
  exact ⟨Algebra.FiniteType.isNoetherianRing P.ResidueField _,
    (PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mp inferInstance).right⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.QuasiFinite.iff_finite_primesOver** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Q
uasiFinite`。
形式化陈述：iff_finite_primesOver [FiniteType R S] : QuasiFinite R S ↔ forall I : Idea
l R, I.IsPrime -> (I.primesOver S).Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.QuasiFinite.iff_finite_comap_preimage_singleton`：iff_finite_coma
p_preimage_singleton [FiniteType R S] : QuasiFinite R S ↔ forall x, (PrimeSpectr
um.comap (algebraMap R S) ⁻¹' {x}).Finite
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_image_iff`：finite_image_iff {s : Set α} {f : α -> β} (hi : In
jOn f s) : (f '' s).Finite ↔ s.Finite
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iff_finite_primesOver [FiniteType R S] :
    QuasiFinite R S ↔ ∀ I : Ideal R, I.IsPrime → (I.primesOver S).Finite := by
  rw [iff_finite_comap_preimage_singleton,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall]
  refine forall₂_congr fun I hI ↦ ?_
  rw [← Set.finite_image_iff (Function.Injective.injOn fun _ _ ↦ PrimeSpectrum.ext)]
  congr!
  ext J
  simp [(PrimeSpectrum.equivSubtype S).exists_congr_left, PrimeSpectrum.ext_iff, eq_comm,
    PrimeSpectrum.equivSubtype, Ideal.primesOver, and_comm, Ideal.liesOver_iff, Ideal.under]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `T` is both a finite type `R`-algebra, and the localization of an integral `R`-algebra
(away from an element), then `T` is quasi-finite over `R` -/
/-
**Algebra.QuasiFinite.of_isIntegral_of_finiteType** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebra.QuasiFinite`。
形式化陈述：of_isIntegral_of_finiteType [Algebra.IsIntegral R S] [Algebra.FiniteType R
 T] (s : S) [IsLocalization.Away s T] : Algebra.QuasiFinite R T
参数：s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsLocalization.Away.algebraMap_isUnit`：algebraMap_isUnit : IsUnit (algeb
raMap R S x)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.Away.lift_eq`：lift_eq (hg : IsUnit (g x)) (a : R) : lift 
x hg (algebraMap R S a) = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `IsScalarTower.to₁₃₄`：∀ (M : Type u_9) (N : Type u_10) (P : Type u_11) (Q
 : Type u_12) [inst : SMul M N] [inst_1 : SMul M P]   [inst_2 : SMul M Q] [inst_
3 : SMul …
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `IsIntegral.algebraMap`：∀ {R : Type u_1} {A : Type u_2} {B : Type u_3} [i
nst : CommRing R] [inst_1 : CommRing A] [inst_2 : Ring B]   [inst_3 : Algebra R 
A] [inst_4 …
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_eq_iff_eq_mul`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Algebra.smul_mul_assoc`：∀ {R : Type u} {A : Type w} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (r : R) (x y : A),   r • x * y 
= r • (x * y…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
（共 67 条，此处仅展示前 30 条）

--- 原说明 ---
If `T` is both a finite type `R`-algebra, and the localization of an integral `R
`-algebra
(away from an element), then `T` is quasi-finite over `R`
-/
lemma of_isIntegral_of_finiteType [Algebra.IsIntegral R S] [Algebra.FiniteType R T]
    (s : S) [IsLocalization.Away s T] : Algebra.QuasiFinite R T := by
  let A := Algebra.adjoin R {s}
  let sA : A := ⟨s, Algebra.subset_adjoin (by simp)⟩
  let f : Localization.Away sA →+* T := IsLocalization.Away.lift sA (g := algebraMap _ _)
    (IsLocalization.Away.algebraMap_isUnit s)
  let := f.toAlgebra
  let : Algebra A (Localization.Away sA) := OreLocalization.instAlgebra
  let : SMul A (Localization.Away sA) := Algebra.toSMul
  let : MulAction A (Localization.Away sA) := Algebra.toModule.toDistribMulAction.toMulAction
  have : IsScalarTower R A (Localization.Away sA) := OreLocalization.instIsScalarTower
  have : IsScalarTower A (Localization.Away sA) T :=
    .of_algebraMap_eq (by simp [f, RingHom.algebraMap_toAlgebra, A])
  have : IsScalarTower R (Localization.Away sA) T := .to₁₃₄ R A (Localization.Away sA) T
  have : Algebra.IsIntegral (Localization.Away sA) T := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨x, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.exists_mk'_eq (.powers s) x
    have : _root_.IsIntegral (Localization.Away sA) (algebraMap S T x) :=
      (Algebra.IsIntegral.isIntegral (R := R) x).algebraMap.tower_top
    convert! this.smul (Localization.Away.invSelf sA ^ n)
    rw [IsLocalization.mk'_eq_iff_eq_mul]
    simp only [map_pow, Algebra.smul_mul_assoc]
    trans (sA • Localization.Away.invSelf sA) ^ n • (algebraMap S T x)
    · simp [Algebra.smul_def, -map_pow, Localization.Away.invSelf, Localization.mk_eq_mk']
    · simp only [Algebra.smul_def, map_pow, map_mul, mul_pow,
        ← IsScalarTower.algebraMap_apply, Subalgebra.algebraMap_def, sA]
      ring
  have : Module.Finite (Localization.Away sA) T :=
    have : Algebra.FiniteType (Localization.Away sA) T := .of_restrictScalars_finiteType R _ _
    Algebra.IsIntegral.finite
  have : Module.Finite R A :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral _)
  have : Algebra.QuasiFinite R (Localization.Away sA) := .of_isLocalization (.powers sA)
  exact .trans _ (Localization.Away sA) _

end Finite

end QuasiFinite

section QuasiFiniteAt

variable (R) in
/-- If `S` is an `R`-algebra and `p` a prime of `S`, we say that `S` is `R`-quasi-finite at `p`
if `Sₚ` is `R`-quasi-finite. In the case where `S` is (essentially) of finite type over `R`,
this is equivalent to the usual definition that `p` is isolated in its fiber.
See `Ideal.exists_notMem_forall_mem_of_ne_of_liesOver`. -/
/-
**Algebra.QuasiFiniteAt** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：QuasiFiniteAt (p : Ideal S) [p.IsPrime] : Prop
参数：p : Ideal S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is an `R`-algebra and `p` a prime of `S`, we say that `S` is `R`-quasi-fi
nite at `p`
if `Sₚ` is `R`-quasi-finite. In the case where `S` is (essentially) of finite ty
pe over `R`,
this is equivalent to the usual definition that `p` is isolated in its fiber.
See `Ideal.exists_notMem_forall_mem_of_ne_of_liesOver`.
-/
abbrev QuasiFiniteAt (p : Ideal S) [p.IsPrime] : Prop :=
  QuasiFinite R (Localization.AtPrime p)
/-
**Algebra.QuasiFiniteAt.baseChange** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.QuasiFinit
eAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (p : Ideal S)   [inst_3 : p.IsPrime] [Algebra.QuasiFinite
At R p] {A : Type u_4} [inst_5 : CommRing A] [inst_6 : Algebra R A]   (q : Ideal
 (TensorProduct R A S)) [inst_7 : q.IsPrime],   p = Ideal.comap Algebra.TensorPr
oduct.includeRight.toRingHom q → Algebra.QuasiFiniteAt A q
参数：p : Ideal S；q : Ideal (TensorProduct R A S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Algebra.TensorProduct.ext_ring`：∀ {R : Type u_4} {S : Type u_5} {A : Typ
e u_6} {B : Type u_7} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_
2 : Semiring A] [ins…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用引理 `Algebra.QuasiFinite.of_forall_exists_mul_mem_range`：of_forall_exists_mul
_mem_range [QuasiFinite R S] (f : S ->ₐ[R] T) (H : forall x : T, exists s : S, I
sUnit (f s) ∧ x * f s in f.range) : Quas…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_spec_mk`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S]
 [inst_3 : IsLoc…
-/
lemma QuasiFiniteAt.baseChange (p : Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
    {A : Type*} [CommRing A] [Algebra R A] (q : Ideal (A ⊗[R] S)) [q.IsPrime]
    (hq : p = q.comap Algebra.TensorProduct.includeRight.toRingHom) :
    QuasiFiniteAt A q := by
  let f : A ⊗[R] Localization.AtPrime p →ₐ[A] Localization.AtPrime q :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _) ⟨Localization.localRingHom _ _ _ hq, by
      simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime p),
        IsScalarTower.algebraMap_apply R (A ⊗[R] S) (Localization.AtPrime q)]⟩ fun _ _ ↦ .all _ _
  let g : A ⊗[R] S →ₐ[A] A ⊗[R] Localization.AtPrime p :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  have : f.comp g = IsScalarTower.toAlgHom _ _ _ := by ext; simp [f, g]
  replace this (x : _) : f (g x) = algebraMap _ _ x := DFunLike.congr_fun this x
  refine .of_forall_exists_mul_mem_range f fun x ↦ ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq q.primeCompl x
  refine ⟨g s, this s ▸ IsLocalization.map_units _ ⟨s, hs⟩, ?_⟩
  rw [this, IsLocalization.mk'_spec_mk]
  exact ⟨g x, this x⟩

set_option backward.isDefEq.respectTransparency false in
omit [Algebra S T] in
/-
**Algebra.QuasiFiniteAt.of_surjectiveOnStalks** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.QuasiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] (p : Ideal S) [inst_5 : p.IsPrime] [Algebra.QuasiFiniteAt R p]   (f : S →ₐ[
R] T),   f.SurjectiveOnStalks → ∀ (q : Ideal T) [inst_7 : q.IsPrime], p = Ideal.
comap f.toRingHom q → Algebra.QuasiFiniteAt R q
参数：p : Ideal S；f : S →ₐ[R] T；q : Ideal T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.QuasiFinite.of_surjective_algHom`：of_surjective_algHom [QuasiFin
ite R S] (f : S ->ₐ[R] T) (hf : Function.Surjective f) : QuasiFinite R T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Localization.localRingHom_to_map`：localRingHom_to_map (J : Ideal P) [J.I
sPrime] (f : R ->+* P) (hIJ : I = J.comap f) (x : R) : localRingHom I J f hIJ (a
lgebraMap _ _ x) = alg…
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma QuasiFiniteAt.of_surjectiveOnStalks (p : Ideal S) [p.IsPrime] [QuasiFiniteAt R p]
    (f : S →ₐ[R] T) (hf : f.SurjectiveOnStalks) (q : Ideal T) [q.IsPrime]
    (hq : p = q.comap f.toRingHom) :
    QuasiFiniteAt R q := by
  subst hq
  refine .of_surjective_algHom ⟨Localization.localRingHom _ q f.toRingHom rfl, ?_⟩ (hf q ‹_›)
  simp [IsScalarTower.algebraMap_apply R S (Localization.AtPrime (q.comap _)),
    IsScalarTower.algebraMap_apply R T (Localization.AtPrime _)]
/-
**Algebra.QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver** 是 Mathlib 中的一个定理，位于命
名空间 `Algebra.QuasiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] [inst_5 : Algebra S T] [IsScalarTower R S T] (p : Ideal S)   [inst_7 : p.Is
Prime] [Algebra.QuasiFiniteAt R p],   (algebraMap S T).SurjectiveOnStalks → ∀ (q
 : Ideal T) [inst_9 : q.IsPrime] [q.LiesOver p], Algebra.QuasiFiniteAt R q
参数：p : Ideal S；algebraMap S T；q : Ideal T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`：∀ {R : Type u_1} {S : Type 
u_2} {T : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing
 T]   [inst_3 : Algebra R S] [ins…
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
-/
lemma QuasiFiniteAt.of_surjectiveOnStalks_of_liesOver (p : Ideal S) [p.IsPrime]
    [QuasiFiniteAt R p] (hf : (algebraMap S T).SurjectiveOnStalks) (q : Ideal T) [q.IsPrime]
    [q.LiesOver p] : QuasiFiniteAt R q :=
  .of_surjectiveOnStalks p (IsScalarTower.toAlgHom R S T) hf _ (q.over_def p)
/-
**Algebra.QuasiFiniteAt.comap_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.QuasiF
initeAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {T : Type u_3} [inst : CommRing R] [inst_1
 : CommRing S] [inst_2 : CommRing T]   [inst_3 : Algebra R S] [inst_4 : Algebra 
R T] (p : Ideal S) [inst_5 : p.IsPrime] [Algebra.QuasiFiniteAt R p]   (f : T ≃ₐ[
R] S), Algebra.QuasiFiniteAt R (Ideal.comap f.toRingEquiv.toRingHom p)
参数：p : Ideal S；f : T ≃ₐ[R] S；Ideal.comap f.toRingEquiv.toRingHom p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.QuasiFiniteAt.of_surjectiveOnStalks`：∀ {R : Type u_1} {S : Type 
u_2} {T : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : CommRing
 T]   [inst_3 : Algebra R S] [ins…
· 使用引理 `RingHom.surjectiveOnStalks_of_surjective`：surjectiveOnStalks_of_surjecti
ve (h : Function.Surjective f) : SurjectiveOnStalks f
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
instance QuasiFiniteAt.comap_algEquiv (p : Ideal S) [p.IsPrime] [Algebra.QuasiFiniteAt R p]
    (f : T ≃ₐ[R] S) : QuasiFiniteAt R (p.comap f.toRingHom) :=
  .of_surjectiveOnStalks p f.symm.toAlgHom
    (RingHom.surjectiveOnStalks_of_surjective f.symm.surjective) _ (by ext; simp)

omit [Algebra S T] in
/-
**Algebra.QuasiFiniteAt.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.QuasiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] {P Q : Ideal S}   [inst_3 : P.IsPrime] [inst_4 : Q.IsPrim
e], P ≤ Q → ∀ [Algebra.QuasiFiniteAt R Q], Algebra.QuasiFiniteAt R P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用引理 `Algebra.QuasiFinite.of_forall_exists_mul_mem_range`：of_forall_exists_mul
_mem_range [QuasiFinite R S] (f : S ->ₐ[R] T) (H : forall x : T, exists s : S, I
sUnit (f s) ∧ x * f s in f.range) : Quas…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.coe_toAlgHom`：coe_toAlgHom : ↑(toAlgHom R S A) = algebraMa
p S A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsLocalization.lift.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R]
 {M M_1 : Submonoid R} (e_M : M = M_1) {S : Type u_2} [inst_1 : CommSemiring S] 
  [inst_2 : Algebra …
· 使用定理 `IsLocalization.lift_eq`：lift_eq (x : R) : lift hg ((algebraMap R S) x) =
 g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsLocalization.mk'_spec_mk`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S]
 [inst_3 : IsLoc…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma QuasiFiniteAt.of_le {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
    (h₁ : P ≤ Q) [QuasiFiniteAt R Q] :
    QuasiFiniteAt R P := by
  let f : Localization.AtPrime Q →ₐ[R] Localization.AtPrime P :=
    IsLocalization.liftAlgHom (M := Q.primeCompl) (f := IsScalarTower.toAlgHom _ _ _) <| by
      simp only [IsScalarTower.coe_toAlgHom', Subtype.forall, Ideal.mem_primeCompl_iff]
      exact fun a ha ↦ IsLocalization.map_units (M := P.primeCompl) _ ⟨a, fun h ↦ ha (h₁ h)⟩
  refine .of_forall_exists_mul_mem_range f fun x ↦ ?_
  obtain ⟨x, ⟨s, hs⟩, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
  exact ⟨algebraMap _ _ s, by simpa [f] using IsLocalization.map_units _ ⟨s, hs⟩,
    algebraMap _ _ x, by simp [f]⟩

omit [Algebra S T] in
/-
**Algebra.QuasiFiniteAt.eq_of_le_of_under_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
QuasiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] {P Q : Ideal S}   [P.IsPrime] [inst_4 : Q.IsPrime], P ≤ Q
 → Ideal.under R P = Ideal.under R Q → ∀ [Algebra.QuasiFiniteAt R Q], P = Q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.isPrime_map_of_isLocalizationAtPrime`：Ideal.isPrime_map_of_isLocal
izationAtPrime {p : Ideal R} [p.IsPrime] (hpq : p <= q) : (p.map (algebraMap R S
)).IsPrime
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用引理 `Algebra.QuasiFinite.eq_of_le_of_under_eq`：eq_of_le_of_under_eq [QuasiFin
ite R S] (P Q : Ideal S) [P.IsPrime] [Q.IsPrime] (h₁ : P <= Q) (h₂ : P.under R =
 Q.under R) : P = Q
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `IsLocalRing.le_maximalIdeal_of_isPrime`：le_maximalIdeal_of_isPrime (p : 
Ideal R) [hp : p.IsPrime] : p <= maximalIdeal R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.under_under`：under_under : (𝔓.under B).under A = 𝔓.under A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Ideal.under_map_of_isLocalizationAtPrime`：Ideal.under_map_of_isLocalizat
ionAtPrime {p : Ideal R} [p.IsPrime] (hpq : p <= q) : (p.map (algebraMap R S)).u
nder R = p
· 使用定理 `Localization.AtPrime.under_maximalIdeal`：∀ {R : Type u_1} [inst : CommSe
miring R] {I : Ideal R} [hI : I.IsPrime],   Ideal.under R (IsLocalRing.maximalId
eal (Localization I.primeComp…
-/
lemma QuasiFiniteAt.eq_of_le_of_under_eq {P Q : Ideal S} [P.IsPrime] [Q.IsPrime]
    (h₁ : P ≤ Q) (h₂ : P.under R = Q.under R) [QuasiFiniteAt R Q] :
    P = Q := by
  have := Q.isPrime_map_of_isLocalizationAtPrime h₁ (S := Localization.AtPrime Q)
  have H := QuasiFinite.eq_of_le_of_under_eq (R := R)
    (Ideal.map (algebraMap S (Localization.AtPrime Q)) P) _
    (IsLocalRing.le_maximalIdeal_of_isPrime _) (by
      convert! h₂ <;> rw [← Ideal.under_under (B := S)]
      · rw [Q.under_map_of_isLocalizationAtPrime h₁]
      · rw [Localization.AtPrime.under_maximalIdeal])
  rw [← Localization.AtPrime.under_maximalIdeal (I := Q), ← H,
    Q.under_map_of_isLocalizationAtPrime h₁]
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime] [P.LiesOver p] [QuasiFiniteAt R P]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [Localization.AtPrime.IsLiesOverAlgebra p P] :
    Module.Finite p.ResidueField P.ResidueField := by
  let m := IsLocalRing.maximalIdeal (Localization.AtPrime P)
  let : m.LiesOver p := .trans _ P _
  let := Localization.AtPrime.algebraOfLiesOver p m
  let := Localization.AtPrime.algebraOfLiesOver P m
  let e := AlgEquiv.ofBijective (IsScalarTower.toAlgHom p.ResidueField P.ResidueField
    m.ResidueField) ((RingHom.surjectiveOnStalks_of_isLocalization
        P.primeCompl _).residueFieldMap_bijective P m (m.over_def P))
  exact .of_surjective e.symm.toLinearMap e.symm.surjective

set_option backward.defeqAttrib.useBackward true in
/-
**Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 
`Algebra.QuasiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (p : Ideal S)   [inst_3 : p.IsPrime] [IsArtinianRing R] [
Algebra.EssFiniteType R S] [Algebra.QuasiFiniteAt R p],   ∃ f ∉ p, ↑(PrimeSpectr
um.basicOpen f) = {{ asIdeal := p, isPrime := inst_3 }}
参数：p : Ideal S；PrimeSpectrum.basicOpen f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalizedModule.map_units`：∀ {R : Type u_1} {inst : CommSemiring R} {M
 : Type u_2} {M' : Type u_3} {inst_1 : AddCommMonoid M}   {inst_2 : AddCommMonoi
d M'} {inst_3 : _…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `Module.Finite.of_quasiFinite`：∀ {R : Type u_1} {S : Type u_2} [inst : Co
mmRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] [IsArtinianRing R]   [Alg
ebra.QuasiFinite R…
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsArtinianRing.of_finite`：IsArtinianRing.of_finite (R S) [Ring R] [Ring 
S] [Module R S] [IsScalarTower R S S] [IsArtinianRing R] [Module.Finite R S] : I
sArtinianRing …
· 使用定理 `Algebra.EssFiniteType.isNoetherianRing`：∀ (R : Type u_3) (S : Type u_4) 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.EssF
initeType R S] [IsNoetherian…
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用引理 `Module.finitePresentation_of_finite`：Module.finitePresentation_of_finite
 [IsNoetherianRing R] [h : Module.Finite R M] : Module.FinitePresentation R M
· 使用引理 `IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation`
：IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation [Module
.Finite R M] [Module.FinitePresentation R M'] : exists r in S…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `isLocalizedModule_iff_isLocalization'`：isLocalizedModule_iff_isLocalizat
ion' : IsLocalizedModule S (Algebra.linearMap R A) ↔ IsLocalization S A
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
（共 47 条，此处仅展示前 30 条）
-/
lemma QuasiFiniteAt.exists_basicOpen_eq_singleton
    (p : Ideal S) [p.IsPrime] [IsArtinianRing R] [Algebra.EssFiniteType R S]
    [Algebra.QuasiFiniteAt R p] :
    ∃ f ∉ p, (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum S)) = {⟨p, ‹_›⟩} := by
  have : IsLocalizedModule p.primeCompl (.id (R := S) (M := Localization.AtPrime p)) :=
    ⟨IsLocalizedModule.map_units (Algebra.linearMap S (Localization.AtPrime p)),
      fun y ↦ ⟨⟨y, 1⟩, by simp⟩, by simpa using ⟨1, p.primeCompl.one_mem⟩⟩
  have : Module.Finite R (Localization.AtPrime p) := .of_quasiFinite
  have : Module.Finite S (Localization.AtPrime p) := .of_restrictScalars_finite R _ _
  have : IsArtinianRing (Localization.AtPrime p) := .of_finite R _
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  have : Module.FinitePresentation S (Localization.AtPrime p) :=
    Module.finitePresentation_of_finite _ _
  obtain ⟨r, hrp, H⟩ := IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation
    p.primeCompl (Algebra.linearMap S (Localization.AtPrime p))
  have : IsLocalization (.powers r) (Localization.AtPrime p) :=
    (isLocalizedModule_iff_isLocalization' _ _).mp H
  let φ : Localization.Away r ≃ₐ[S] Localization.AtPrime p :=
    IsLocalization.algEquiv (.powers r) _ _
  refine ⟨r, hrp, subset_antisymm (fun q hrq ↦ ?_) (Set.singleton_subset_iff.mpr hrp)⟩
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r).ge hrq
  obtain ⟨q, rfl⟩ := (PrimeSpectrum.comapEquiv φ.toRingEquiv).symm.surjective q
  -- As Sₚ is an artinian local ring, its prime spectrum is a singleton.
  obtain rfl : q = IsLocalRing.closedPoint _ := Subsingleton.elim _ _
  ext1
  dsimp [-RingEquiv.symm_mk]
  rw [Ideal.comap_comap, ← AlgEquiv.toAlgHom_toRingHom, AlgHom.comp_algebraMap]
  exact IsLocalization.AtPrime.under_maximalIdeal _ _

/-- If `R` is an artinian ring, and `S` is a finite type `R`-algebra `R`-quasi-finite at `p`,
then `{p}` is clopen in `Spec S`. -/
/-
**Algebra.QuasiFiniteAt.isClopen_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Qu
asiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (p : PrimeSpectrum S)   [IsArtinianRing R] [Algebra.Finit
eType R S] [Algebra.QuasiFiniteAt R p.asIdeal], IsClopen {p}
参数：p : PrimeSpectrum S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `isJacobsonRing_of_finiteType`：isJacobsonRing_of_finiteType {A B : Type*}
 [CommRing A] [CommRing B] [Algebra A B] [IsJacobsonRing A] [Algebra.FiniteType 
A B] : IsJacobsonR…
· 使用定理 `instIsJacobsonRingOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : CommRin
g R] [Ring.KrullDimLE 0 R], IsJacobsonRing R
· 使用定理 `IsArtinianRing.instKrullDimLEOfNatNat`：∀ (R : Type u_1) [inst : CommRing
 R] [IsArtinianRing R], Ring.KrullDimLE 0 R
· 使用定理 `Algebra.FiniteType.isNoetherianRing`：isNoetherianRing (R S : Type*) [Com
mRing R] [CommRing S] [Algebra R S] [h : Algebra.FiniteType R S] [IsNoetherianRi
ng R] : IsNoetherianRing …
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing`：i
sOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing [IsNoetherianRing R] [IsJ
acobsonRing R] (x : PrimeSpectrum R) : List.TFAE [IsOpen {x…
· 使用定理 `Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton`：∀ {R : Type u_1} {S
 : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (p
 : Ideal S)   [inst_3 : p.IsPrime] [IsArt…
· 使用定理 `Algebra.EssFiniteType.of_finiteType`：∀ (R : Type u_1) (S : Type u_2) [in
st : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [Algebra.FiniteT
ype R S], Algebra.EssFini…
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U

--- 原说明 ---
If `R` is an artinian ring, and `S` is a finite type `R`-algebra `R`-quasi-finit
e at `p`,
then `{p}` is clopen in `Spec S`.
-/
lemma QuasiFiniteAt.isClopen_singleton
    (p : PrimeSpectrum S) [IsArtinianRing R] [Algebra.FiniteType R S]
    [Algebra.QuasiFiniteAt R p.asIdeal] : IsClopen {p} := by
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  refine ((PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out 0 1).mp ?_
  obtain ⟨f, hf, e⟩ := exists_basicOpen_eq_singleton (R := R) p.asIdeal
  exact e ▸ (PrimeSpectrum.basicOpen f).isOpen
/-
**Algebra.QuasiFiniteAt.of_isOpen_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Q
uasiFiniteAt`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [IsArtinianRing R]   (p : PrimeSpectrum S) [Algebra.Finit
eType R S], IsOpen {p} → Algebra.QuasiFiniteAt R p.asIdeal
参数：p : PrimeSpectrum S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.FiniteType.isNoetherianRing`：isNoetherianRing (R S : Type*) [Com
mRing R] [CommRing S] [Algebra R S] [h : Algebra.FiniteType R S] [IsNoetherianRi
ng R] : IsNoetherianRing …
· 使用定理 `instIsNoetherianRingOfIsArtinianRing`：∀ (R : Type u_2) [inst : Ring R] [
IsArtinianRing R], IsNoetherianRing R
· 使用引理 `isJacobsonRing_of_finiteType`：isJacobsonRing_of_finiteType {A B : Type*}
 [CommRing A] [CommRing B] [Algebra A B] [IsJacobsonRing A] [Algebra.FiniteType 
A B] : IsJacobsonR…
· 使用定理 `instIsJacobsonRingOfKrullDimLEOfNatNat`：∀ {R : Type u_1} [inst : CommRin
g R] [Ring.KrullDimLE 0 R], IsJacobsonRing R
· 使用定理 `IsArtinianRing.instKrullDimLEOfNatNat`：∀ (R : Type u_1) [inst : CommRing
 R] [IsArtinianRing R], Ring.KrullDimLE 0 R
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `PrimeSpectrum.isClopen_iff`：isClopen_iff {s : Set (PrimeSpectrum R)} : I
sClopen s ↔ exists e : R, IsIdempotentElem e ∧ s = basicOpen e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing`：i
sOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing [IsNoetherianRing R] [IsJ
acobsonRing R] (x : PrimeSpectrum R) : List.TFAE [IsOpen {x…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.injective_codRestrict`：injective_codRestrict {f : ι -> α} {s : Set α
} (h : forall x, f x in s) : Injective (codRestrict f s h) ↔ Injective f
· 使用定理 `PrimeSpectrum.localization_comap_injective`：localization_comap_injective
 [Algebra R S] (M : Submonoid R) [IsLocalization M S] : Function.Injective (coma
p (algebraMap R S))
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
（共 56 条，此处仅展示前 30 条）
-/
lemma QuasiFiniteAt.of_isOpen_singleton
    [IsArtinianRing R] (p : PrimeSpectrum S) [Algebra.FiniteType R S]
    (H : IsOpen {p}) : Algebra.QuasiFiniteAt R p.asIdeal := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := R)
  rw [(PrimeSpectrum.isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing p).out
    0 1 rfl rfl] at H
  obtain ⟨e, he, H⟩ := PrimeSpectrum.isClopen_iff.mp H
  have hep : e ∉ p.asIdeal := H.le rfl
  let f : Localization.Away e →ₐ[S] Localization.AtPrime p.asIdeal :=
    IsLocalization.Away.liftAlgHom e (f := Algebra.ofId _ _)
      (IsLocalization.map_units (M := p.asIdeal.primeCompl) _ ⟨e, hep⟩)
  have h₁ := (PrimeSpectrum.localization_away_comap_range (Localization.Away e) e).trans H.symm
  have : Subsingleton (PrimeSpectrum (Localization.Away e)) :=
    Function.Injective.subsingleton
    (f := Set.codRestrict (PrimeSpectrum.comap (algebraMap S (Localization.Away e))) {p} fun x ↦
      h₁.le ⟨x, rfl⟩)
    ((Set.injective_codRestrict ..).mpr (PrimeSpectrum.localization_comap_injective _ (.powers e)))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl x
    suffices IsUnit (algebraMap _ (Localization.Away e) s.1) by
      refine ⟨algebraMap _ _ x * this.unit⁻¹, (this.map f).mul_right_cancel ?_⟩
      simp only [← map_mul, mul_assoc, IsUnit.val_inv_mul]
      simp
    by_contra H
    obtain ⟨M, hM, H⟩ :=
      Ideal.exists_le_maximal (.span {algebraMap _ (Localization.Away e) s.1}) (by simpa)
    have := Subsingleton.elim ((IsLocalRing.closedPoint _).comap f.toRingHom) ⟨M, inferInstance⟩
    have := congr(($this).1).ge (H (Ideal.mem_span_singleton_self _))
    simp [IsLocalRing.closedPoint, IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal] at this
  have : Algebra.FiniteType R (Localization.AtPrime p.asIdeal) :=
    .of_surjective (f.restrictScalars R) hf
  have := (PrimeSpectrum.comap_injective_of_surjective f.toRingHom hf).subsingleton
  exact QuasiFinite.iff_finite_comap_preimage_singleton.mpr fun _ ↦
    Set.subsingleton_of_subsingleton.finite

attribute [local instance] RingHom.ker_isPrime in
/-
**Algebra._root_.Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver** 是 Mathlib 中
的一个引理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Ideal.exists_not_mem_forall_mem_of_ne_of_liesOver
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    [Algebra.EssFiniteType R S] [Algebra.QuasiFiniteAt R q] :
    ∃ s ∉ q, ∀ q' : Ideal S, q'.IsPrime → q' ≠ q → q'.LiesOver p → s ∈ q' := by
  let e := PrimeSpectrum.preimageHomeomorphFiber _ S ⟨p, inferInstance⟩
  let qF : PrimeSpectrum (p.Fiber S) := e ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩
  have : Algebra.QuasiFiniteAt p.ResidueField qF.asIdeal := .baseChange q _
    congr($(e.symm_apply_apply ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩).1.1).symm
  obtain ⟨r, hr, hrq⟩ := Algebra.QuasiFiniteAt.exists_basicOpen_eq_singleton
    (R := p.ResidueField) qF.asIdeal
  obtain ⟨s, hs, x, hsx⟩ := Ideal.Fiber.exists_smul_eq_one_tmul _ r
  have : x ∉ q := by
    have : r ∉ _ := hrq.ge rfl
    simp only [PrimeSpectrum.preimageHomeomorphFiber, PrimeSpectrum.preimageOrderIsoFiber,
      Homeomorph.homeomorph_mk_coe, qF, e] at this
    rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal,
        ← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s), ← Algebra.smul_def, hsx] at this
    · simpa using this
    · simpa [IsScalarTower.algebraMap_apply R S q.ResidueField, q.over_def p] using hs
  refine ⟨x, this, fun q' _ hq' _ ↦ not_not.mp fun hxq' ↦ hq' ?_⟩
  refine congr($(e.injective (a₁ := ⟨⟨q', ‹_›⟩, PrimeSpectrum.ext (q'.over_def p).symm⟩)
    (a₂ := ⟨⟨q, ‹_›⟩, PrimeSpectrum.ext (q.over_def p).symm⟩) (hrq.le ?_)).1.1)
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, PrimeSpectrum.preimageHomeomorphFiber,
    PrimeSpectrum.preimageOrderIsoFiber, Homeomorph.homeomorph_mk_coe, Set.mem_compl_iff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe, e]
  rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal,
    ← Ideal.IsPrime.mul_mem_left_iff (x := algebraMap _ _ s), ← Algebra.smul_def, hsx]
  · simpa
  · simpa [IsScalarTower.algebraMap_apply R S q'.ResidueField, ← Ideal.mem_comap, ← q'.over_def p]
/-
**Algebra._root_.Ideal.Fiber.lift_residueField_surjective** 是 Mathlib 中的一个引理，位于命
名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Ideal.Fiber.lift_residueField_surjective [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q] :
    Function.Surjective (Algebra.TensorProduct.lift (Algebra.ofId _ _)
      (IsScalarTower.toAlgHom _ _ _) fun _ _ ↦ .all _ _ :
      p.Fiber S →ₐ[p.ResidueField] q.ResidueField) := by
  let q' : Ideal (p.Fiber S) := (PrimeSpectrum.primesOverOrderIsoFiber R S p ⟨q, ‹_›, ‹_›⟩).asIdeal
  have hq' : q = q'.comap Algebra.TensorProduct.includeRight.toRingHom :=
    congr($((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply ⟨q, ‹_›, ‹_›⟩).1).symm
  have : Algebra.QuasiFiniteAt p.ResidueField q' := .baseChange q _ hq'
  have : q'.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
    (QuasiFiniteAt.isClopen_singleton (R := p.ResidueField) _).isClosed
  refine .of_comp_left ?_
    (p.surjectiveOnStalks_residueField.baseChange'.residueFieldMap_bijective q q' hq').1
  rw [← AlgHom.coe_toRingHom, ← RingHom.coe_comp]
  convert! q'.algebraMap_residueField_surjective
  ext <;> simp [IsScalarTower.algebraMap_apply R S q.ResidueField]

end QuasiFiniteAt

end Algebra

