/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.RingTheory.Unramified.Basic

/-!

# Étale morphisms

An `R`-algebra `A` is formally etale if `Ω[A⁄R]` and `H¹(L_{A/R})` both vanish.
This is equivalent to the standard definition that "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
exactly one lift `A →ₐ[R] B`".
An `R`-algebra `A` is étale if it is formally étale and of finite presentation.

We show that the property extends onto nilpotent ideals, and that these properties are stable
under `R`-algebra homomorphisms and compositions.

We show that étale is stable under algebra isomorphisms, composition and
localization at an element.

-/

@[expose] public section

open scoped TensorProduct

universe u v

namespace Algebra

variable {R : Type u} {A : Type v} {B : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]

section

variable (R A) in
/-- An `R`-algebra `A` is formally etale if both `Ω[A⁄R]` and `H¹(L_{A/R})` are zero.
For the infinitesimal lifting definition, see `FormallyEtale.iff_comp_bijective`. -/
@[mk_iff, stacks 00UQ]
/--
Definition of `FormallyEtale` / `FormallyEtale` 的定义

English:
class FormallyEtale
  parameters: : Prop where
  axioms and operations (2):
    - subsingleton_kaehlerDifferential : Subsingleton Ω[A⁄R]
    - subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)

中文:
类 FormallyEtale
  参数: : 命题 where
  公理与运算 (2 个):
    - subsingleton_kaehlerDifferential : Subsingleton Ω[A⁄R]
    - subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)
-/
class FormallyEtale : Prop where
  subsingleton_kaehlerDifferential : Subsingleton Ω[A⁄R]
  subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)

attribute [instance]
  FormallyEtale.subsingleton_kaehlerDifferential FormallyEtale.subsingleton_h1Cotangent

end

namespace FormallyEtale

section

instance (priority := 100) [FormallyEtale R A] :
    FormallyUnramified R A := ⟨inferInstance⟩

instance (priority := 100) [FormallyEtale R A] : FormallySmooth R A :=
  ⟨inferInstance, inferInstance⟩

/--
theorem `iff_formallyUnramified_and_formallySmooth` / 定理 `iff_formallyUnramified_and_formallySmooth`

English:
theorem iff_formallyUnramified_and_formallySmooth
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ⟨inferInstance, inferInstance⟩⟩

中文:
定理 iff_formallyUnramified_and_formallySmooth
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ⟨inferInstance, inferInstance⟩⟩
-/
theorem iff_formallyUnramified_and_formallySmooth :
    FormallyEtale R A ↔ FormallyUnramified R A ∧ FormallySmooth R A :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => ⟨inferInstance, inferInstance⟩⟩

/--
theorem `of_formallyUnramified_and_formallySmooth` / 定理 `of_formallyUnramified_and_formallySmooth`

English:
theorem of_formallyUnramified_and_formallySmooth
  statement: [FormallyUnramified R A]
  proof: FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨‹_›, ‹_›⟩

中文:
定理 of_formallyUnramified_and_formallySmooth
  结论: [FormallyUnramified R A]
  证明: FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨‹_›, ‹_›⟩

Depends on / 依赖: FormallyEtale, FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr, iff_formallyUnramified_and_formallySmooth
-/
theorem of_formallyUnramified_and_formallySmooth [FormallyUnramified R A]
    [FormallySmooth R A] : FormallyEtale R A :=
  FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨‹_›, ‹_›⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FormallyEtale R R
  body: of_formallyUnramified_and_formallySmooth

中文:
实例 :
  签名: FormallyEtale R R
  定义体: of_formallyUnramified_and_formallySmooth

Depends on / 依赖: of_formallyUnramified_and_formallySmooth, transpose, without
-/
instance : FormallyEtale R R := of_formallyUnramified_and_formallySmooth

variable (R A) in
/--
lemma `comp_bijective` / 引理 `comp_bijective`

English:
lemma comp_bijective
  given: [FormallyEtale R A] (I : Ideal B) (hI : I ^ 2 = ⊥)
  proof: ⟨FormallyUnramified.comp_injective I hI, FormallySmooth.comp_surjective R A I hI⟩

中文:
引理 comp_bijective
  条件: [FormallyEtale R A] (I : Ideal B) (hI : I ^ 2 = ⊥)
  证明: ⟨FormallyUnramified.comp_injective I hI, FormallySmooth.comp_surjective R A I hI⟩

Depends on / 依赖: FormallySmooth, FormallySmooth.comp_surjective, FormallyUnramified, FormallyUnramified.comp_injective, comp_injective, comp_surjective
-/
lemma comp_bijective [FormallyEtale R A] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ I) :=
  ⟨FormallyUnramified.comp_injective I hI, FormallySmooth.comp_surjective R A I hI⟩

/--
theorem `iff_comp_bijective` / 定理 `iff_comp_bijective`

English:
theorem iff_comp_bijective
  proof: ⟨fun _ _ => comp_bijective R A, fun H =>
    have : FormallyUnramified R A := FormallyUnramified.iff_comp_injective_of_small.{max u v}.mpr
      (by aesop (add safe Function.Bijective.injective))
    have : FormallySmooth R A := FormallySmooth.of_comp_surjective
      (by aesop (add safe Function.Bi

中文:
定理 iff_comp_bijective
  证明: ⟨fun _ _ => comp_bijective R A, fun H =>
    have : FormallyUnramified R A := FormallyUnramified.iff_comp_injective_of_small.{max u v}.mpr
      (by aesop (add safe Function.Bijective.injective))
    have : FormallySmooth R A := FormallySmooth.of_comp_surjective
      (by aesop (add safe Function.Bi

Depends on / 依赖: Bijective, FormallySmooth, FormallySmooth.of_comp_surjective, FormallyUnramified, FormallyUnramified.iff_comp_injective_of_small, Function, Function.Bijective.injective, Function.Bijective.surjective, comp_bijective, iff_comp_injective_of_small, injective, of_comp_surjective, of_formallyUnramified_and_formallySmooth, surjective
-/
theorem iff_comp_bijective :
   FormallyEtale R A ↔ forall ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B), I ^ 2 = ⊥ ->
      Function.Bijective ((Ideal.Quotient.mkₐ R I).comp : (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ I) :=
  ⟨fun _ _ => comp_bijective R A, fun H =>
    have : FormallyUnramified R A := FormallyUnramified.iff_comp_injective_of_small.{max u v}.mpr
      (by aesop (add safe Function.Bijective.injective))
    have : FormallySmooth R A := FormallySmooth.of_comp_surjective
      (by aesop (add safe Function.Bijective.surjective))
   .of_formallyUnramified_and_formallySmooth⟩

end

section OfEquiv

/--
theorem `of_equiv` / 定理 `of_equiv`

English:
theorem of_equiv
  given: [FormallyEtale R A] (e : A ≃ₐ[R] B)
  statement: FormallyEtale R B
  proof: FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩

中文:
定理 of_equiv
  条件: [FormallyEtale R A] (e : A ≃ₐ[R] B)
  结论: FormallyEtale R B
  证明: FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩

Depends on / 依赖: FormallyEtale, FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr, FormallySmooth, FormallySmooth.of_equiv, FormallyUnramified, FormallyUnramified.of_equiv, iff_formallyUnramified_and_formallySmooth, of_equiv
-/
theorem of_equiv [FormallyEtale R A] (e : A ≃ₐ[R] B) : FormallyEtale R B :=
  FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.of_equiv e, FormallySmooth.of_equiv e⟩

/--
theorem `iff_of_equiv` / 定理 `iff_of_equiv`

English:
theorem iff_of_equiv
  given: (e : A ≃ₐ[R] B)
  statement: FormallyEtale R A ↔ FormallyEtale R B
  proof: ⟨fun _ => of_equiv e, fun _ => of_equiv e.symm⟩

中文:
定理 iff_of_equiv
  条件: (e : A ≃ₐ[R] B)
  结论: FormallyEtale R A ↔ FormallyEtale R B
  证明: ⟨fun _ => of_equiv e, fun _ => of_equiv e.symm⟩

Depends on / 依赖: e.symm, of_equiv
-/
theorem iff_of_equiv (e : A ≃ₐ[R] B) : FormallyEtale R A ↔ FormallyEtale R B :=
  ⟨fun _ => of_equiv e, fun _ => of_equiv e.symm⟩

end OfEquiv

section Comp

variable [Algebra A B] [IsScalarTower R A B]

variable (R A B) in
/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: [FormallyEtale R A] [FormallyEtale A B]
  proof: FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.comp R A B, FormallySmooth.comp R A B⟩

中文:
定理 comp
  条件: [FormallyEtale R A] [FormallyEtale A B]
  证明: FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.comp R A B, FormallySmooth.comp R A B⟩

Depends on / 依赖: FormallyEtale, FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr, FormallySmooth, FormallySmooth.comp, FormallyUnramified, FormallyUnramified.comp, iff_formallyUnramified_and_formallySmooth
-/
theorem comp [FormallyEtale R A] [FormallyEtale A B] :
    FormallyEtale R B :=
  FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.comp R A B, FormallySmooth.comp R A B⟩

/--
lemma `of_restrictScalars` / 引理 `of_restrictScalars`

English:
lemma of_restrictScalars
  given: [FormallyUnramified R A] [FormallyEtale R B]
  proof: have := FormallyUnramified.of_restrictScalars R A B
  have := FormallySmooth.of_restrictScalars R A B
  .of_formallyUnramified_and_formallySmooth

中文:
引理 of_restrictScalars
  条件: [FormallyUnramified R A] [FormallyEtale R B]
  证明: have := FormallyUnramified.of_restrictScalars R A B
  have := FormallySmooth.of_restrictScalars R A B
  .of_formallyUnramified_and_formallySmooth

Depends on / 依赖: FormallySmooth, FormallySmooth.of_restrictScalars, FormallyUnramified, FormallyUnramified.of_restrictScalars, of_formallyUnramified_and_formallySmooth, of_restrictScalars
-/
lemma of_restrictScalars [FormallyUnramified R A] [FormallyEtale R B] :
    FormallyEtale A B :=
  have := FormallyUnramified.of_restrictScalars R A B
  have := FormallySmooth.of_restrictScalars R A B
  .of_formallyUnramified_and_formallySmooth

/--
lemma `iff_restrictScalars` / 引理 `iff_restrictScalars`

English:
lemma iff_restrictScalars
  given: [FormallyEtale R A]
  proof: ⟨fun _ => .of_restrictScalars (R := R), fun _ => .comp _ A _⟩

中文:
引理 iff_restrictScalars
  条件: [FormallyEtale R A]
  证明: ⟨fun _ => .of_restrictScalars (R := R), fun _ => .comp _ A _⟩

Depends on / 依赖: of_restrictScalars
-/
lemma iff_restrictScalars [FormallyEtale R A] :
    Algebra.FormallyEtale R B ↔ Algebra.FormallyEtale A B :=
  ⟨fun _ => .of_restrictScalars (R := R), fun _ => .comp _ A _⟩

/--
lemma `_root_.Algebra.FormallySmooth.iff_restrictScalars` / 引理 `_root_.Algebra.FormallySmooth.iff_restrictScalars`

English:
lemma _root_.Algebra.FormallySmooth.iff_restrictScalars
  given: [FormallyEtale R A]
  proof: ⟨fun _ => .of_restrictScalars R _ _, fun _ => .comp _ A _⟩

中文:
引理 _root_.Algebra.FormallySmooth.iff_restrictScalars
  条件: [FormallyEtale R A]
  证明: ⟨fun _ => .of_restrictScalars R _ _, fun _ => .comp _ A _⟩

Depends on / 依赖: of_restrictScalars
-/
lemma _root_.Algebra.FormallySmooth.iff_restrictScalars [FormallyEtale R A] :
    Algebra.FormallySmooth R B ↔ Algebra.FormallySmooth A B :=
  ⟨fun _ => .of_restrictScalars R _ _, fun _ => .comp _ A _⟩

end Comp

/--
lemma `iff_of_surjective` / 引理 `iff_of_surjective`

English:
lemma iff_of_surjective
  proof: by
  rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth]; rw [← FormallySmooth.iff_of_surjective h]; rw [and_iff_right (FormallyUnramified.of_surjective (Algebra.ofId R S) h)]

中文:
引理 iff_of_surjective
  证明: by
  rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth]; rw [← FormallySmooth.iff_of_surjective h]; rw [and_iff_right (FormallyUnramified.of_surjective (Algebra.ofId R S) h)]

Depends on / 依赖: Algebra, Algebra.ofId, FormallyEtale, FormallyEtale.iff_formallyUnramified_and_formallySmooth, FormallySmooth, FormallySmooth.iff_of_surjective, FormallyUnramified, FormallyUnramified.of_surjective, and_iff_right, iff_formallyUnramified_and_formallySmooth, iff_of_surjective, of_surjective
-/
lemma iff_of_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (h : Function.Surjective (algebraMap R S)) :
    Algebra.FormallyEtale R S ↔ IsIdempotentElem (RingHom.ker (algebraMap R S)) := by
  rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth]; rw [← FormallySmooth.iff_of_surjective h]; rw [and_iff_right (FormallyUnramified.of_surjective (Algebra.ofId R S) h)]

section BaseChange


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FormallyEtale
  signature: R A] : FormallyEtale B (B otimes[R] A)
  body: .of_formallyUnramified_and_formallySmooth

中文:
实例 [FormallyEtale
  签名: R A] : FormallyEtale B (B otimes[R] A)
  定义体: .of_formallyUnramified_and_formallySmooth

Depends on / 依赖: of_formallyUnramified_and_formallySmooth
-/
instance [FormallyEtale R A] : FormallyEtale B (B otimes[R] A) :=
  .of_formallyUnramified_and_formallySmooth

end BaseChange

section Localization

/-!

We now consider a commutative square of commutative rings

```
R -----> S
| |
| |
v v
Rₘ ----> Sₘ
```

where `Rₘ` and `Sₘ` are the localisations of `R` and `S` at a multiplicatively closed
subset `M` of `R`.
-/

/-! Let R, S, Rₘ, Sₘ be commutative rings -/
variable {R S Rₘ Sₘ : Type*} [CommRing R] [CommRing S] [CommRing Rₘ] [CommRing Sₘ]
/-! Let M be a multiplicatively closed subset of `R` -/
variable (M : Submonoid R)
/-! Assume that the rings are in a commutative diagram as above. -/
variable [Algebra R S] [Algebra R Sₘ] [Algebra S Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R S Sₘ]
/-! and that Rₘ and Sₘ are localizations of R and S at M. -/
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R S)) Sₘ]
include M

/--
theorem `of_isLocalization` / 定理 `of_isLocalization`

English:
theorem of_isLocalization
  statement: FormallyEtale R Rₘ
  proof: FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.of_isLocalization M, FormallySmooth.of_isLocalization M⟩

中文:
定理 of_isLocalization
  结论: FormallyEtale R Rₘ
  证明: FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.of_isLocalization M, FormallySmooth.of_isLocalization M⟩

Depends on / 依赖: FormallyEtale, FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr, FormallySmooth, FormallySmooth.of_isLocalization, FormallyUnramified, FormallyUnramified.of_isLocalization, iff_formallyUnramified_and_formallySmooth, of_isLocalization
-/
theorem of_isLocalization : FormallyEtale R Rₘ :=
  FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.of_isLocalization M, FormallySmooth.of_isLocalization M⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FormallyEtale
  signature: R S] (M
  body: .of_formallyUnramified_and_formallySmooth

中文:
实例 [FormallyEtale
  签名: R S] (M
  定义体: .of_formallyUnramified_and_formallySmooth

Depends on / 依赖: of_formallyUnramified_and_formallySmooth
-/
instance [FormallyEtale R S] (M : Submonoid S) : FormallyEtale R (Localization M) :=
  .of_formallyUnramified_and_formallySmooth

/--
theorem `localization_base` / 定理 `localization_base`

English:
theorem localization_base
  given: [FormallyEtale R Sₘ]
  statement: FormallyEtale Rₘ Sₘ
  proof: FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.localization_base M, FormallySmooth.localization_base M⟩

中文:
定理 localization_base
  条件: [FormallyEtale R Sₘ]
  结论: FormallyEtale Rₘ Sₘ
  证明: FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.localization_base M, FormallySmooth.localization_base M⟩

Depends on / 依赖: FormallyEtale, FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr, FormallySmooth, FormallySmooth.localization_base, FormallyUnramified, FormallyUnramified.localization_base, iff_formallyUnramified_and_formallySmooth, localization_base
-/
theorem localization_base [FormallyEtale R Sₘ] : FormallyEtale Rₘ Sₘ :=
  FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr
    ⟨FormallyUnramified.localization_base M, FormallySmooth.localization_base M⟩

/--
theorem `localization_map` / 定理 `localization_map`

English:
theorem localization_map
  given: [FormallyEtale R S]
  statement: FormallyEtale Rₘ Sₘ
  proof: by
  have : FormallyEtale S Sₘ := FormallyEtale.of_isLocalization (M.map (algebraMap R S))
  have : FormallyEtale R Sₘ := FormallyEtale.comp R S Sₘ
  exact FormallyEtale.localization_base M

中文:
定理 localization_map
  条件: [FormallyEtale R S]
  结论: FormallyEtale Rₘ Sₘ
  证明: by
  have : FormallyEtale S Sₘ := FormallyEtale.of_isLocalization (M.map (algebraMap R S))
  have : FormallyEtale R Sₘ := FormallyEtale.comp R S Sₘ
  exact FormallyEtale.localization_base M

Depends on / 依赖: FormallyEtale, FormallyEtale.comp, FormallyEtale.localization_base, FormallyEtale.of_isLocalization, M.map, algebraMap, localization_base, of_isLocalization
-/
theorem localization_map [FormallyEtale R S] : FormallyEtale Rₘ Sₘ := by
  have : FormallyEtale S Sₘ := FormallyEtale.of_isLocalization (M.map (algebraMap R S))
  have : FormallyEtale R Sₘ := FormallyEtale.comp R S Sₘ
  exact FormallyEtale.localization_base M

end Localization

end FormallyEtale

section

variable (R A) in
/-- An `R`-algebra `A` is étale if it is formally étale and of finite presentation. -/
@[mk_iff, stacks 00U1 "Note that this is a different definition from this Stacks entry, but
<https://stacks.math.columbia.edu/tag/00UR> shows that it is equivalent to the definition here."]
/--
Definition of `Etale` / `Etale` 的定义

English:
class Etale
  parameters: : Prop where
  axioms and operations (2):
    - formallyEtale : FormallyEtale R A  [default: by infer_instance]
    - finitePresentation : FinitePresentation R A  [default: by infer_instance]

中文:
类 Etale
  参数: : 命题 where
  公理与运算 (2 个):
    - formallyEtale : FormallyEtale R A  [默认: by infer_instance]
    - finitePresentation : FinitePresentation R A  [默认: by infer_instance]

Depends on / 依赖: FinitePresentation, finitePresentation, infer_instance
-/
class Etale : Prop where
  formallyEtale : FormallyEtale R A := by infer_instance
  finitePresentation : FinitePresentation R A := by infer_instance

/--
lemma `Etale.iff_formallyUnramified_and_smooth` / 引理 `Etale.iff_formallyUnramified_and_smooth`

English:
lemma Etale.iff_formallyUnramified_and_smooth
  proof: by
  rw [etale_iff]; rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth]; rw [smooth_iff]
  tauto

中文:
引理 Etale.iff_formallyUnramified_and_smooth
  证明: by
  rw [etale_iff]; rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth]; rw [smooth_iff]
  tauto

Depends on / 依赖: FormallyEtale, FormallyEtale.iff_formallyUnramified_and_formallySmooth, Function, Function.Injective.ring, Injective, etale_iff, fast_instance, iff_formallyUnramified_and_formallySmooth, smooth_iff
-/
lemma Etale.iff_formallyUnramified_and_smooth :
    Etale R A ↔ FormallyUnramified R A ∧ Smooth R A := by
  rw [etale_iff]; rw [FormallyEtale.iff_formallyUnramified_and_formallySmooth]; rw [smooth_iff]
  tauto

end

namespace Etale

attribute [instance] formallyEtale finitePresentation

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Etale R R

中文:
实例 :
  签名: Etale R R
-/
instance : Etale R R where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Etale
  signature: R A] : Smooth R A where

中文:
实例 [Etale
  签名: R A] : Smooth R A where
-/
instance [Etale R A] : Smooth R A where

instance (priority := low) [Etale R A] : Unramified R A where

/--
theorem `of_equiv` / 定理 `of_equiv`

English:
theorem of_equiv
  given: [Etale R A] (e : A ≃ₐ[R] B)
  statement: Etale R B where
  proof: FormallyEtale.of_equiv e
  finitePresentation := FinitePresentation.equiv e

中文:
定理 of_equiv
  条件: [Etale R A] (e : A ≃ₐ[R] B)
  结论: Etale R B where
  证明: FormallyEtale.of_equiv e
  finitePresentation := FinitePresentation.equiv e

Depends on / 依赖: FormallyEtale, FormallyEtale.of_equiv, of_equiv
-/
theorem of_equiv [Etale R A] (e : A ≃ₐ[R] B) : Etale R B where
  formallyEtale := FormallyEtale.of_equiv e
  finitePresentation := FinitePresentation.equiv e

section Comp

variable (R A B)

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale A B]
  statement: Etale R B where
  proof: FormallyEtale.comp R A B
  finitePresentation := FinitePresentation.trans R A B

中文:
定理 comp
  条件: [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale A B]
  结论: Etale R B where
  证明: FormallyEtale.comp R A B
  finitePresentation := FinitePresentation.trans R A B

Depends on / 依赖: FormallyEtale, FormallyEtale.comp
-/
theorem comp [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale A B] : Etale R B where
  formallyEtale := FormallyEtale.comp R A B
  finitePresentation := FinitePresentation.trans R A B

/--
Instance `baseChange` / 实例 `baseChange`

English:
instance baseChange
  signature: [Etale R A]

中文:
实例 baseChange
  签名: [Etale R A]
-/
instance baseChange [Etale R A] : Etale B (B otimes[R] A) where

/--
lemma `of_restrictScalars` / 引理 `of_restrictScalars`

English:
lemma of_restrictScalars
  given: [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale R B]
  proof: .of_restrict_scalars_finitePresentation R A B
  formallyEtale := .of_restrictScalars (R := R)

中文:
引理 of_restrictScalars
  条件: [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale R B]
  证明: .of_restrict_scalars_finitePresentation R A B
  formallyEtale := .of_restrictScalars (R := R)

Depends on / 依赖: of_restrict_scalars_finitePresentation
-/
lemma of_restrictScalars [Algebra A B] [IsScalarTower R A B] [Etale R A] [Etale R B] :
    Etale A B where
  finitePresentation := .of_restrict_scalars_finitePresentation R A B
  formallyEtale := .of_restrictScalars (R := R)

end Comp

/--
theorem `of_isLocalizationAway` / 定理 `of_isLocalizationAway`

English:
theorem of_isLocalizationAway
  given: (r : R) [IsLocalization.Away r A]
  statement: Etale R A where
  proof: Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

中文:
定理 of_isLocalizationAway
  条件: (r : R) [IsLocalization.Away r A]
  结论: Etale R A where
  证明: Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

Depends on / 依赖: Algebra, Algebra.FormallyEtale.of_isLocalization, FormallyEtale, Submonoid, Submonoid.powers, of_isLocalization, powers
-/
theorem of_isLocalizationAway (r : R) [IsLocalization.Away r A] : Etale R A where
  formallyEtale := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

instance (s : A) [Algebra.Etale R A] : Algebra.Etale R (Localization.Away s) where

instance (R S : Type u) [CommRing R] [CommRing S] :
    letI : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
    Algebra.Etale (R × S) S := by
  algebraize [RingHom.snd R S]
  exact Algebra.Etale.of_isLocalizationAway (0, 1)

instance (S : Type*) [CommRing S] :
    letI : Algebra (R × S) R := (RingHom.fst R S).toAlgebra
    Algebra.Etale (R × S) R := by
  algebraize [RingHom.fst R S]
  exact Algebra.Etale.of_isLocalizationAway (1, 0)

instance (S : Type*) [CommRing S] :
    letI : Algebra (R × S) S := (RingHom.snd R S).toAlgebra
    Algebra.Etale (R × S) S := by
  algebraize [RingHom.snd R S]
  exact Algebra.Etale.of_isLocalizationAway (0, 1)

end Etale

end Algebra

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

/--
A ring homomorphism `R →+* A` is formally étale if it is formally unramified and formally smooth.
See `Algebra.FormallyEtale`.
-/
@[algebraize Algebra.FormallyEtale]
/--
Definition of `FormallyEtale` / `FormallyEtale` 的定义

English:
definition FormallyEtale
  signature: (f : R ->+* S)
  body: letI := f.toAlgebra
  Algebra.FormallyEtale R S

中文:
定义 FormallyEtale
  签名: (f : R ->+* S)
  定义体: letI := f.toAlgebra
  Algebra.FormallyEtale R S

Depends on / 依赖: Algebra, Algebra.FormallyEtale, FormallyEtale, f.toAlgebra, toAlgebra
-/
def FormallyEtale (f : R ->+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallyEtale R S

/--
lemma `formallyEtale_algebraMap` / 引理 `formallyEtale_algebraMap`

English:
lemma formallyEtale_algebraMap
  given: [Algebra R S]
  proof: by
  rw [FormallyEtale]; rw [toAlgebra_algebraMap]

中文:
引理 formallyEtale_algebraMap
  条件: [Algebra R S]
  证明: by
  rw [FormallyEtale]; rw [toAlgebra_algebraMap]

Depends on / 依赖: FormallyEtale, toAlgebra_algebraMap
-/
lemma formallyEtale_algebraMap [Algebra R S] :
    (algebraMap R S).FormallyEtale ↔ Algebra.FormallyEtale R S := by
  rw [FormallyEtale]; rw [toAlgebra_algebraMap]

/--
lemma `FormallyEtale.comp` / 引理 `FormallyEtale.comp`

English:
lemma FormallyEtale.comp
  statement: {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T} (hf : f.FormallyEtale)
  proof: by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyEtale.comp R S T

中文:
引理 FormallyEtale.comp
  结论: {T : 类型} [CommRing T] {f : R ->+* S} {g : S ->+* T} (hf : f.FormallyEtale)
  证明: by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyEtale.comp R S T

Depends on / 依赖: Algebra, Algebra.FormallyEtale.comp, FormallyEtale, algebraize, g.comp
-/
lemma FormallyEtale.comp {T : Type*} [CommRing T] {f : R ->+* S} {g : S ->+* T} (hf : f.FormallyEtale)
    (hg : g.FormallyEtale) :
    (g.comp f).FormallyEtale := by
  algebraize [f, g, g.comp f]
  exact Algebra.FormallyEtale.comp R S T

end RingHom
