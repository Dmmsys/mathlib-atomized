/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Unramified.Basic

/-!

# Smooth morphisms

An `R`-algebra `A` is formally smooth if `Ω[A⁄R]` is `A`-projective and `H¹(L_{A/R}) = 0`.
This is equivalent to the standard definition that "for every `R`-algebra `B`,
every square-zero ideal `I : Ideal B` and `f : A →ₐ[R] B ⧸ I`, there exists
at least one lift `A →ₐ[R] B`".
An `R`-algebra `A` is smooth if it is formally smooth and of finite presentation.

We show that the property of being formally smooth extends onto nilpotent ideals,
and that it is stable under `R`-algebra homomorphisms and compositions.

We show that smooth is stable under algebra isomorphisms, composition and
localization at an element.

## Main results
- `Algebra.FormallySmooth`: The class of formally smooth algebras.
- `Algebra.formallySmooth_iff` :
  Formally smooth iff `Ω[A⁄R]` is `A`-projective and `H¹(L_{A/R}) = 0`.
- `Algebra.FormallySmooth.lift`: If `A` is formally smooth and `I` is nilpotent,
  any map `A →ₐ[R] B ⧸ I` lifts to `A →ₐ[R] B`.
- `Algebra.FormallySmooth.iff_comp_surjective`: `A` is formally smooth iff
  any map `A →ₐ[R] B ⧸ I` lifts to `A →ₐ[R] B` for any square zero `I`.

Suppose `P` is a formally smooth `R` algebra that surjects onto `A` with kernel `I`, then
- `Algebra.FormallySmooth.iff_split_surjection`: `A` is formally smooth iff
  the algebra map `P ⧸ I² →ₐ[R] A` has an `R`-algebra section.
- `Algebra.Extension.equivH1CotangentOfFormallySmooth`:
  `H¹(L_{A/R})` is isomorphic to `ker(I/I² → A ⊗[P] Ω[P⁄R])`.
- `Algebra.FormallySmooth.iff_split_injection`: `A` is formally smooth iff
  the `P`-linear map `I/I² → A ⊗[P] Ω[P⁄R]` is split injective.

-/

@[expose] public section

open scoped TensorProduct
open Algebra.Extension KaehlerDifferential MvPolynomial

universe u v w

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable {B P C : Type*} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  [CommRing P] [Algebra R P]
namespace Algebra

section

variable (R A) in
/--
An `R`-algebra `A` is formally smooth if `Ω[A⁄R]` is `A`-projective and `H¹(L_{A/R}) = 0`.
For the infinitesimal lifting definition,
see `FormallySmooth.lift` and `FormallySmooth.iff_comp_surjective`.
-/
@[stacks 00TI "Also see 031J (6) for the equivalence with the definition given here.", mk_iff]
/--
Definition of `FormallySmooth` / `FormallySmooth` 的定义

English:
class FormallySmooth
  parameters: : Prop where
  axioms and operations (2):
    - projective_kaehlerDifferential : Module.Projective A Ω[A⁄R]
    - subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)

中文:
类 FormallySmooth
  参数: : 命题 where
  公理与运算 (2 个):
    - projective_kaehlerDifferential : Module.Projective A Ω[A⁄R]
    - subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)
-/
class FormallySmooth : Prop where
  projective_kaehlerDifferential : Module.Projective A Ω[A⁄R]
  subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)

attribute [instance] FormallySmooth.projective_kaehlerDifferential
  FormallySmooth.subsingleton_h1Cotangent

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (R A) in
/--
lemma `FormallySmooth.comp_surjective` / 引理 `FormallySmooth.comp_surjective`

English:
lemma FormallySmooth.comp_surjective
  given: [FormallySmooth R A] (I : Ideal B) (hI : I ^ 2 = ⊥)
  proof: by
  intro f
  let P : Algebra.Generators R A A := Generators.self R A
  have hP : Function.Injective P.toExtension.cotangentComplex := by
    rw [← LinearMap.ker_eq_bot]; rw [← Submodule.subsingleton_iff_eq_bot]
    exact FormallySmooth.subsingleton_h1Cotangent
  obtain ⟨l, hl⟩ := ((P.toExtension.e

中文:
引理 FormallySmooth.comp_surjective
  条件: [FormallySmooth R A] (I : Ideal B) (hI : I ^ 2 = ⊥)
  证明: by
  intro f
  let P : Algebra.Generators R A A := Generators.self R A
  have hP : Function.Injective P.toExtension.cotangentComplex := by
    rw [← LinearMap.ker_eq_bot]; rw [← Submodule.subsingleton_iff_eq_bot]
    exact FormallySmooth.subsingleton_h1Cotangent
  obtain ⟨l, hl⟩ := ((P.toExtension.e

Depends on / 依赖: Algebra, Algebra.Generators, FormallySmooth, FormallySmooth.subsingleton_h1Cotangent, Function, Function.Injective, Generators, Generators.self, Injective, LinearMap, LinearMap.ker_eq_bot, Module, Module.projective_lifting_property, P.toExtension.cotangentComplex, P.toExtension.exact_cotangentComplex_toKaehler.split_tfae, P.toExtension.subsingleton_h1Cotangent.mp, P.toExtension.toKaehler_surje, Submodule, Submodule.subsingleton_iff_eq_bot, cotangentComplex
-/
lemma FormallySmooth.comp_surjective [FormallySmooth R A] (I : Ideal B) (hI : I ^ 2 = ⊥) :
    Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ I) := by
  intro f
  let P : Algebra.Generators R A A := Generators.self R A
  have hP : Function.Injective P.toExtension.cotangentComplex := by
    rw [← LinearMap.ker_eq_bot]; rw [← Submodule.subsingleton_iff_eq_bot]
    exact FormallySmooth.subsingleton_h1Cotangent
  obtain ⟨l, hl⟩ := ((P.toExtension.exact_cotangentComplex_toKaehler.split_tfae'.out 0 1 rfl rfl).mp
    ⟨P.toExtension.subsingleton_h1Cotangent.mp FormallySmooth.subsingleton_h1Cotangent,
      Module.projective_lifting_property _ _ P.toExtension.toKaehler_surjective⟩).2
  obtain ⟨g, hg⟩ := retractionKerCotangentToTensorEquivSection (R := R) P.algebraMap_surjective
    ⟨⟨⟨Cotangent.val, by simp⟩, by simpa using! Cotangent.val_smul' (P := P.toExtension)⟩ ∘ₗ
      l.restrictScalars P.toExtension.Ring, LinearMap.ext fun x => congr($hl x)⟩
  let σ := Function.surjInv (f := algebraMap B (B ⧸ I)) Ideal.Quotient.mk_surjective
  have H (x : P.Ring) : ↑(aeval (σ ∘ f) x) = f (algebraMap _ A x) := by
    rw [← Ideal.Quotient.algebraMap_eq]; rw [← aeval_algebraMap_apply]; rw [P.algebraMap_eq]; rw [AlgHom.coe_toRingHom]; rw [comp_aeval_apply]; rw [← Function.comp_assoc]; rw [Function.comp_surjInv]
    simp [P]
  let l : P.Ring ⧸ (RingHom.ker (algebraMap P.Ring A)) ^ 2 ->ₐ[R] B :=
Ideal.Quotient.liftₐ _ (aeval (σ ∘ f))
      have : RingHom.ker (algebraMap P.Ring A) <= I.comap (aeval (σ ∘ f)).toRingHom := fun x hx => by
        simp_all [← Ideal.Quotient.eq_zero_iff_mem (I := I), -map_aeval]
      show RingHom.ker _ ^ 2 <= RingHom.ker _ from
        (Ideal.pow_right_mono this 2).trans ((Ideal.le_comap_pow _ _).trans_eq (hI ▸ rfl))
  have : f.comp (IsScalarTower.toAlgHom R P.Ring A).kerSquareLift =
      (Ideal.Quotient.mkₐ R _).comp l := by
    refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i => ?_)
    change f (algebraMap P.Ring A (.X i)) = algebraMap _ _ (MvPolynomial.aeval (σ ∘ f) (.X i))
    simpa using! (Function.surjInv_eq _ _).symm
  exact ⟨l.comp g, by rw [← AlgHom.comp_assoc, ← this, AlgHom.comp_assoc, hg, AlgHom.comp_id]⟩

set_option backward.defeqAttrib.useBackward true in
/--
Instance `instFormallySmoothMvPolynomial` / 实例 `instFormallySmoothMvPolynomial`

English:
instance instFormallySmoothMvPolynomial
  signature: (σ : Type*)
  body: by
  let P := Generators.mvPolynomial R σ
  have : Subsingleton ↥P.toExtension.ker :=
    Submodule.subsingleton_iff_eq_bot.mpr Generators.ker_mvPolynomial
  have : Subsingleton P.toExtension.Cotangent := Cotangent.mk_surjective.subsingleton
  have := P.toExtension.h1Cotangentι_injective.subsingleto

中文:
实例 instFormallySmoothMvPolynomial
  签名: (σ : 类型)
  定义体: by
  let P := Generators.mvPolynomial R σ
  have : Subsingleton ↥P.toExtension.ker :=
    Submodule.subsingleton_iff_eq_bot.mpr Generators.ker_mvPolynomial
  have : Subsingleton P.toExtension.Cotangent := Cotangent.mk_surjective.subsingleton
  have := P.toExtension.h1Cotangentι_injective.subsingleto

Depends on / 依赖: Cotangent, Cotangent.mk_surjective.subsingleton, Generators, Generators.ker_mvPolynomial, Generators.mvPolynomial, P.equivH1Cotangent.symm.subsingleton, P.toExtension.Cotangent, P.toExtension.h1Cotangent, P.toExtension.ker, Submodule, Submodule.subsingleton_iff_eq_bot.mpr, Subsingleton, _injective.subsingleton, equivH1Cotangent, ker_mvPolynomial, mk_surjective, mvPolynomial, subsingleton, subsingleton_iff_eq_bot, toExtension
-/
instance instFormallySmoothMvPolynomial (σ : Type*) : FormallySmooth R (MvPolynomial σ R) := by
  let P := Generators.mvPolynomial R σ
  have : Subsingleton ↥P.toExtension.ker :=
    Submodule.subsingleton_iff_eq_bot.mpr Generators.ker_mvPolynomial
  have : Subsingleton P.toExtension.Cotangent := Cotangent.mk_surjective.subsingleton
  have := P.toExtension.h1Cotangentι_injective.subsingleton
  exact ⟨inferInstance, P.equivH1Cotangent.symm.subsingleton⟩

@[deprecated (since := "2026-05-22")] alias mvPolynomial := instFormallySmoothMvPolynomial

end

namespace FormallySmooth

/--
theorem `exists_lift` / 定理 `exists_lift`

English:
theorem exists_lift
  proof: by
  revert g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  revert ‹Algebra R B›
  apply Ideal.IsNilpotent.induction_on (S := B) I hI
  · intro B _ I hI _; exact FormallySmooth.comp_surjective R A I hI
  · intro B _ I J hIJ h₁ h₂ _ g
    let : ((B ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃

中文:
定理 exists_lift
  证明: by
  revert g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  revert ‹Algebra R B›
  apply Ideal.IsNilpotent.induction_on (S := B) I hI
  · intro B _ I hI _; exact FormallySmooth.comp_surjective R A I hI
  · intro B _ I J hIJ h₁ h₂ _ g
    let : ((B ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃

Depends on / 依赖: Algebra, DoubleQuot, DoubleQuot.quotQuotEquivQuotSup, FormallySmooth, FormallySmooth.comp_surjective, Function, Function.Surjective, Ideal.IsNilpotent.induction_on, Ideal.Quotient.mk, Ideal.quotEquivOfEq, IsNilpotent, J.map, Quotient, Surjective, commutes, comp_surjective, induction_on, quotEquivOfEq, quotQuotEquivQuotSup, revert
-/
theorem exists_lift
    [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I) (g : A ->ₐ[R] B ⧸ I) :
    exists f : A ->ₐ[R] B, (Ideal.Quotient.mkₐ R I).comp f = g := by
  revert g
  change Function.Surjective (Ideal.Quotient.mkₐ R I).comp
  revert ‹Algebra R B›
  apply Ideal.IsNilpotent.induction_on (S := B) I hI
  · intro B _ I hI _; exact FormallySmooth.comp_surjective R A I hI
  · intro B _ I J hIJ h₁ h₂ _ g
    let : ((B ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) ≃ₐ[R] B ⧸ J :=
      { (DoubleQuot.quotQuotEquivQuotSup I J).trans
          (Ideal.quotEquivOfEq (sup_eq_right.mpr hIJ)) with
        commutes' := fun x => rfl }
    obtain ⟨g', e⟩ := h₂ (this.symm.toAlgHom.comp g)
    obtain ⟨g', rfl⟩ := h₁ g'
    replace e := congr_arg this.toAlgHom.comp e
    conv_rhs at e =>
      rw [← AlgHom.comp_assoc]; rw [AlgEquiv.comp_symm]; rw [AlgHom.id_comp]
    exact ⟨g', e⟩

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
  body: (FormallySmooth.exists_lift I hI g).choose

@[simp]

中文:
定义 lift
  签名: [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
  定义体: (FormallySmooth.exists_lift I hI g).choose

@[simp]

Depends on / 依赖: FormallySmooth, FormallySmooth.exists_lift, exists_lift
-/
noncomputable def lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A ->ₐ[R] B ⧸ I) : A ->ₐ[R] B :=
  (FormallySmooth.exists_lift I hI g).choose

@[simp]
/--
theorem `comp_lift` / 定理 `comp_lift`

English:
theorem comp_lift
  statement: [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
  proof: (FormallySmooth.exists_lift I hI g).choose_spec

@[simp]

中文:
定理 comp_lift
  结论: [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
  证明: (FormallySmooth.exists_lift I hI g).choose_spec

@[simp]

Depends on / 依赖: FormallySmooth, FormallySmooth.exists_lift, HereditarilyLindelof, HereditarilyLindelof.to_Lindelof, HereditarilyLindelofSpace, choose_spec, exists_lift, to_Lindelof
-/
theorem comp_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A ->ₐ[R] B ⧸ I) : (Ideal.Quotient.mkₐ R I).comp (FormallySmooth.lift I hI g) = g :=
  (FormallySmooth.exists_lift I hI g).choose_spec

@[simp]
/--
theorem `mk_lift` / 定理 `mk_lift`

English:
theorem mk_lift
  statement: [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
  proof: AlgHom.congr_fun (FormallySmooth.comp_lift I hI g :) x

中文:
定理 mk_lift
  结论: [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
  证明: AlgHom.congr_fun (FormallySmooth.comp_lift I hI g :) x

Depends on / 依赖: AlgHom, AlgHom.congr_fun, FormallySmooth, FormallySmooth.comp_lift, comp_lift, congr_fun
-/
theorem mk_lift [FormallySmooth R A] (I : Ideal B) (hI : IsNilpotent I)
    (g : A ->ₐ[R] B ⧸ I) (x : A) : Ideal.Quotient.mk I (FormallySmooth.lift I hI g x) = g x :=
  AlgHom.congr_fun (FormallySmooth.comp_lift I hI g :) x

variable {C : Type*} [CommRing C] [Algebra R C]

/--
Definition of `liftOfSurjective` / `liftOfSurjective` 的定义

English:
definition liftOfSurjective
  signature: [FormallySmooth R A] (f : A ->ₐ[R] C)
  body: FormallySmooth.lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)

中文:
定义 liftOfSurjective
  签名: [FormallySmooth R A] (f : A ->ₐ[R] C)
  定义体: FormallySmooth.lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)

Depends on / 依赖: FormallySmooth, FormallySmooth.lift, Ideal.quotientKerAlgEquivOfSurjective, quotientKerAlgEquivOfSurjective, symm.toAlgHom.comp, toAlgHom
-/
noncomputable def liftOfSurjective [FormallySmooth R A] (f : A ->ₐ[R] C)
    (g : B ->ₐ[R] C) (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B ->+* C)) :
    A ->ₐ[R] B :=
  FormallySmooth.lift _ hg' ((Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom.comp f)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `liftOfSurjective_apply` / 定理 `liftOfSurjective_apply`

English:
theorem liftOfSurjective_apply
  statement: [FormallySmooth R A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  proof: by
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).symm.injective
  conv_rhs => rw [← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply,
    ← FormallySmooth.mk_lift (A := A) _ hg']
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).injective
  rw [AlgEquiv.apply_symm_apply]; rw [Ideal.quotientKerAlgEqu

中文:
定理 liftOfSurjective_apply
  结论: [FormallySmooth R A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  证明: by
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).symm.injective
  conv_rhs => rw [← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply,
    ← FormallySmooth.mk_lift (A := A) _ hg']
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).injective
  rw [AlgEquiv.apply_symm_apply]; rw [Ideal.quotientKerAlgEqu

Depends on / 依赖: AlgEquiv, AlgEquiv.apply_symm_apply, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.comp_apply, FormallySmooth, FormallySmooth.mk_lift, Ideal.quotientKerAlgEquivOfSurjective, Ideal.quotientKerAlgEquivOfSurjective_apply, RingHom, RingHom.coe_coe, RingHom.kerLift_mk, RingHom.ker_coe_toRingHom, SecondCountableTopology, SecondCountableTopology.toHereditarilyLindelof, apply_symm_apply, coe_coe, coe_toAlgHom, comp_apply, conv_rhs
-/
theorem liftOfSurjective_apply [FormallySmooth R A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker g) (x : A) :
    g (FormallySmooth.liftOfSurjective f g hg hg' x) = f x := by
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).symm.injective
  conv_rhs => rw [← AlgEquiv.coe_toAlgHom, ← AlgHom.comp_apply,
    ← FormallySmooth.mk_lift (A := A) _ hg']
  apply (Ideal.quotientKerAlgEquivOfSurjective hg).injective
  rw [AlgEquiv.apply_symm_apply]; rw [Ideal.quotientKerAlgEquivOfSurjective_apply]
  simp only [liftOfSurjective, ← RingHom.ker_coe_toRingHom g, RingHom.kerLift_mk, RingHom.coe_coe]

@[simp]
/--
theorem `comp_liftOfSurjective` / 定理 `comp_liftOfSurjective`

English:
theorem comp_liftOfSurjective
  statement: [FormallySmooth R A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  proof: AlgHom.ext (FormallySmooth.liftOfSurjective_apply f g hg hg')

中文:
定理 comp_liftOfSurjective
  结论: [FormallySmooth R A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
  证明: AlgHom.ext (FormallySmooth.liftOfSurjective_apply f g hg hg')

Depends on / 依赖: AlgHom, AlgHom.ext, FormallySmooth, FormallySmooth.liftOfSurjective_apply, liftOfSurjective_apply
-/
theorem comp_liftOfSurjective [FormallySmooth R A] (f : A ->ₐ[R] C) (g : B ->ₐ[R] C)
    (hg : Function.Surjective g) (hg' : IsNilpotent <| RingHom.ker (g : B ->+* C)) :
    g.comp (FormallySmooth.liftOfSurjective f g hg hg') = f :=
  AlgHom.ext (FormallySmooth.liftOfSurjective_apply f g hg hg')

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EssFiniteType
  signature: R A] [FormallySmooth R A] : Module.FinitePresentation A Ω[A⁄R]
  body: Module.finitePresentation_of_projective A Ω[A⁄R]

中文:
实例 [EssFiniteType
  签名: R A] [FormallySmooth R A] : Module.FinitePresentation A Ω[A⁄R]
  定义体: Module.finitePresentation_of_projective A Ω[A⁄R]

Depends on / 依赖: Module, Module.finitePresentation_of_projective, finitePresentation_of_projective
-/
instance [EssFiniteType R A] [FormallySmooth R A] : Module.FinitePresentation A Ω[A⁄R] :=
  Module.finitePresentation_of_projective A Ω[A⁄R]

end FormallySmooth

namespace Extension

set_option backward.isDefEq.respectTransparency false in
/--
Given extensions `0 → I₁ → P₁ → A → 0` and `0 → I₂ → P₂ → A → 0` with `P₁` formally smooth,
this is an arbitrarily chosen map `P₁/I₁² → P₂/I₂²` of extensions.
-/
noncomputable
/--
Definition of `homInfinitesimal` / `homInfinitesimal` 的定义

English:
definition homInfinitesimal
  signature: (P₁ P₂ : Extension R A) [FormallySmooth R P₁.Ring]
  body: letI lift : P₁.Ring ->ₐ[R] P₂.infinitesimal.Ring := FormallySmooth.liftOfSurjective
    (IsScalarTower.toAlgHom R P₁.Ring A)
    (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A)
    P₂.infinitesimal.algebraMap_surjective
    ⟨2, show P₂.infinitesimal.ker ^ 2 = ⊥ by
      rw [ker_infinitesimal]; ex

中文:
定义 homInfinitesimal
  签名: (P₁ P₂ : Extension R A) [FormallySmooth R P₁.Ring]
  定义体: letI lift : P₁.Ring ->ₐ[R] P₂.infinitesimal.Ring := FormallySmooth.liftOfSurjective
    (IsScalarTower.toAlgHom R P₁.Ring A)
    (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A)
    P₂.infinitesimal.algebraMap_surjective
    ⟨2, show P₂.infinitesimal.ker ^ 2 = ⊥ by
      rw [ker_infinitesimal]; ex

Depends on / 依赖: FormallySmooth, FormallySmooth.liftOfSurjective, Ideal.Quotient.lift, Ideal.cotangentIdeal_square, Ideal.mul_le, IsScalarTower, IsScalarTower.toAlgHom, Quotient, RingHom, RingHom.ker, algebraMap_surjective, cotangentIdeal_square, infinitesimal, infinitesimal.Ring, infinitesimal.algebraMap_surjective, infinitesimal.ker, ker_infinitesimal, liftOfSurjective, mul_le, pow_two
-/
def homInfinitesimal (P₁ P₂ : Extension R A) [FormallySmooth R P₁.Ring] :
    P₁.infinitesimal.Hom P₂.infinitesimal :=
  letI lift : P₁.Ring ->ₐ[R] P₂.infinitesimal.Ring := FormallySmooth.liftOfSurjective
    (IsScalarTower.toAlgHom R P₁.Ring A)
    (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A)
    P₂.infinitesimal.algebraMap_surjective
    ⟨2, show P₂.infinitesimal.ker ^ 2 = ⊥ by
      rw [ker_infinitesimal]; exact Ideal.cotangentIdeal_square _⟩
  { toRingHom := (Ideal.Quotient.liftₐ (P₁.ker ^ 2) lift (by
        change P₁.ker ^ 2 <= RingHom.ker lift
        rw [pow_two]; rw [Ideal.mul_le]
        have : forall r in P₁.ker, lift r in P₂.infinitesimal.ker :=
          fun r hr => (FormallySmooth.liftOfSurjective_apply _
            (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A) _ _ r).trans hr
        intro r hr s hs
        rw [RingHom.mem_ker]; rw [map_mul]; rw [← Ideal.mem_bot]; rw [← P₂.ker.cotangentIdeal_square]; rw [← ker_infinitesimal]; rw [pow_two]
        exact Ideal.mul_mem_mul (this r hr) (this s hs))).toRingHom
    toRingHom_algebraMap := by simp
    algebraMap_toRingHom x := by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact FormallySmooth.liftOfSurjective_apply _
            (IsScalarTower.toAlgHom R P₂.infinitesimal.Ring A) _ _ x }

/-- Formally smooth extensions have isomorphic `H¹(L_P)`. -/
noncomputable
/--
Definition of `H1Cotangent.equivOfFormallySmooth` / `H1Cotangent.equivOfFormallySmooth` 的定义

English:
definition H1Cotangent.equivOfFormallySmooth
  signature: (P₁ P₂ : Extension R A)
  body: .ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₁) ≪≫ₗ
    H1Cotangent.equiv (Extension.homInfinitesimal _ _) (Extension.homInfinitesimal _ _)
    ≪≫ₗ .symm (.ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₂))

中文:
定义 H1Cotangent.equivOfFormallySmooth
  签名: (P₁ P₂ : Extension R A)
  定义体: .ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₁) ≪≫ₗ
    H1Cotangent.equiv (Extension.homInfinitesimal _ _) (Extension.homInfinitesimal _ _)
    ≪≫ₗ .symm (.ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₂))

Depends on / 依赖: Extension, Extension.homInfinitesimal, H1Cotangent, H1Cotangent.equiv, H1Cotangent.map_toInfinitesimal_bijective, homInfinitesimal, map_toInfinitesimal_bijective, ofBijective
-/
def H1Cotangent.equivOfFormallySmooth (P₁ P₂ : Extension R A)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    P₁.H1Cotangent ≃ₗ[A] P₂.H1Cotangent :=
  .ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₁) ≪≫ₗ
    H1Cotangent.equiv (Extension.homInfinitesimal _ _) (Extension.homInfinitesimal _ _)
    ≪≫ₗ .symm (.ofBijective _ (H1Cotangent.map_toInfinitesimal_bijective P₂))

/--
lemma `H1Cotangent.equivOfFormallySmooth_toLinearMap` / 引理 `H1Cotangent.equivOfFormallySmooth_toLinearMap`

English:
lemma H1Cotangent.equivOfFormallySmooth_toLinearMap
  statement: {P₁ P₂ : Extension R A} (f : P₁.Hom P₂)
  proof: by
  ext1 x
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  change ((map (P₁.homInfinitesimal P₂)).restrictScalars A ∘ₗ map P₁.toInfinitesimal) x =
    ((map P₂.toInfinitesimal).restrictScalars A ∘ₗ map f) x
  rw [← map_comp]; rw [← map_comp]; rw [map_eq]

中文:
引理 H1Cotangent.equivOfFormallySmooth_toLinearMap
  结论: {P₁ P₂ : Extension R A} (f : P₁.Hom P₂)
  证明: by
  ext1 x
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  change ((map (P₁.homInfinitesimal P₂)).restrictScalars A ∘ₗ map P₁.toInfinitesimal) x =
    ((map P₂.toInfinitesimal).restrictScalars A ∘ₗ map f) x
  rw [← map_comp]; rw [← map_comp]; rw [map_eq]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, homInfinitesimal, map_comp, map_eq, restrictScalars, symm_apply_eq, toInfinitesimal
-/
lemma H1Cotangent.equivOfFormallySmooth_toLinearMap {P₁ P₂ : Extension R A} (f : P₁.Hom P₂)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    (H1Cotangent.equivOfFormallySmooth P₁ P₂).toLinearMap = map f := by
  ext1 x
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  change ((map (P₁.homInfinitesimal P₂)).restrictScalars A ∘ₗ map P₁.toInfinitesimal) x =
    ((map P₂.toInfinitesimal).restrictScalars A ∘ₗ map f) x
  rw [← map_comp]; rw [← map_comp]; rw [map_eq]

/--
lemma `H1Cotangent.equivOfFormallySmooth_apply` / 引理 `H1Cotangent.equivOfFormallySmooth_apply`

English:
lemma H1Cotangent.equivOfFormallySmooth_apply
  statement: {P₁ P₂ : Extension R A} (f : P₁.Hom P₂)
  proof: by
  rw [← equivOfFormallySmooth_toLinearMap]; rw [LinearEquiv.coe_coe]

中文:
引理 H1Cotangent.equivOfFormallySmooth_apply
  结论: {P₁ P₂ : Extension R A} (f : P₁.Hom P₂)
  证明: by
  rw [← equivOfFormallySmooth_toLinearMap]; rw [LinearEquiv.coe_coe]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, coe_coe, equivOfFormallySmooth_toLinearMap
-/
lemma H1Cotangent.equivOfFormallySmooth_apply {P₁ P₂ : Extension R A} (f : P₁.Hom P₂)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] (x) :
    H1Cotangent.equivOfFormallySmooth P₁ P₂ x = map f x := by
  rw [← equivOfFormallySmooth_toLinearMap]; rw [LinearEquiv.coe_coe]

/--
lemma `H1Cotangent.equivOfFormallySmooth_symm` / 引理 `H1Cotangent.equivOfFormallySmooth_symm`

English:
lemma H1Cotangent.equivOfFormallySmooth_symm
  statement: (P₁ P₂ : Extension R A)
  proof: rfl

中文:
引理 H1Cotangent.equivOfFormallySmooth_symm
  结论: (P₁ P₂ : Extension R A)
  证明: rfl

Depends on / 依赖: exists_compact_mem_nhds, isCompact_univ_pi, set_pi_mem_nhds, toFinite, univ.toFinite
-/
lemma H1Cotangent.equivOfFormallySmooth_symm (P₁ P₂ : Extension R A)
    [FormallySmooth R P₁.Ring] [FormallySmooth R P₂.Ring] :
    (equivOfFormallySmooth P₁ P₂).symm = equivOfFormallySmooth P₂ P₁ := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Any formally smooth extension can be used to calculate `H¹(L_{A/R})`. -/
noncomputable
/--
Definition of `equivH1CotangentOfFormallySmooth` / `equivH1CotangentOfFormallySmooth` 的定义

English:
definition equivH1CotangentOfFormallySmooth
  signature: (P : Extension R A) [FormallySmooth R P.Ring]
  body: haveI : FormallySmooth R (Generators.self R A).toExtension.Ring :=
    inferInstanceAs (FormallySmooth R (MvPolynomial _ _))
  H1Cotangent.equivOfFormallySmooth _ _

中文:
定义 equivH1CotangentOfFormallySmooth
  签名: (P : Extension R A) [FormallySmooth R P.Ring]
  定义体: haveI : FormallySmooth R (Generators.self R A).toExtension.Ring :=
    inferInstanceAs (FormallySmooth R (MvPolynomial _ _))
  H1Cotangent.equivOfFormallySmooth _ _

Depends on / 依赖: CompactSpace, FormallySmooth, Generators, Generators.self, H1Cotangent, H1Cotangent.equivOfFormallySmooth, MvPolynomial, WeaklyLocallyCompactSpace, equivOfFormallySmooth, toExtension, toExtension.Ring
-/
def equivH1CotangentOfFormallySmooth (P : Extension R A) [FormallySmooth R P.Ring] :
    P.H1Cotangent ≃ₗ[A] H1Cotangent R A :=
  haveI : FormallySmooth R (Generators.self R A).toExtension.Ring :=
    inferInstanceAs (FormallySmooth R (MvPolynomial _ _))
  H1Cotangent.equivOfFormallySmooth _ _

/--
lemma `cotangentComplex_injective_iff` / 引理 `cotangentComplex_injective_iff`

English:
lemma cotangentComplex_injective_iff
  proof: by
  rw [← Algebra.Extension.subsingleton_h1Cotangent]; rw [P.equivH1CotangentOfFormallySmooth.subsingleton_congr]

中文:
引理 cotangentComplex_injective_iff
  证明: by
  rw [← Algebra.Extension.subsingleton_h1Cotangent]; rw [P.equivH1CotangentOfFormallySmooth.subsingleton_congr]

Depends on / 依赖: Algebra, Algebra.Extension.subsingleton_h1Cotangent, Extension, P.equivH1CotangentOfFormallySmooth.subsingleton_congr, equivH1CotangentOfFormallySmooth, subsingleton_congr, subsingleton_h1Cotangent
-/
lemma cotangentComplex_injective_iff
    (P : Extension R A) [FormallySmooth R P.Ring] :
    Function.Injective P.cotangentComplex ↔ Subsingleton (Algebra.H1Cotangent R A) := by
  rw [← Algebra.Extension.subsingleton_h1Cotangent]; rw [P.equivH1CotangentOfFormallySmooth.subsingleton_congr]

end Algebra.Extension

namespace Algebra.FormallySmooth

section iff_split

variable [Algebra.FormallySmooth R P]

/--
lemma `kerCotangentToTensor_injective_iff` / 引理 `kerCotangentToTensor_injective_iff`

English:
lemma kerCotangentToTensor_injective_iff
  proof: let P' : Algebra.Extension R A := ⟨P, _, Function.surjInv_eq hf⟩
  have : Algebra.FormallySmooth R P'.Ring := ‹_›
  P'.cotangentComplex_injective_iff

中文:
引理 kerCotangentToTensor_injective_iff
  证明: let P' : Algebra.Extension R A := ⟨P, _, Function.surjInv_eq hf⟩
  have : Algebra.FormallySmooth R P'.Ring := ‹_›
  P'.cotangentComplex_injective_iff

Depends on / 依赖: Algebra, Algebra.Extension, Algebra.FormallySmooth, Extension, FormallySmooth, Function, Function.surjInv_eq, cotangentComplex_injective_iff, surjInv_eq
-/
lemma kerCotangentToTensor_injective_iff
    [Algebra P A] [IsScalarTower R P A] (hf : Function.Surjective (algebraMap P A)) :
    Function.Injective (kerCotangentToTensor R P A) ↔ Subsingleton (Algebra.H1Cotangent R A) :=
  let P' : Algebra.Extension R A := ⟨P, _, Function.surjInv_eq hf⟩
  have : Algebra.FormallySmooth R P'.Ring := ‹_›
  P'.cotangentComplex_injective_iff

/--
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] A`
with kernel `I` (typically a presentation `R[X] → A`),
`A` is formally smooth iff the `P`-linear map `I/I² → A ⊗[P] Ω[P⁄R]` is split injective.
Also see `Algebra.Extension.formallySmooth_iff_split_injection`
for the version in terms of `Extension`.
-/
@[stacks 031I]
/--
theorem `iff_split_injection` / 定理 `iff_split_injection`

English:
theorem iff_split_injection
  proof: by
  rw [formallySmooth_iff]; rw [and_comm]; rw [Module.Projective.iff_split_of_projective (KaehlerDifferential.mapBaseChange R P A)
      (mapBaseChange_surjective R P A hf)]; rw [← kerCotangentToTensor_injective_iff hf]
  convert!
    (((exact_kerCotangentToTensor_mapBaseChange R _ _ hf).split_tfa

中文:
定理 iff_split_injection
  证明: by
  rw [formallySmooth_iff]; rw [and_comm]; rw [Module.Projective.iff_split_of_projective (KaehlerDifferential.mapBaseChange R P A)
      (mapBaseChange_surjective R P A hf)]; rw [← kerCotangentToTensor_injective_iff hf]
  convert!
    (((exact_kerCotangentToTensor_mapBaseChange R _ _ hf).split_tfa

Depends on / 依赖: KaehlerDifferential, KaehlerDifferential.mapBaseChange, LinearMap, LinearMap.ext_iff, LinearMap.extendScalarsOfSurjectiveEquiv, Module, Module.Projective.iff_split_of_projective, Projective, and_comm, and_iff_right, convert, exact_kerCotangentToTensor_mapBaseChange, exists_congr_right, ext_iff, extendScalarsOfSurjectiveEquiv, formallySmooth_iff, iff_split_of_projective, kerCotangentToTensor_injective_iff, mapBaseChange, mapBaseChange_surjective
-/
theorem iff_split_injection
    [Algebra P A] [IsScalarTower R P A] (hf : Function.Surjective (algebraMap P A)) :
    Algebra.FormallySmooth R A ↔ exists l, l ∘ₗ (kerCotangentToTensor R P A) = LinearMap.id := by
  rw [formallySmooth_iff]; rw [and_comm]; rw [Module.Projective.iff_split_of_projective (KaehlerDifferential.mapBaseChange R P A)
      (mapBaseChange_surjective R P A hf)]; rw [← kerCotangentToTensor_injective_iff hf]
  convert!
    (((exact_kerCotangentToTensor_mapBaseChange R _ _ hf).split_tfae' (g :=
          (KaehlerDifferential.mapBaseChange R P A).restrictScalars P)).out
      0 1) using 2
  · rw [← (LinearMap.extendScalarsOfSurjectiveEquiv hf).exists_congr_right]
    simp [LinearMap.ext_iff]
  · rw [and_iff_right (by exact mapBaseChange_surjective R P A hf)]

set_option backward.isDefEq.respectTransparency.types false in
/--
Given a formally smooth `R`-algebra `P` and a surjective algebra homomorphism `f : P →ₐ[R] S`
with kernel `I` (typically a presentation `R[X] → S`),
`S` is formally smooth iff the `P`-linear map `I/I² → S ⊗[P] Ω[P⁄R]` is split injective.
-/
@[stacks 031I]
/--
theorem `_root_.Algebra.Extension.formallySmooth_iff_split_injection` / 定理 `_root_.Algebra.Extension.formallySmooth_iff_split_injection`

English:
theorem _root_.Algebra.Extension.formallySmooth_iff_split_injection
  proof: by
  refine (Algebra.FormallySmooth.iff_split_injection P.algebraMap_surjective).trans ?_
  let e : P.ker.Cotangent ≃ₗ[P.Ring] P.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' r m := by ext1; simp; rfl }
  constructor
  · intro ⟨l, hl⟩
    exact ⟨(e.comp l).extendScalarsOfSurjective P.algebraMa

中文:
定理 _root_.Algebra.Extension.formallySmooth_iff_split_injection
  证明: by
  refine (Algebra.FormallySmooth.iff_split_injection P.algebraMap_surjective).trans ?_
  let e : P.ker.Cotangent ≃ₗ[P.Ring] P.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' r m := by ext1; simp; rfl }
  constructor
  · intro ⟨l, hl⟩
    exact ⟨(e.comp l).extendScalarsOfSurjective P.algebraMa

Depends on / 依赖: AddEquiv, AddEquiv.refl, Algebra, Algebra.FormallySmooth.iff_split_injection, Cotangent, DFunLike, DFunLike.congr_fun, FormallySmooth, LinearMap, LinearMap.ext, P.Cotangent, P.Ring, P.algebraMap_surjective, P.ker.Cotangent, algebraMap_surjective, congr_fun, e.comp, e.symm.toLinearMap, extendScalarsOfSurjective, iff_split_injection
-/
theorem _root_.Algebra.Extension.formallySmooth_iff_split_injection
    (P : Algebra.Extension.{w} R A) [FormallySmooth R P.Ring] :
    Algebra.FormallySmooth R A ↔ exists l, l ∘ₗ P.cotangentComplex = LinearMap.id := by
  refine (Algebra.FormallySmooth.iff_split_injection P.algebraMap_surjective).trans ?_
  let e : P.ker.Cotangent ≃ₗ[P.Ring] P.Cotangent :=
    { __ := AddEquiv.refl _, map_smul' r m := by ext1; simp; rfl }
  constructor
  · intro ⟨l, hl⟩
    exact ⟨(e.comp l).extendScalarsOfSurjective P.algebraMap_surjective,
      LinearMap.ext (DFunLike.congr_fun hl : _)⟩
  · intro ⟨l, hl⟩
    exact ⟨e.symm.toLinearMap ∘ₗ l.restrictScalars P.Ring,
      LinearMap.ext (DFunLike.congr_fun hl : _)⟩

/--
theorem `iff_split_surjection` / 定理 `iff_split_surjection`

English:
theorem iff_split_surjection
  given: (f : P ->ₐ[R] A) (hf : Function.Surjective f)
  proof: by
  let := f.toAlgebra
  rw [iff_split_injection hf]; rw [← nonempty_subtype]; rw [← nonempty_subtype]; rw [(retractionKerCotangentToTensorEquivSection hf).nonempty_congr]
  rfl

中文:
定理 iff_split_surjection
  条件: (f : P ->ₐ[R] A) (hf : Function.Surjective f)
  证明: by
  let := f.toAlgebra
  rw [iff_split_injection hf]; rw [← nonempty_subtype]; rw [← nonempty_subtype]; rw [(retractionKerCotangentToTensorEquivSection hf).nonempty_congr]
  rfl

Depends on / 依赖: f.toAlgebra, iff_split_injection, nonempty_congr, nonempty_subtype, retractionKerCotangentToTensorEquivSection, toAlgebra
-/
theorem iff_split_surjection (f : P ->ₐ[R] A) (hf : Function.Surjective f) :
    FormallySmooth R A ↔ exists g, f.kerSquareLift.comp g = AlgHom.id R A := by
  let := f.toAlgebra
  rw [iff_split_injection hf]; rw [← nonempty_subtype]; rw [← nonempty_subtype]; rw [(retractionKerCotangentToTensorEquivSection hf).nonempty_congr]
  rfl

/--
theorem `of_split` / 定理 `of_split`

English:
theorem of_split
  statement: (f : P ->ₐ[R] A) (g : A ->ₐ[R] P ⧸ RingHom.ker f.toRingHom ^ 2)
  proof: by
  refine (iff_split_surjection f fun x => ?_).mpr ⟨g, h⟩
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g x)
  exact ⟨y, congr(f.kerSquareLift $hy).trans congr($h x)⟩

中文:
定理 of_split
  结论: (f : P ->ₐ[R] A) (g : A ->ₐ[R] P ⧸ RingHom.ker f.toRingHom ^ 2)
  证明: by
  refine (iff_split_surjection f fun x => ?_).mpr ⟨g, h⟩
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g x)
  exact ⟨y, congr(f.kerSquareLift $hy).trans congr($h x)⟩

Depends on / 依赖: Ideal.Quotient.mk_surjective, Quotient, f.kerSquareLift, iff_split_surjection, kerSquareLift, mk_surjective
-/
theorem of_split (f : P ->ₐ[R] A) (g : A ->ₐ[R] P ⧸ RingHom.ker f.toRingHom ^ 2)
    (h : f.kerSquareLift.comp g = AlgHom.id R A) :
    FormallySmooth R A := by
  refine (iff_split_surjection f fun x => ?_).mpr ⟨g, h⟩
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (g x)
  exact ⟨y, congr(f.kerSquareLift $hy).trans congr($h x)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `of_comp_surjective` / 定理 `of_comp_surjective`

English:
theorem of_comp_surjective
  proof: by
  let P := Generators.self R A
  let f := IsScalarTower.toAlgHom R P.Ring A
  rw [iff_split_surjection f P.algebraMap_surjective]
  have surj : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ P.algebraMap_surjective
  have sqz : RingHom.ker f.kerSquareL

中文:
定理 of_comp_surjective
  证明: by
  let P := Generators.self R A
  let f := IsScalarTower.toAlgHom R P.Ring A
  rw [iff_split_surjection f P.algebraMap_surjective]
  have surj : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ P.algebraMap_surjective
  have sqz : RingHom.ker f.kerSquareL

Depends on / 依赖: AlgHom, AlgHom.ker_kerSquareLift, AlgHom.toRingHom_eq_coe, Function, Function.Surjective, Generators, Generators.self, Ideal.Quotient.lift_surjective_of_surjective, Ideal.cotangentIdeal_square, Ideal.quotientKerAlgEqui, IsScalarTower, IsScalarTower.toAlgHom, P.Ring, P.algebraMap_surjective, Quotient, RingHom, RingHom.ker, RingHom.ker_coe_toRingHom, Surjective, algebraMap_surjective
-/
theorem of_comp_surjective
    (H : forall ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B) (_ : I ^ 2 = ⊥),
        Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ I)) :
    FormallySmooth R A := by
  let P := Generators.self R A
  let f := IsScalarTower.toAlgHom R P.Ring A
  rw [iff_split_surjection f P.algebraMap_surjective]
  have surj : Function.Surjective f.kerSquareLift :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ P.algebraMap_surjective
  have sqz : RingHom.ker f.kerSquareLift.toRingHom ^ 2 = ⊥ := by
    rw [AlgHom.ker_kerSquareLift]; rw [Ideal.cotangentIdeal_square]
  dsimp only [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom] at sqz
  obtain ⟨g, hg⟩ := H _ sqz (Ideal.quotientKerAlgEquivOfSurjective surj).symm.toAlgHom
  refine ⟨g, AlgHom.ext fun x => congr(f.kerSquareLift.kerLift ($hg x)).trans ?_⟩
  obtain ⟨x, rfl⟩ := (Ideal.quotientKerAlgEquivOfSurjective surj).surjective x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [AlgHom.toRingHom_eq_coe, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    AlgHom.coe_id, id_eq]
  simp only [Ideal.quotientKerAlgEquivOfSurjective_apply]

/--
theorem `iff_comp_surjective` / 定理 `iff_comp_surjective`

English:
theorem iff_comp_surjective
  proof: ⟨fun _ _ => comp_surjective R A, of_comp_surjective⟩

中文:
定理 iff_comp_surjective
  证明: ⟨fun _ _ => comp_surjective R A, of_comp_surjective⟩

Depends on / 依赖: comp_surjective, of_comp_surjective
-/
theorem iff_comp_surjective :
   FormallySmooth R A ↔ forall ⦃B : Type max u v⦄ [CommRing B] [Algebra R B] (I : Ideal B), I ^ 2 = ⊥ ->
      Function.Surjective ((Ideal.Quotient.mkₐ R I).comp : (A ->ₐ[R] B) -> A ->ₐ[R] B ⧸ I) :=
  ⟨fun _ _ => comp_surjective R A, of_comp_surjective⟩

end iff_split

section OfEquiv

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/--
theorem `of_equiv` / 定理 `of_equiv`

English:
theorem of_equiv
  given: [FormallySmooth R A] (e : A ≃ₐ[R] B)
  statement: FormallySmooth R B
  proof: (iff_split_surjection e.toAlgHom e.surjective).mpr
    ⟨(Ideal.Quotient.mkₐ _ _).comp e.symm, AlgHom.ext e.apply_symm_apply⟩

中文:
定理 of_equiv
  条件: [FormallySmooth R A] (e : A ≃ₐ[R] B)
  结论: FormallySmooth R B
  证明: (iff_split_surjection e.toAlgHom e.surjective).mpr
    ⟨(Ideal.Quotient.mkₐ _ _).comp e.symm, AlgHom.ext e.apply_symm_apply⟩

Depends on / 依赖: AlgHom, AlgHom.ext, Ideal.Quotient.mk, Quotient, apply_symm_apply, e.apply_symm_apply, e.surjective, e.symm, e.toAlgHom, iff_split_surjection, surjective, toAlgHom
-/
theorem of_equiv [FormallySmooth R A] (e : A ≃ₐ[R] B) : FormallySmooth R B :=
  (iff_split_surjection e.toAlgHom e.surjective).mpr
    ⟨(Ideal.Quotient.mkₐ _ _).comp e.symm, AlgHom.ext e.apply_symm_apply⟩

/--
theorem `iff_of_equiv` / 定理 `iff_of_equiv`

English:
theorem iff_of_equiv
  given: (e : A ≃ₐ[R] B)
  statement: FormallySmooth R A ↔ FormallySmooth R B
  proof: ⟨fun _ => of_equiv e, fun _ => of_equiv e.symm⟩

中文:
定理 iff_of_equiv
  条件: (e : A ≃ₐ[R] B)
  结论: FormallySmooth R A ↔ FormallySmooth R B
  证明: ⟨fun _ => of_equiv e, fun _ => of_equiv e.symm⟩

Depends on / 依赖: e.symm, of_equiv
-/
theorem iff_of_equiv (e : A ≃ₐ[R] B) : FormallySmooth R A ↔ FormallySmooth R B :=
  ⟨fun _ => of_equiv e, fun _ => of_equiv e.symm⟩

end OfEquiv

section Polynomial

open scoped Polynomial in
/--
Instance `polynomial` / 实例 `polynomial`

English:
instance polynomial
  signature: (R : Type*) [CommRing R]
  body: .of_equiv (MvPolynomial.uniqueAlgEquiv.{_, 0} R PUnit)

中文:
实例 polynomial
  签名: (R : 类型) [CommRing R]
  定义体: .of_equiv (MvPolynomial.uniqueAlgEquiv.{_, 0} R PUnit)

Depends on / 依赖: MvPolynomial, MvPolynomial.uniqueAlgEquiv, of_equiv, uniqueAlgEquiv
-/
instance polynomial (R : Type*) [CommRing R] :
  FormallySmooth R R[X] := .of_equiv (MvPolynomial.uniqueAlgEquiv.{_, 0} R PUnit)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FormallySmooth R R
  body: .of_equiv (MvPolynomial.isEmptyAlgEquiv R Empty)

中文:
实例 :
  签名: FormallySmooth R R
  定义体: .of_equiv (MvPolynomial.isEmptyAlgEquiv R Empty)

Depends on / 依赖: LocallyCompactPair, LocallyCompactSpace, MvPolynomial, MvPolynomial.isEmptyAlgEquiv, isEmptyAlgEquiv, of_equiv
-/
instance : FormallySmooth R R := .of_equiv (MvPolynomial.isEmptyAlgEquiv R Empty)

end Polynomial

section Comp

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: [FormallySmooth R A] [FormallySmooth A B]
  statement: FormallySmooth R B
  proof: by
  refine .of_comp_surjective fun C _ _ I hI f => ?_
  obtain ⟨f', e⟩ := FormallySmooth.comp_surjective _ _ I hI (f.comp (IsScalarTower.toAlgHom R A B))
  let := f'.toRingHom.toAlgebra
  obtain ⟨f'', e'⟩ := comp_surjective _ _ I hI { f with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom

中文:
定理 comp
  条件: [FormallySmooth R A] [FormallySmooth A B]
  结论: FormallySmooth R B
  证明: by
  refine .of_comp_surjective fun C _ _ I hI f => ?_
  obtain ⟨f', e⟩ := FormallySmooth.comp_surjective _ _ I hI (f.comp (IsScalarTower.toAlgHom R A B))
  let := f'.toRingHom.toAlgebra
  obtain ⟨f'', e'⟩ := comp_surjective _ _ I hI { f with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom

Depends on / 依赖: AlgHom, AlgHom.congr_fun, AlgHom.ext, AlgHom.restrictScalars, FormallySmooth, FormallySmooth.comp_surjective, IsScalarTower, IsScalarTower.toAlgHom, LocallyCompactSpace, WeaklyLocallyCompactSpace, apply_fun, commutes, comp_surjective, congr_fun, e.symm, f.comp, of_comp_surjective, restrictScalars, toAlgHom, toAlgebra
-/
theorem comp [FormallySmooth R A] [FormallySmooth A B] : FormallySmooth R B := by
  refine .of_comp_surjective fun C _ _ I hI f => ?_
  obtain ⟨f', e⟩ := FormallySmooth.comp_surjective _ _ I hI (f.comp (IsScalarTower.toAlgHom R A B))
  let := f'.toRingHom.toAlgebra
  obtain ⟨f'', e'⟩ := comp_surjective _ _ I hI { f with commutes' := AlgHom.congr_fun e.symm }
  apply_fun AlgHom.restrictScalars R at e'
  exact ⟨f''.restrictScalars _, e'.trans (AlgHom.ext fun _ => rfl)⟩

/--
lemma `of_restrictScalars` / 引理 `of_restrictScalars`

English:
lemma of_restrictScalars
  given: [FormallyUnramified R A] [FormallySmooth R B]
  proof: by
  refine iff_comp_surjective.mpr fun C _ _ I hI f => ?_
  algebraize [(algebraMap A C).comp (algebraMap R A)]
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective _ _ I hI (f.restrictScalars R)
  suffices g.comp (IsScalarTower.toAlgHom R A B) = IsScalarTower.toAlgHom R A C from
    ⟨{ __ :=

中文:
引理 of_restrictScalars
  条件: [FormallyUnramified R A] [FormallySmooth R B]
  证明: by
  refine iff_comp_surjective.mpr fun C _ _ I hI f => ?_
  algebraize [(algebraMap A C).comp (algebraMap R A)]
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective _ _ I hI (f.restrictScalars R)
  suffices g.comp (IsScalarTower.toAlgHom R A B) = IsScalarTower.toAlgHom R A C from
    ⟨{ __ :=

Depends on / 依赖: AlgHom, AlgHom.comp_assoc, AlgHom.ext, Algebra, Algebra.FormallySmooth.comp_surjective, Algebra.FormallyUnramified.comp_injective, FormallySmooth, FormallyUnramified, IsScalarTower, IsScalarTower.toAlgHom, algebraMap, algebraize, commutes, comp_assoc, comp_injective, comp_surjective, f.commutes, f.restrictScalars, g.comp, iff_comp_surjective
-/
lemma of_restrictScalars [FormallyUnramified R A] [FormallySmooth R B] :
    FormallySmooth A B := by
  refine iff_comp_surjective.mpr fun C _ _ I hI f => ?_
  algebraize [(algebraMap A C).comp (algebraMap R A)]
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective _ _ I hI (f.restrictScalars R)
  suffices g.comp (IsScalarTower.toAlgHom R A B) = IsScalarTower.toAlgHom R A C from
    ⟨{ __ := g, commutes' x := congr($this x) }, AlgHom.ext fun x => congr($hg x)⟩
  apply Algebra.FormallyUnramified.comp_injective _ hI
  rw [← AlgHom.comp_assoc]; rw [hg]
  exact AlgHom.ext f.commutes

end Comp

section surjective

variable {R : Type*} [CommRing R]
variable {P A : Type*} [CommRing A] [Algebra R A] [CommRing P] [Algebra R P]
variable (f : P ->ₐ[R] A)

/--
lemma `iff_of_surjective` / 引理 `iff_of_surjective`

English:
lemma iff_of_surjective
  given: (h : Function.Surjective (algebraMap R A))
  proof: by
  rw [Algebra.FormallySmooth.iff_split_surjection (Algebra.ofId R A) h]
  constructor
  · intro ⟨g, hg⟩
    let e : A ≃ₐ[R] R ⧸ RingHom.ker (algebraMap R A) ^ 2 :=
      .ofAlgHom _ _ (Ideal.Quotient.algHom_ext _ (by ext)) hg
    rw [IsIdempotentElem]; rw [← pow_two]; rw [← Ideal.mk_ker (I := _ ^

中文:
引理 iff_of_surjective
  条件: (h : Function.Surjective (algebraMap R A))
  证明: by
  rw [Algebra.FormallySmooth.iff_split_surjection (Algebra.ofId R A) h]
  constructor
  · intro ⟨g, hg⟩
    let e : A ≃ₐ[R] R ⧸ RingHom.ker (algebraMap R A) ^ 2 :=
      .ofAlgHom _ _ (Ideal.Quotient.algHom_ext _ (by ext)) hg
    rw [IsIdempotentElem]; rw [← pow_two]; rw [← Ideal.mk_ker (I := _ ^

Depends on / 依赖: Algebra, Algebra.FormallySmooth.iff_split_surjection, Algebra.ofId, FormallySmooth, Ideal.Quotient.algHom_ext, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, Ideal.quotientEquivAlgOfEq, IsIdempotentElem, Quotient, RingHom, RingHom.ker, RingHom.ker_comp_of_injective, algHom_ext, algebraMap, algebraMap_eq, comp_algebraMap, e.injective, e.toAlgHom.comp_algebraMap, iff_split_surjection
-/
lemma iff_of_surjective (h : Function.Surjective (algebraMap R A)) :
    Algebra.FormallySmooth R A ↔ IsIdempotentElem (RingHom.ker (algebraMap R A)) := by
  rw [Algebra.FormallySmooth.iff_split_surjection (Algebra.ofId R A) h]
  constructor
  · intro ⟨g, hg⟩
    let e : A ≃ₐ[R] R ⧸ RingHom.ker (algebraMap R A) ^ 2 :=
      .ofAlgHom _ _ (Ideal.Quotient.algHom_ext _ (by ext)) hg
    rw [IsIdempotentElem]; rw [← pow_two]; rw [← Ideal.mk_ker (I := _ ^ 2)]; rw [← Ideal.Quotient.algebraMap_eq]; rw [← e.toAlgHom.comp_algebraMap]; rw [RingHom.ker_comp_of_injective _ (by exact e.injective)]
  · intro H
    let e := (Ideal.quotientEquivAlgOfEq _ ((pow_two _).trans H)).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R A) h)
exact ⟨e.symm.toAlgHom, AlgHom.ext h.forall.mpr fun x => by simp⟩

end surjective

section BaseChange


variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]
variable (B : Type*) [CommRing B] [Algebra R B]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FormallySmooth
  signature: R A] : FormallySmooth B (B otimes[R] A)
  body: by
  refine .of_comp_surjective fun C _ _ I hI f => ?_
  let := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨TensorProduct.productLeftAlgHom (Algebra.ofId B C) ?_, ?_⟩
  · exact FormallySmooth.lift I ⟨2, hI⟩ ((f.rest

中文:
实例 [FormallySmooth
  签名: R A] : FormallySmooth B (B otimes[R] A)
  定义体: by
  refine .of_comp_surjective fun C _ _ I hI f => ?_
  let := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨TensorProduct.productLeftAlgHom (Algebra.ofId B C) ?_, ?_⟩
  · exact FormallySmooth.lift I ⟨2, hI⟩ ((f.rest

Depends on / 依赖: AlgHom, AlgHom.restrictScalars_injective, Algebr, Algebra, Algebra.ofId, FormallySmooth, FormallySmooth.lift, IsScalarTower, IsScalarTower.of_algebraMap_eq, TensorProduct, TensorProduct.ext, TensorProduct.includeRight, TensorProduct.productLeftAlgHom, algebraMap, f.restrictScalars, includeRight, of_algebraMap_eq, of_comp_surjective, productLeftAlgHom, restrictScalars
-/
instance [FormallySmooth R A] : FormallySmooth B (B otimes[R] A) := by
  refine .of_comp_surjective fun C _ _ I hI f => ?_
  let := ((algebraMap B C).comp (algebraMap R B)).toAlgebra
  have : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq' rfl
  refine ⟨TensorProduct.productLeftAlgHom (Algebra.ofId B C) ?_, ?_⟩
  · exact FormallySmooth.lift I ⟨2, hI⟩ ((f.restrictScalars R).comp TensorProduct.includeRight)
  · apply AlgHom.restrictScalars_injective R
    apply TensorProduct.ext'
    intro b a
    suffices algebraMap B _ b * f (1 otimesₜ[R] a) = f (b otimesₜ[R] a) by simpa [Algebra.ofId_apply]
    rw [← Algebra.smul_def]; rw [← map_smul]; rw [TensorProduct.smul_tmul']; rw [smul_eq_mul]; rw [mul_one]

end BaseChange

section Localization

variable {R A Rₘ Sₘ : Type*} [CommRing R] [CommRing A] [CommRing Rₘ] [CommRing Sₘ]
variable (M : Submonoid R)
variable [Algebra R A] [Algebra R Sₘ] [Algebra A Sₘ] [Algebra R Rₘ] [Algebra Rₘ Sₘ]
variable [IsScalarTower R Rₘ Sₘ] [IsScalarTower R A Sₘ]
variable [IsLocalization M Rₘ] [IsLocalization (M.map (algebraMap R A)) Sₘ]
include M

/--
theorem `of_isLocalization` / 定理 `of_isLocalization`

English:
theorem of_isLocalization
  statement: FormallySmooth R Rₘ
  proof: by
  refine .of_comp_surjective fun Q _ _ I e f => ?_
  have : forall x : M, IsUnit (algebraMap R Q x) := by
    intro x
    apply (IsNilpotent.isUnit_quotient_mk_iff ⟨2, e⟩).mp
    convert! (IsLocalization.map_units Rₘ x).map f
    simp only [Ideal.Quotient.mk_algebraMap, AlgHom.commutes]
  let : R

中文:
定理 of_isLocalization
  结论: FormallySmooth R Rₘ
  证明: by
  refine .of_comp_surjective fun Q _ _ I e f => ?_
  have : forall x : M, IsUnit (algebraMap R Q x) := by
    intro x
    apply (IsNilpotent.isUnit_quotient_mk_iff ⟨2, e⟩).mp
    convert! (IsLocalization.map_units Rₘ x).map f
    simp only [Ideal.Quotient.mk_algebraMap, AlgHom.commutes]
  let : R

Depends on / 依赖: AlgHom, AlgHom.coe_ringHom_injective, AlgHom.commutes, Ideal.Quotient.mk_algebraMap, IsLocalization, IsLocalization.lift, IsLocalization.lift_eq, IsLocalization.map_units, IsLocalization.ringHom_ext, IsNilpotent, IsNilpotent.isUnit_quotient_mk_iff, IsUnit, Quotient, algebraMap, coe_ringHom_injective, commutes, convert, isUnit_quotient_mk_iff, lift_eq, map_units
-/
theorem of_isLocalization : FormallySmooth R Rₘ := by
  refine .of_comp_surjective fun Q _ _ I e f => ?_
  have : forall x : M, IsUnit (algebraMap R Q x) := by
    intro x
    apply (IsNilpotent.isUnit_quotient_mk_iff ⟨2, e⟩).mp
    convert! (IsLocalization.map_units Rₘ x).map f
    simp only [Ideal.Quotient.mk_algebraMap, AlgHom.commutes]
  let : Rₘ ->ₐ[R] Q :=
    { IsLocalization.lift this with commutes' := IsLocalization.lift_eq this }
  use this
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext M ?_
  ext
  simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FormallySmooth
  signature: R A] (M
  body: have : FormallySmooth A (Localization M) := of_isLocalization M
  .comp _ A _

中文:
实例 [FormallySmooth
  签名: R A] (M
  定义体: have : FormallySmooth A (Localization M) := of_isLocalization M
  .comp _ A _

Depends on / 依赖: FormallySmooth, Localization, of_isLocalization
-/
instance [FormallySmooth R A] (M : Submonoid A) : FormallySmooth R (Localization M) :=
  have : FormallySmooth A (Localization M) := of_isLocalization M
  .comp _ A _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `localization_base` / 定理 `localization_base`

English:
theorem localization_base
  given: [FormallySmooth R Sₘ]
  statement: FormallySmooth Rₘ Sₘ
  proof: by
  refine .of_comp_surjective fun Q _ _ I e f => ?_
  let := ((algebraMap Rₘ Q).comp (algebraMap R Rₘ)).toAlgebra
  let : IsScalarTower R Rₘ Q := IsScalarTower.of_algebraMap_eq' rfl
  let f : Sₘ ->ₐ[Rₘ] Q := by
    refine { FormallySmooth.lift I ⟨2, e⟩ (f.restrictScalars R) with commutes' := ?_ }


中文:
定理 localization_base
  条件: [FormallySmooth R Sₘ]
  结论: FormallySmooth Rₘ Sₘ
  证明: by
  refine .of_comp_surjective fun Q _ _ I e f => ?_
  let := ((algebraMap Rₘ Q).comp (algebraMap R Rₘ)).toAlgebra
  let : IsScalarTower R Rₘ Q := IsScalarTower.of_algebraMap_eq' rfl
  let f : Sₘ ->ₐ[Rₘ] Q := by
    refine { FormallySmooth.lift I ⟨2, e⟩ (f.restrictScalars R) with commutes' := ?_ }


Depends on / 依赖: FormallySmooth, FormallySmooth.lift, IsLocalization, IsLocalization.ringHom_ext, IsScalarTower, IsScalarTower.of_algebraMap_eq, RingHom, RingHom.comp, RingHom.comp_assoc, algebraMap, commutes, comp_assoc, f.restrictScalars, of_algebraMap_eq, of_comp_surjective, restrictScalars, ringHom_ext, toAlgebra
-/
theorem localization_base [FormallySmooth R Sₘ] : FormallySmooth Rₘ Sₘ := by
  refine .of_comp_surjective fun Q _ _ I e f => ?_
  let := ((algebraMap Rₘ Q).comp (algebraMap R Rₘ)).toAlgebra
  let : IsScalarTower R Rₘ Q := IsScalarTower.of_algebraMap_eq' rfl
  let f : Sₘ ->ₐ[Rₘ] Q := by
    refine { FormallySmooth.lift I ⟨2, e⟩ (f.restrictScalars R) with commutes' := ?_ }
    intro r
    change
      (RingHom.comp (FormallySmooth.lift I ⟨2, e⟩ (f.restrictScalars R) : Sₘ ->+* Q)
            (algebraMap _ _))
          r =
        algebraMap _ _ r
    congr 1
    refine IsLocalization.ringHom_ext M ?_
    rw [RingHom.comp_assoc]; rw [← IsScalarTower.algebraMap_eq]; rw [← IsScalarTower.algebraMap_eq]; rw [AlgHom.comp_algebraMap]
  use f
  ext
  simp [f]

/--
theorem `localization_map` / 定理 `localization_map`

English:
theorem localization_map
  given: [FormallySmooth R A]
  statement: FormallySmooth Rₘ Sₘ
  proof: by
  have : FormallySmooth A Sₘ := FormallySmooth.of_isLocalization (M.map (algebraMap R A))
  have : FormallySmooth R Sₘ := FormallySmooth.comp R A Sₘ
  exact FormallySmooth.localization_base M

中文:
定理 localization_map
  条件: [FormallySmooth R A]
  结论: FormallySmooth Rₘ Sₘ
  证明: by
  have : FormallySmooth A Sₘ := FormallySmooth.of_isLocalization (M.map (algebraMap R A))
  have : FormallySmooth R Sₘ := FormallySmooth.comp R A Sₘ
  exact FormallySmooth.localization_base M

Depends on / 依赖: FormallySmooth, FormallySmooth.comp, FormallySmooth.localization_base, FormallySmooth.of_isLocalization, M.map, algebraMap, localization_base, of_isLocalization
-/
theorem localization_map [FormallySmooth R A] : FormallySmooth Rₘ Sₘ := by
  have : FormallySmooth A Sₘ := FormallySmooth.of_isLocalization (M.map (algebraMap R A))
  have : FormallySmooth R Sₘ := FormallySmooth.comp R A Sₘ
  exact FormallySmooth.localization_base M

end Localization

end FormallySmooth

section

variable (R : Type*) [CommRing R]
variable (A : Type*) [CommRing A] [Algebra R A]

/-- An `R` algebra `A` is smooth if it is formally smooth and of finite presentation. -/
@[stacks 00T2 "In the stacks project, the definition of smooth is completely different, and tag
<https://stacks.math.columbia.edu/tag/00TN> proves that their definition is equivalent to this.",
mk_iff]
/--
Definition of `Smooth` / `Smooth` 的定义

English:
class Smooth
  parameters: [CommRing R] (A : Type u) [CommRing A] [Algebra R A]
  axioms and operations (2):
    - formallySmooth : FormallySmooth R A  [default: by infer_instance]
    - finitePresentation : FinitePresentation R A  [default: by infer_instance]

中文:
类 Smooth
  参数: [CommRing R] (A : 类型u) [CommRing A] [Algebra R A]
  公理与运算 (2 个):
    - formallySmooth : FormallySmooth R A  [默认: by infer_instance]
    - finitePresentation : FinitePresentation R A  [默认: by infer_instance]

Depends on / 依赖: FinitePresentation, finitePresentation, infer_instance
-/
class Smooth [CommRing R] (A : Type u) [CommRing A] [Algebra R A] : Prop where
  formallySmooth : FormallySmooth R A := by infer_instance
  finitePresentation : FinitePresentation R A := by infer_instance

end

namespace Smooth

attribute [instance] formallySmooth finitePresentation

variable {R : Type*} [CommRing R]
variable {A B : Type*} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/--
theorem `of_equiv` / 定理 `of_equiv`

English:
theorem of_equiv
  given: [Smooth R A] (e : A ≃ₐ[R] B)
  statement: Smooth R B where
  proof: FormallySmooth.of_equiv e
  finitePresentation := FinitePresentation.equiv e

中文:
定理 of_equiv
  条件: [Smooth R A] (e : A ≃ₐ[R] B)
  结论: Smooth R B where
  证明: FormallySmooth.of_equiv e
  finitePresentation := FinitePresentation.equiv e

Depends on / 依赖: FormallySmooth, FormallySmooth.of_equiv, of_equiv
-/
theorem of_equiv [Smooth R A] (e : A ≃ₐ[R] B) : Smooth R B where
  formallySmooth := FormallySmooth.of_equiv e
  finitePresentation := FinitePresentation.equiv e

/--
theorem `of_isLocalization_Away` / 定理 `of_isLocalization_Away`

English:
theorem of_isLocalization_Away
  given: (r : R) [IsLocalization.Away r A]
  statement: Smooth R A where
  proof: Algebra.FormallySmooth.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

中文:
定理 of_isLocalization_Away
  条件: (r : R) [IsLocalization.Away r A]
  结论: Smooth R A where
  证明: Algebra.FormallySmooth.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

Depends on / 依赖: Algebra, Algebra.FormallySmooth.of_isLocalization, FormallySmooth, Submonoid, Submonoid.powers, of_isLocalization, powers
-/
theorem of_isLocalization_Away (r : R) [IsLocalization.Away r A] : Smooth R A where
  formallySmooth := Algebra.FormallySmooth.of_isLocalization (Submonoid.powers r)
  finitePresentation := IsLocalization.Away.finitePresentation r

section Comp

variable (R A B)

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: [Algebra A B] [IsScalarTower R A B] [Smooth R A] [Smooth A B]
  statement: Smooth R B where
  proof: FormallySmooth.comp R A B
  finitePresentation := FinitePresentation.trans R A B

中文:
定理 comp
  条件: [Algebra A B] [IsScalarTower R A B] [Smooth R A] [Smooth A B]
  结论: Smooth R B where
  证明: FormallySmooth.comp R A B
  finitePresentation := FinitePresentation.trans R A B

Depends on / 依赖: FormallySmooth, FormallySmooth.comp
-/
theorem comp [Algebra A B] [IsScalarTower R A B] [Smooth R A] [Smooth A B] : Smooth R B where
  formallySmooth := FormallySmooth.comp R A B
  finitePresentation := FinitePresentation.trans R A B

/--
Instance `baseChange` / 实例 `baseChange`

English:
instance baseChange
  signature: [Smooth R A]

中文:
实例 baseChange
  签名: [Smooth R A]
-/
instance baseChange [Smooth R A] : Smooth B (B otimes[R] A) where

end Comp

end Smooth

end Algebra
