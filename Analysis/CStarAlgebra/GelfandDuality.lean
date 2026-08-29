/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.Fuglede
public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.Algebra
public import Mathlib.Topology.ContinuousMap.Ideals
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Gelfand Duality

The `gelfandTransform` is an algebra homomorphism from a topological `𝕜`-algebra `A` to
`C(characterSpace 𝕜 A, 𝕜)`. In the case where `A` is a commutative complex Banach algebra, then
the Gelfand transform is actually spectrum-preserving (`spectrum.gelfandTransform_eq`). Moreover,
when `A` is a commutative C⋆-algebra over `ℂ`, then the Gelfand transform is a surjective isometry,
and even an equivalence between C⋆-algebras.

Consider the contravariant functors between compact Hausdorff spaces and commutative unital
C⋆algebras `F : Cpct → CommCStarAlg := X ↦ C(X, ℂ)` and
`G : CommCStarAlg → Cpct := A → characterSpace ℂ A` whose actions on morphisms are given by
`WeakDual.CharacterSpace.compContinuousMap` and `ContinuousMap.compStarAlgHom'`, respectively.

Then `η₁ : id → F ∘ G := gelfandStarTransform` and
`η₂ : id → G ∘ F := WeakDual.CharacterSpace.homeoEval` are the natural isomorphisms implementing
**Gelfand Duality**, i.e., the (contravariant) equivalence of these categories.

## Main definitions

* `Ideal.toCharacterSpace` : constructs an element of the character space from a maximal ideal in
  a commutative complex Banach algebra
* `WeakDual.CharacterSpace.compContinuousMap`: The functorial map taking `ψ : A →⋆ₐ[𝕜] B` to a
  continuous function `characterSpace 𝕜 B → characterSpace 𝕜 A` given by pre-composition with `ψ`.

## Main statements

* `spectrum.gelfandTransform_eq` : the Gelfand transform is spectrum-preserving when the algebra is
  a commutative complex Banach algebra.
* `gelfandTransform_isometry` : the Gelfand transform is an isometry when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfandTransform_bijective` : the Gelfand transform is bijective when the algebra is a
  commutative (unital) C⋆-algebra over `ℂ`.
* `gelfandStarTransform_naturality`: The `gelfandStarTransform` is a natural isomorphism
* `WeakDual.CharacterSpace.homeoEval_naturality`: This map implements a natural isomorphism

## TODO

* After defining the category of commutative unital C⋆-algebras, bundle the existing unbundled
  **Gelfand duality** into an actual equivalence (duality) of categories associated to the
  functors `C(·, ℂ)` and `characterSpace ℂ ·` and the natural isomorphisms `gelfandStarTransform`
  and `WeakDual.CharacterSpace.homeoEval`.

## Tags

Gelfand transform, character space, C⋆-algebra
-/

@[expose] public section


open WeakDual

open scoped NNReal

section ComplexBanachAlgebra

open Ideal

variable {A : Type*} [NormedCommRing A] [NormedAlgebra Complex A] [CompleteSpace A] (I : Ideal A)
  [Ideal.IsMaximal I]

/--
Definition of `Ideal.toCharacterSpace` / `Ideal.toCharacterSpace` 的定义

English:
definition Ideal.toCharacterSpace
  signature: : characterSpace Complex A
  body: CharacterSpace.equivAlgHom.symm
    ((NormedRing.algEquivComplexOfComplete
      (letI := Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm : A ⧸ I ->ₐ[Complex] Complex).comp <|
    Quotient.mkₐ Complex I

中文:
定义 Ideal.toCharacterSpace
  签名: : characterSpace Complex A
  定义体: CharacterSpace.equivAlgHom.symm
    ((NormedRing.algEquivComplexOfComplete
      (letI := Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm : A ⧸ I ->ₐ[Complex] Complex).comp <|
    Quotient.mkₐ Complex I

Depends on / 依赖: CharacterSpace, CharacterSpace.equivAlgHom.symm, NormedRing, NormedRing.algEquivComplexOfComplete, Quotient, Quotient.field, Quotient.mk, algEquivComplexOfComplete, equivAlgHom, isUnit_iff_ne_zero
-/
noncomputable def Ideal.toCharacterSpace : characterSpace Complex A :=
CharacterSpace.equivAlgHom.symm
    ((NormedRing.algEquivComplexOfComplete
      (letI := Quotient.field I; isUnit_iff_ne_zero (G₀ := A ⧸ I))).symm : A ⧸ I ->ₐ[Complex] Complex).comp <|
    Quotient.mkₐ Complex I

/--
theorem `Ideal.toCharacterSpace_apply_eq_zero_of_mem` / 定理 `Ideal.toCharacterSpace_apply_eq_zero_of_mem`

English:
theorem Ideal.toCharacterSpace_apply_eq_zero_of_mem
  given: {a : A} (ha : a in I)
  proof: by
  unfold Ideal.toCharacterSpace
  simp only [CharacterSpace.equivAlgHom_symm_coe, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    Quotient.mkₐ_eq_mk, Function.comp_apply, NormedRing.algEquivComplexOfComplete_symm_apply]
  simp_rw [Quotient.eq_zero_iff_mem.mpr ha, spectrum.zero_eq]
  exact Set.eq_of_m

中文:
定理 Ideal.toCharacterSpace_apply_eq_zero_of_mem
  条件: {a : A} (ha : a in I)
  证明: by
  unfold Ideal.toCharacterSpace
  simp only [CharacterSpace.equivAlgHom_symm_coe, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    Quotient.mkₐ_eq_mk, Function.comp_apply, NormedRing.algEquivComplexOfComplete_symm_apply]
  simp_rw [Quotient.eq_zero_iff_mem.mpr ha, spectrum.zero_eq]
  exact Set.eq_of_m

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.coe_comp, CharacterSpace, CharacterSpace.equivAlgHom_symm_coe, Function, Function.comp_apply, Ideal.toCharacterSpace, NormedRing, NormedRing.algEquivComplexOfComplete_symm_apply, Quotient, Quotient.eq_zero_iff_mem.mpr, Quotient.mk, Set.eq_of_mem_singleton, Set.singleton_nonempty, algEquivComplexOfComplete_symm_apply, coe_comp, coe_toAlgHom, comp_apply
-/
theorem Ideal.toCharacterSpace_apply_eq_zero_of_mem {a : A} (ha : a in I) :
    I.toCharacterSpace a = 0 := by
  unfold Ideal.toCharacterSpace
  simp only [CharacterSpace.equivAlgHom_symm_coe, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom,
    Quotient.mkₐ_eq_mk, Function.comp_apply, NormedRing.algEquivComplexOfComplete_symm_apply]
  simp_rw [Quotient.eq_zero_iff_mem.mpr ha, spectrum.zero_eq]
  exact Set.eq_of_mem_singleton (Set.singleton_nonempty (0 : Complex)).some_mem

/--
theorem `WeakDual.CharacterSpace.exists_apply_eq_zero` / 定理 `WeakDual.CharacterSpace.exists_apply_eq_zero`

English:
theorem WeakDual.CharacterSpace.exists_apply_eq_zero
  given: {a : A} (ha : ¬IsUnit a)
  proof: by
  obtain ⟨M, hM, haM⟩ := (span {a}).exists_le_maximal (span_singleton_ne_top ha)
  exact
    ⟨M.toCharacterSpace,
      M.toCharacterSpace_apply_eq_zero_of_mem
        (haM (mem_span_singleton.mpr ⟨1, (mul_one a).symm⟩))⟩

中文:
定理 WeakDual.CharacterSpace.exists_apply_eq_zero
  条件: {a : A} (ha : ¬IsUnit a)
  证明: by
  obtain ⟨M, hM, haM⟩ := (span {a}).exists_le_maximal (span_singleton_ne_top ha)
  exact
    ⟨M.toCharacterSpace,
      M.toCharacterSpace_apply_eq_zero_of_mem
        (haM (mem_span_singleton.mpr ⟨1, (mul_one a).symm⟩))⟩

Depends on / 依赖: M.toCharacterSpace, M.toCharacterSpace_apply_eq_zero_of_mem, exists_le_maximal, mem_span_singleton, mem_span_singleton.mpr, mul_one, span_singleton_ne_top, toCharacterSpace, toCharacterSpace_apply_eq_zero_of_mem
-/
theorem WeakDual.CharacterSpace.exists_apply_eq_zero {a : A} (ha : ¬IsUnit a) :
    exists f : characterSpace Complex A, f a = 0 := by
  obtain ⟨M, hM, haM⟩ := (span {a}).exists_le_maximal (span_singleton_ne_top ha)
  exact
    ⟨M.toCharacterSpace,
      M.toCharacterSpace_apply_eq_zero_of_mem
        (haM (mem_span_singleton.mpr ⟨1, (mul_one a).symm⟩))⟩

/--
theorem `WeakDual.CharacterSpace.mem_spectrum_iff_exists` / 定理 `WeakDual.CharacterSpace.mem_spectrum_iff_exists`

English:
theorem WeakDual.CharacterSpace.mem_spectrum_iff_exists
  given: {a : A} {z : Complex}
  proof: by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨f, hf⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hz
    simp only [map_sub, sub_eq_zero, AlgHomClass.commutes] at hf
    exact ⟨_, hf.symm⟩
  · rintro ⟨f, rfl⟩
    exact AlgHom.apply_mem_spectrum f a

中文:
定理 WeakDual.CharacterSpace.mem_spectrum_iff_exists
  条件: {a : A} {z : Complex}
  证明: by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨f, hf⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hz
    simp only [map_sub, sub_eq_zero, AlgHomClass.commutes] at hf
    exact ⟨_, hf.symm⟩
  · rintro ⟨f, rfl⟩
    exact AlgHom.apply_mem_spectrum f a

Depends on / 依赖: AlgHom, AlgHom.apply_mem_spectrum, AlgHomClass, AlgHomClass.commutes, CharacterSpace, WeakDual, WeakDual.CharacterSpace.exists_apply_eq_zero, apply_mem_spectrum, commutes, exists_apply_eq_zero, hf.symm, map_sub, sub_eq_zero
-/
theorem WeakDual.CharacterSpace.mem_spectrum_iff_exists {a : A} {z : Complex} :
    z in spectrum Complex a ↔ exists f : characterSpace Complex A, f a = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨f, hf⟩ := WeakDual.CharacterSpace.exists_apply_eq_zero hz
    simp only [map_sub, sub_eq_zero, AlgHomClass.commutes] at hf
    exact ⟨_, hf.symm⟩
  · rintro ⟨f, rfl⟩
    exact AlgHom.apply_mem_spectrum f a

/--
theorem `spectrum.gelfandTransform_eq` / 定理 `spectrum.gelfandTransform_eq`

English:
theorem spectrum.gelfandTransform_eq
  given: (a : A)
  proof: by
  ext z
  rw [ContinuousMap.spectrum_eq_range]; rw [WeakDual.CharacterSpace.mem_spectrum_iff_exists]
  exact Iff.rfl

中文:
定理 spectrum.gelfandTransform_eq
  条件: (a : A)
  证明: by
  ext z
  rw [ContinuousMap.spectrum_eq_range]; rw [WeakDual.CharacterSpace.mem_spectrum_iff_exists]
  exact Iff.rfl

Depends on / 依赖: CharacterSpace, ContinuousMap, ContinuousMap.spectrum_eq_range, Iff.rfl, WeakDual, WeakDual.CharacterSpace.mem_spectrum_iff_exists, mem_spectrum_iff_exists, spectrum_eq_range
-/
theorem spectrum.gelfandTransform_eq (a : A) :
    spectrum Complex (gelfandTransform Complex A a) = spectrum Complex a := by
  ext z
  rw [ContinuousMap.spectrum_eq_range]; rw [WeakDual.CharacterSpace.mem_spectrum_iff_exists]
  exact Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: A] : Nonempty (characterSpace Complex A)
  body: ⟨Classical.choose
WeakDual.CharacterSpace.exists_apply_eq_zero zero_mem_nonunits.2 zero_ne_one⟩

中文:
实例 [Nontrivial
  签名: A] : Nonempty (characterSpace Complex A)
  定义体: ⟨Classical.choose
WeakDual.CharacterSpace.exists_apply_eq_zero zero_mem_nonunits.2 zero_ne_one⟩

Depends on / 依赖: CharacterSpace, Classical, Classical.choose, WeakDual, WeakDual.CharacterSpace.exists_apply_eq_zero, exists_apply_eq_zero, zero_mem_nonunits, zero_ne_one
-/
instance [Nontrivial A] : Nonempty (characterSpace Complex A) :=
⟨Classical.choose
WeakDual.CharacterSpace.exists_apply_eq_zero zero_mem_nonunits.2 zero_ne_one⟩

end ComplexBanachAlgebra

section ComplexCStarAlgebra

section Commutative

variable {A : Type*} [CommCStarAlgebra A]

/--
theorem `gelfandTransform_map_star` / 定理 `gelfandTransform_map_star`

English:
theorem gelfandTransform_map_star
  given: (a : A)
  proof: ContinuousMap.ext fun φ => map_star φ a

中文:
定理 gelfandTransform_map_star
  条件: (a : A)
  证明: ContinuousMap.ext fun φ => map_star φ a

Depends on / 依赖: ContinuousMap, ContinuousMap.ext, map_star
-/
theorem gelfandTransform_map_star (a : A) :
    gelfandTransform Complex A (star a) = star (gelfandTransform Complex A a) :=
  ContinuousMap.ext fun φ => map_star φ a

variable (A)

/--
theorem `gelfandTransform_isometry` / 定理 `gelfandTransform_isometry`

English:
theorem gelfandTransform_isometry
  statement: Isometry (gelfandTransform Complex A)
  proof: by
  refine AddMonoidHomClass.isometry_of_norm (gelfandTransform Complex A) fun a => ?_
  /- By `spectrum.gelfandTransform_eq`, the spectra of `star a * a` and its
    `gelfandTransform` coincide. Therefore, so do their spectral radii, and since they are
    self-adjoint, so also do their norms. App

中文:
定理 gelfandTransform_isometry
  结论: Isometry (gelfandTransform Complex A)
  证明: by
  refine AddMonoidHomClass.isometry_of_norm (gelfandTransform Complex A) fun a => ?_
  /- By `spectrum.gelfandTransform_eq`, the spectra of `star a * a` and its
    `gelfandTransform` coincide. Therefore, so do their spectral radii, and since they are
    self-adjoint, so also do their norms. App

Depends on / 依赖: AddMonoidHomClass, AddMonoidHomClass.isometry_of_norm, gelfandTransform, isometry_of_norm
-/
theorem gelfandTransform_isometry : Isometry (gelfandTransform Complex A) := by
  refine AddMonoidHomClass.isometry_of_norm (gelfandTransform Complex A) fun a => ?_
  /- By `spectrum.gelfandTransform_eq`, the spectra of `star a * a` and its
    `gelfandTransform` coincide. Therefore, so do their spectral radii, and since they are
    self-adjoint, so also do their norms. Applying the C⋆-property of the norm and taking square
    roots shows that the norm is preserved. -/
  have : spectralRadius Complex (gelfandTransform Complex A (star a * a)) = spectralRadius Complex (star a * a) := by
    unfold spectralRadius; rw [spectrum.gelfandTransform_eq]
  rw [map_mul]; rw [(IsSelfAdjoint.star_mul_self a).spectralRadius_eq_nnnorm]; rw [gelfandTransform_map_star]; rw [(IsSelfAdjoint.star_mul_self (gelfandTransform Complex A a)).spectralRadius_eq_nnnorm] at this
  simp only [ENNReal.coe_inj, CStarRing.nnnorm_star_mul_self, ← sq] at this
  simpa only [Function.comp_apply, NNReal.sqrt_sq] using!
    congr_arg (((↑) : Real>=0 -> Real) ∘ ⇑NNReal.sqrt) this

set_option backward.defeqAttrib.useBackward true in
/--
theorem `gelfandTransform_bijective` / 定理 `gelfandTransform_bijective`

English:
theorem gelfandTransform_bijective
  statement: Function.Bijective (gelfandTransform Complex A)
  proof: by
  refine ⟨(gelfandTransform_isometry A).injective, ?_⟩
  /- The range of `gelfandTransform ℂ A` is actually a `StarSubalgebra`. The key lemma below may be
    hard to spot; it's `map_star` coming from `WeakDual.Complex.instStarHomClass`, which is a
    nontrivial result. -/
  let rng : StarSubalg

中文:
定理 gelfandTransform_bijective
  结论: Function.Bijective (gelfandTransform Complex A)
  证明: by
  refine ⟨(gelfandTransform_isometry A).injective, ?_⟩
  /- The range of `gelfandTransform ℂ A` is actually a `StarSubalgebra`. The key lemma below may be
    hard to spot; it's `map_star` coming from `WeakDual.Complex.instStarHomClass`, which is a
    nontrivial result. -/
  let rng : StarSubalg

Depends on / 依赖: gelfandTransform_isometry, injective
-/
theorem gelfandTransform_bijective : Function.Bijective (gelfandTransform Complex A) := by
  refine ⟨(gelfandTransform_isometry A).injective, ?_⟩
  /- The range of `gelfandTransform ℂ A` is actually a `StarSubalgebra`. The key lemma below may be
    hard to spot; it's `map_star` coming from `WeakDual.Complex.instStarHomClass`, which is a
    nontrivial result. -/
  let rng : StarSubalgebra Complex C(characterSpace Complex A, Complex) :=
    { toSubalgebra := (gelfandTransform Complex A).range
      star_mem' := by
        rintro - ⟨a, rfl⟩
        use star a
        ext1 φ
        dsimp
        simp only [map_star, RCLike.star_def] }
  suffices rng = ⊤ from
    fun x => show x in rng from this.symm ▸ StarSubalgebra.mem_top
  /- Because the `gelfandTransform ℂ A` is an isometry, it has closed range, and so by the
    Stone-Weierstrass theorem, it suffices to show that the image of the Gelfand transform separates
    points in `C(characterSpace ℂ A, ℂ)` and is closed under `star`. -/
  have h : rng.topologicalClosure = rng := le_antisymm
    (StarSubalgebra.topologicalClosure_minimal le_rfl
      (gelfandTransform_isometry A).isClosedEmbedding.isClosed_range)
    (StarSubalgebra.le_topologicalClosure _)
  refine h ▸ ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    _ (fun _ _ => ?_)
  /- Separating points just means that elements of the `characterSpace` which agree at all points
    of `A` are the same functional, which is just extensionality. -/
  contrapose!
  exact fun h => Subtype.ext (ContinuousLinearMap.ext fun a =>
    h (gelfandTransform Complex A a) ⟨gelfandTransform Complex A a, ⟨a, rfl⟩, rfl⟩)

/-- The Gelfand transform as a `StarAlgEquiv` between a commutative unital C⋆-algebra over `ℂ`
and the continuous functions on its `characterSpace`. -/
@[simps!]
/--
Definition of `gelfandStarTransform` / `gelfandStarTransform` 的定义

English:
definition gelfandStarTransform
  signature: : A ≃⋆ₐ[Complex] C(characterSpace Complex A, Complex)
  body: StarAlgEquiv.ofBijective
    (show A ->⋆ₐ[Complex] C(characterSpace Complex A, Complex) from
      { gelfandTransform Complex A with map_star' := fun x => gelfandTransform_map_star x })
    (gelfandTransform_bijective A)

中文:
定义 gelfandStarTransform
  签名: : A ≃⋆ₐ[Complex] C(characterSpace Complex A, Complex)
  定义体: StarAlgEquiv.ofBijective
    (show A ->⋆ₐ[Complex] C(characterSpace Complex A, Complex) from
      { gelfandTransform Complex A with map_star' := fun x => gelfandTransform_map_star x })
    (gelfandTransform_bijective A)

Depends on / 依赖: StarAlgEquiv, StarAlgEquiv.ofBijective, characterSpace, gelfandTransform, gelfandTransform_bijective, gelfandTransform_map_star, map_star, ofBijective
-/
noncomputable def gelfandStarTransform : A ≃⋆ₐ[Complex] C(characterSpace Complex A, Complex) :=
  StarAlgEquiv.ofBijective
    (show A ->⋆ₐ[Complex] C(characterSpace Complex A, Complex) from
      { gelfandTransform Complex A with map_star' := fun x => gelfandTransform_map_star x })
    (gelfandTransform_bijective A)

end Commutative

namespace CommCStarAlgebra

variable {A : Type*} [NonUnitalCommCStarAlgebra A] {a b : A}

open scoped CStarAlgebra in
open Unitization in
/--
lemma `norm_add_eq_max` / 引理 `norm_add_eq_max`

English:
lemma norm_add_eq_max
  given: (h : a * b = 0)
  statement: ‖a + b‖ = max ‖a‖ ‖b‖
  proof: by
  let f := gelfandStarTransform A⁺¹ ∘ inrNonUnitalAlgHom Complex A
.comp isometry_inr have hf : Isometry f := gelfandTransform_isometry _
  simp_rw [← hf.norm_map_of_map_zero (by simp [f]), show f (a + b) = f a + f b by simp [f]]
exact ContinuousMap.norm_add_eq_max by simpa [f] using congr(f $h)

中文:
引理 norm_add_eq_max
  条件: (h : a * b = 0)
  结论: ‖a + b‖ = max ‖a‖ ‖b‖
  证明: by
  let f := gelfandStarTransform A⁺¹ ∘ inrNonUnitalAlgHom Complex A
.comp isometry_inr have hf : Isometry f := gelfandTransform_isometry _
  simp_rw [← hf.norm_map_of_map_zero (by simp [f]), show f (a + b) = f a + f b by simp [f]]
exact ContinuousMap.norm_add_eq_max by simpa [f] using congr(f $h)

Depends on / 依赖: ContinuousMap, ContinuousMap.norm_add_eq_max, Isometry, gelfandStarTransform, gelfandTransform_isometry, hf.norm_map_of_map_zero, inrNonUnitalAlgHom, isometry_inr, norm_add_eq_max, norm_map_of_map_zero, simp_rw
-/
lemma norm_add_eq_max (h : a * b = 0) : ‖a + b‖ = max ‖a‖ ‖b‖ := by
  let f := gelfandStarTransform A⁺¹ ∘ inrNonUnitalAlgHom Complex A
.comp isometry_inr have hf : Isometry f := gelfandTransform_isometry _
  simp_rw [← hf.norm_map_of_map_zero (by simp [f]), show f (a + b) = f a + f b by simp [f]]
exact ContinuousMap.norm_add_eq_max by simpa [f] using congr(f $h)

/--
lemma `nnnorm_add_eq_max` / 引理 `nnnorm_add_eq_max`

English:
lemma nnnorm_add_eq_max
  given: (h : a * b = 0)
  statement: ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊
  proof: NNReal.eq norm_add_eq_max h

中文:
引理 nnnorm_add_eq_max
  条件: (h : a * b = 0)
  结论: ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊
  证明: NNReal.eq norm_add_eq_max h

Depends on / 依赖: NNReal, NNReal.eq, norm_add_eq_max
-/
lemma nnnorm_add_eq_max (h : a * b = 0) : ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊ :=
NNReal.eq norm_add_eq_max h

/--
lemma `norm_sub_eq_max` / 引理 `norm_sub_eq_max`

English:
lemma norm_sub_eq_max
  given: (h : a * b = 0)
  statement: ‖a - b‖ = max ‖a‖ ‖b‖
  proof: by
  simpa [sub_eq_add_neg] using norm_add_eq_max (a := a) (b := -b) (by simpa)

中文:
引理 norm_sub_eq_max
  条件: (h : a * b = 0)
  结论: ‖a - b‖ = max ‖a‖ ‖b‖
  证明: by
  simpa [sub_eq_add_neg] using norm_add_eq_max (a := a) (b := -b) (by simpa)

Depends on / 依赖: norm_add_eq_max, sub_eq_add_neg
-/
lemma norm_sub_eq_max (h : a * b = 0) : ‖a - b‖ = max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using norm_add_eq_max (a := a) (b := -b) (by simpa)

/--
lemma `nnnorm_sub_eq_max` / 引理 `nnnorm_sub_eq_max`

English:
lemma nnnorm_sub_eq_max
  given: (h : a * b = 0)
  statement: ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊
  proof: NNReal.eq norm_sub_eq_max h

中文:
引理 nnnorm_sub_eq_max
  条件: (h : a * b = 0)
  结论: ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊
  证明: NNReal.eq norm_sub_eq_max h

Depends on / 依赖: NNReal, NNReal.eq, norm_sub_eq_max
-/
lemma nnnorm_sub_eq_max (h : a * b = 0) : ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊ :=
NNReal.eq norm_sub_eq_max h

open scoped Function in
/--
lemma `nnnorm_sum_eq_sup` / 引理 `nnnorm_sum_eq_sup`

English:
lemma nnnorm_sum_eq_sup
  given: {ι : Type*} {f : ι -> A} (s : Finset ι) (h0 : Pairwise ((· * · = 0) on f))
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by simp_all [nnnorm_add_eq_max this]
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h0 (by grind)

中文:
引理 nnnorm_sum_eq_sup
  条件: {ι : 类型} {f : ι -> A} (s : Finset ι) (h0 : Pairwise ((· * · = 0) on f))
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by simp_all [nnnorm_add_eq_max this]
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h0 (by grind)

Depends on / 依赖: Finset, Finset.induction, Finset.mul_sum, Finset.sum_eq_zero, classical, insert, mul_sum, nnnorm_add_eq_max, sum_eq_zero
-/
lemma nnnorm_sum_eq_sup {ι : Type*} {f : ι -> A} (s : Finset ι) (h0 : Pairwise ((· * · = 0) on f)) :
    ‖∑ i in s, f i‖₊ = s.sup (‖f ·‖₊) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by simp_all [nnnorm_add_eq_max this]
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h0 (by grind)

end CommCStarAlgebra

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] {a b : A}

namespace IsStarNormal

open scoped IsMulCommutative in
open NonUnitalStarAlgebra NonUnitalStarSubalgebra in
/--
lemma `norm_add_eq_max` / 引理 `norm_add_eq_max`

English:
lemma norm_add_eq_max
  statement: (ha : IsStarNormal a) (hb : IsStarNormal b)
  proof: by
  /- Since `a` and `b` are normal, commute, and commute with the `star` of the other,
  the C⋆-subalgebra generated by `a` and `b` is commutative, and the conclusion follows from the
  corresponding result for commutative C⋆-algebras. -/
  -- TODO: once #36418 is merged, it should be possible to 

中文:
引理 norm_add_eq_max
  结论: (ha : IsStarNormal a) (hb : IsStarNormal b)
  证明: by
  /- Since `a` and `b` are normal, commute, and commute with the `star` of the other,
  the C⋆-subalgebra generated by `a` and `b` is commutative, and the conclusion follows from the
  corresponding result for commutative C⋆-algebras. -/
  -- TODO: once #36418 is merged, it should be possible to 
-/
lemma norm_add_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b)
    (hcomm : Commute a b) (hab : a * b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ := by
  /- Since `a` and `b` are normal, commute, and commute with the `star` of the other,
  the C⋆-subalgebra generated by `a` and `b` is commutative, and the conclusion follows from the
  corresponding result for commutative C⋆-algebras. -/
  -- TODO: once #36418 is merged, it should be possible to remove the `let _`s below entirely.
  let S : NonUnitalStarSubalgebra Complex A := (adjoin Complex {a, b}).topologicalClosure
  have hS : IsClosed (S : Set A) := (adjoin Complex {a, b}).isClosed_topologicalClosure
  have hcomm₁ := ha.commute_star_left hcomm
  have hcomm₂ := hb.commute_star_right hcomm
  have : IsMulCommutative (adjoin Complex {a, b}) :=
    isMulCommutative_adjoin Complex (by grind) (by grind [commute_star_comm])
  let _ : NonUnitalCommRing S := (adjoin Complex {a, b}).nonUnitalCommRingTopologicalClosure mul_comm
  let _ : NonUnitalCommCStarAlgebra S := { }
  refine CommCStarAlgebra.norm_add_eq_max (A := S) (a := ⟨a, ?_⟩) (b := ⟨b, ?_⟩) (by ext; simpa)
  all_goals apply le_topologicalClosure; aesop

/--
lemma `nnnorm_add_eq_max` / 引理 `nnnorm_add_eq_max`

English:
lemma nnnorm_add_eq_max
  statement: (ha : IsStarNormal a) (hb : IsStarNormal b)
  proof: NNReal.eq ha.norm_add_eq_max hb hcomm hab

中文:
引理 nnnorm_add_eq_max
  结论: (ha : IsStarNormal a) (hb : IsStarNormal b)
  证明: NNReal.eq ha.norm_add_eq_max hb hcomm hab

Depends on / 依赖: NNReal, NNReal.eq, ha.norm_add_eq_max, norm_add_eq_max
-/
lemma nnnorm_add_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b)
    (hcomm : Commute a b) (hab : a * b = 0) :
    ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊ :=
NNReal.eq ha.norm_add_eq_max hb hcomm hab

/--
lemma `norm_sub_eq_max` / 引理 `norm_sub_eq_max`

English:
lemma norm_sub_eq_max
  statement: (ha : IsStarNormal a) (hb : IsStarNormal b)
  proof: by
  simpa [sub_eq_add_neg] using
    ha.norm_add_eq_max hb.neg hcomm.neg_right (by simpa)

中文:
引理 norm_sub_eq_max
  结论: (ha : IsStarNormal a) (hb : IsStarNormal b)
  证明: by
  simpa [sub_eq_add_neg] using
    ha.norm_add_eq_max hb.neg hcomm.neg_right (by simpa)

Depends on / 依赖: ha.norm_add_eq_max, hb.neg, hcomm.neg_right, neg_right, norm_add_eq_max, sub_eq_add_neg
-/
lemma norm_sub_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b)
    (hcomm : Commute a b) (hab : a * b = 0) :
    ‖a - b‖ = max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using
    ha.norm_add_eq_max hb.neg hcomm.neg_right (by simpa)

/--
lemma `nnnorm_sub_eq_max` / 引理 `nnnorm_sub_eq_max`

English:
lemma nnnorm_sub_eq_max
  statement: (ha : IsStarNormal a) (hb : IsStarNormal b)
  proof: NNReal.eq ha.norm_sub_eq_max hb hcomm hab

中文:
引理 nnnorm_sub_eq_max
  结论: (ha : IsStarNormal a) (hb : IsStarNormal b)
  证明: NNReal.eq ha.norm_sub_eq_max hb hcomm hab

Depends on / 依赖: NNReal, NNReal.eq, ha.norm_sub_eq_max, norm_sub_eq_max
-/
lemma nnnorm_sub_eq_max (ha : IsStarNormal a) (hb : IsStarNormal b)
    (hcomm : Commute a b) (hab : a * b = 0) :
    ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊ :=
NNReal.eq ha.norm_sub_eq_max hb hcomm hab

end IsStarNormal

namespace IsSelfAdjoint

open NonUnitalStarAlgebra in
/--
lemma `norm_add_eq_max` / 引理 `norm_add_eq_max`

English:
lemma norm_add_eq_max
  given: (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0)
  proof: ha.isStarNormal.norm_add_eq_max hb.isStarNormal (by grind [commute_of_mul_eq_zero]) hab

中文:
引理 norm_add_eq_max
  条件: (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0)
  证明: ha.isStarNormal.norm_add_eq_max hb.isStarNormal (by grind [commute_of_mul_eq_zero]) hab

Depends on / 依赖: commute_of_mul_eq_zero, ha.isStarNormal.norm_add_eq_max, hb.isStarNormal, isStarNormal, norm_add_eq_max
-/
lemma norm_add_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) :
    ‖a + b‖ = max ‖a‖ ‖b‖ :=
  ha.isStarNormal.norm_add_eq_max hb.isStarNormal (by grind [commute_of_mul_eq_zero]) hab

/--
lemma `nnnorm_add_eq_max` / 引理 `nnnorm_add_eq_max`

English:
lemma nnnorm_add_eq_max
  given: (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0)
  proof: NNReal.eq ha.norm_add_eq_max hb hab

中文:
引理 nnnorm_add_eq_max
  条件: (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0)
  证明: NNReal.eq ha.norm_add_eq_max hb hab

Depends on / 依赖: NNReal, NNReal.eq, ha.norm_add_eq_max, norm_add_eq_max
-/
lemma nnnorm_add_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) :
    ‖a + b‖₊ = max ‖a‖₊ ‖b‖₊ :=
NNReal.eq ha.norm_add_eq_max hb hab

/--
lemma `norm_sub_eq_max` / 引理 `norm_sub_eq_max`

English:
lemma norm_sub_eq_max
  given: (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0)
  proof: by
  simpa [sub_eq_add_neg] using ha.norm_add_eq_max hb.neg (by simpa)

中文:
引理 norm_sub_eq_max
  条件: (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0)
  证明: by
  simpa [sub_eq_add_neg] using ha.norm_add_eq_max hb.neg (by simpa)

Depends on / 依赖: ha.norm_add_eq_max, hb.neg, norm_add_eq_max, sub_eq_add_neg
-/
lemma norm_sub_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) :
    ‖a - b‖ = max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using ha.norm_add_eq_max hb.neg (by simpa)

/--
lemma `nnnorm_sub_eq_max` / 引理 `nnnorm_sub_eq_max`

English:
lemma nnnorm_sub_eq_max
  given: (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0)
  proof: NNReal.eq ha.norm_sub_eq_max hb hab

中文:
引理 nnnorm_sub_eq_max
  条件: (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0)
  证明: NNReal.eq ha.norm_sub_eq_max hb hab

Depends on / 依赖: NNReal, NNReal.eq, ha.norm_sub_eq_max, norm_sub_eq_max
-/
lemma nnnorm_sub_eq_max (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b) (hab : a * b = 0) :
    ‖a - b‖₊ = max ‖a‖₊ ‖b‖₊ :=
NNReal.eq ha.norm_sub_eq_max hb hab

open scoped Function in
/--
lemma `nnnorm_sum_eq_sup` / 引理 `nnnorm_sum_eq_sup`

English:
lemma nnnorm_sum_eq_sup
  statement: {ι : Type*} {f : ι -> A} (s : Finset ι)
  proof: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by
      simp_all [(h j (by simp)).nnnorm_add_eq_max (by cfc_tac) this]
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h0 (by grind)

中文:
引理 nnnorm_sum_eq_sup
  结论: {ι : 类型} {f : ι -> A} (s : Finset ι)
  证明: by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by
      simp_all [(h j (by simp)).nnnorm_add_eq_max (by cfc_tac) this]
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h0 (by grind)

Depends on / 依赖: Finset, Finset.induction, Finset.mul_sum, Finset.sum_eq_zero, cfc_tac, classical, insert, mul_sum, nnnorm_add_eq_max, sum_eq_zero
-/
lemma nnnorm_sum_eq_sup {ι : Type*} {f : ι -> A} (s : Finset ι)
    (h : forall i in s, IsSelfAdjoint (f i)) (h0 : Pairwise ((· * · = 0) on f)) :
    ‖∑ i in s, f i‖₊ = s.sup (‖f ·‖₊) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    suffices f j * ∑ i in s, f i = 0 by
      simp_all [(h j (by simp)).nnnorm_add_eq_max (by cfc_tac) this]
    simpa [Finset.mul_sum] using Finset.sum_eq_zero fun i hi => h0 (by grind)

end IsSelfAdjoint

end NonUnital

end ComplexCStarAlgebra

section Functoriality

namespace WeakDual

namespace CharacterSpace

variable {A B C 𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A] [StarRing A]
variable [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B] [StarRing B]
variable [NormedRing C] [NormedAlgebra 𝕜 C] [CompleteSpace C] [StarRing C]

/-- The functorial map taking `ψ : A →⋆ₐ[ℂ] B` to a continuous function
`characterSpace ℂ B → characterSpace ℂ A` obtained by pre-composition with `ψ`. -/
@[simps]
/--
Definition of `compContinuousMap` / `compContinuousMap` 的定义

English:
definition compContinuousMap
  signature: (ψ : A ->⋆ₐ[𝕜] B)
  body: equivAlgHom.symm ((equivAlgHom φ).comp ψ.toAlgHom)
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_of_continuous_eval fun a => map_continuous <| gelfandTransform 𝕜 B (ψ a)) _

中文:
定义 compContinuousMap
  签名: (ψ : A ->⋆ₐ[𝕜] B)
  定义体: equivAlgHom.symm ((equivAlgHom φ).comp ψ.toAlgHom)
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_of_continuous_eval fun a => map_continuous <| gelfandTransform 𝕜 B (ψ a)) _

Depends on / 依赖: equivAlgHom, equivAlgHom.symm, toAlgHom
-/
noncomputable def compContinuousMap (ψ : A ->⋆ₐ[𝕜] B) :
    C(characterSpace 𝕜 B, characterSpace 𝕜 A) where
  toFun φ := equivAlgHom.symm ((equivAlgHom φ).comp ψ.toAlgHom)
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_of_continuous_eval fun a => map_continuous <| gelfandTransform 𝕜 B (ψ a)) _

variable (A) in
/-- `WeakDual.CharacterSpace.compContinuousMap` sends the identity to the identity. -/
@[simp]
/--
theorem `compContinuousMap_id` / 定理 `compContinuousMap_id`

English:
theorem compContinuousMap_id
  proof: ContinuousMap.ext fun _a => ext fun _x => rfl

中文:
定理 compContinuousMap_id
  证明: ContinuousMap.ext fun _a => ext fun _x => rfl

Depends on / 依赖: ContinuousMap, ContinuousMap.ext
-/
theorem compContinuousMap_id :
    compContinuousMap (StarAlgHom.id 𝕜 A) = ContinuousMap.id (characterSpace 𝕜 A) :=
  ContinuousMap.ext fun _a => ext fun _x => rfl

/-- `WeakDual.CharacterSpace.compContinuousMap` is functorial. -/
@[simp]
/--
theorem `compContinuousMap_comp` / 定理 `compContinuousMap_comp`

English:
theorem compContinuousMap_comp
  given: (ψ₂ : B ->⋆ₐ[𝕜] C) (ψ₁ : A ->⋆ₐ[𝕜] B)
  proof: ContinuousMap.ext fun _a => ext fun _x => rfl

中文:
定理 compContinuousMap_comp
  条件: (ψ₂ : B ->⋆ₐ[𝕜] C) (ψ₁ : A ->⋆ₐ[𝕜] B)
  证明: ContinuousMap.ext fun _a => ext fun _x => rfl

Depends on / 依赖: ContinuousMap, ContinuousMap.ext
-/
theorem compContinuousMap_comp (ψ₂ : B ->⋆ₐ[𝕜] C) (ψ₁ : A ->⋆ₐ[𝕜] B) :
    compContinuousMap (ψ₂.comp ψ₁) = (compContinuousMap ψ₁).comp (compContinuousMap ψ₂) :=
  ContinuousMap.ext fun _a => ext fun _x => rfl

end CharacterSpace

end WeakDual

end Functoriality

open CharacterSpace in
/--
theorem `gelfandStarTransform_naturality` / 定理 `gelfandStarTransform_naturality`

English:
theorem gelfandStarTransform_naturality
  statement: {A B : Type*} [CommCStarAlgebra A] [CommCStarAlgebra B]
  proof: by
  rfl

中文:
定理 gelfandStarTransform_naturality
  结论: {A B : 类型} [CommCStarAlgebra A] [CommCStarAlgebra B]
  证明: by
  rfl
-/
theorem gelfandStarTransform_naturality {A B : Type*} [CommCStarAlgebra A] [CommCStarAlgebra B]
    (φ : A ->⋆ₐ[Complex] B) :
    (gelfandStarTransform B : _ ->⋆ₐ[Complex] _).comp φ =
      (compContinuousMap φ |>.compStarAlgHom' Complex Complex).comp (gelfandStarTransform A : _ ->⋆ₐ[Complex] _) := by
  rfl

/--
lemma `WeakDual.CharacterSpace.homeoEval_naturality` / 引理 `WeakDual.CharacterSpace.homeoEval_naturality`

English:
lemma WeakDual.CharacterSpace.homeoEval_naturality
  statement: {X Y 𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace X]
  proof: rfl

中文:
引理 WeakDual.CharacterSpace.homeoEval_naturality
  结论: {X Y 𝕜 : 类型} [RCLike 𝕜] [TopologicalSpace X]
  证明: rfl
-/
lemma WeakDual.CharacterSpace.homeoEval_naturality {X Y 𝕜 : Type*} [RCLike 𝕜] [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (f : C(X, Y)) :
    (homeoEval Y 𝕜 : C(_, _)).comp f =
      (f.compStarAlgHom' 𝕜 𝕜 |> compContinuousMap).comp (homeoEval X 𝕜 : C(_, _)) :=
  rfl
