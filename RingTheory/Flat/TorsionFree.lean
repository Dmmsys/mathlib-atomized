/-
Copyright (c) 2025 Matthew Jasper. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Jasper, Kevin Buzzard
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.Ideal.IsPrincipal

/-!
# Relationships between flatness and torsionfreeness.

We show that flat implies torsion-free, and that they're the same
concept for rings satisfying a certain property, including Dedekind
domains and valuation rings.

## Main theorems

* `Module.Flat.isSMulRegular_of_nonZeroDivisors`: Scalar multiplication by a nonzerodivisor of `R`
  is injective on a flat `R`-module.
* `Module.Flat.torsion_eq_bot`: `Torsion R M = ⊥` if `M` is a flat `R`-module.
* `Module.Flat.flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal`: if localizing `R`
  at the complement of any maximal ideal is a valuation ring then `Torsion R M = ⊥` iff `M` is a
  flat `R`-module.
-/

public section
-- TODO: Add definition and properties of Prüfer domains.
-- TODO: Use `IsTorsionFree`.

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open Submodule (IsPrincipal torsion)

open TensorProduct

namespace Module.Flat

section Semiring

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

open LinearMap in
/--
lemma `isSMulRegular_of_isRegular` / 引理 `isSMulRegular_of_isRegular`

English:
lemma isSMulRegular_of_isRegular
  given: {r : R} (hr : IsRegular r) [Flat R M]
  proof: by
  -- `r ∈ R⁰` implies that `toSpanSingleton R R r`, i.e. `(r * ⬝) : R → R` is injective
  -- Flatness implies that corresponding map `R ⊗[R] M →ₗ[R] R ⊗[R] M` is injective
  have h := Flat.rTensor_preserves_injective_linearMap (M := M)
(toSpanSingleton R R r) hr.right
  -- But precomposing and postcomposing with the isomorphism `M ≃ₗ[R] (R ⊗[R] M)`
  -- we get a map `M →ₗ[R] M` which is just `(r • ·)`.
  have h2 : (fun (x : M) => r • x) = ((TensorProduct.lid R M) ∘ₗ
            (rTensor M (toSpanSingleton R R r)) ∘ₗ
            (TensorProduct.lid R M).symm) := by ext; simp
  -- Hence `(r • ·) : M → M` is also injective
  rw [IsSMulRegular]; rw [h2]
  simp [h, LinearEquiv.injective]

中文:
引理 isSMulRegular_of_isRegular
  条件: {r : R} (hr : 是正则 r) [平坦 R M]
  证明: by
  -- `r ∈ R⁰` implies that `toSpanSingleton R R r`, i.e. `(r * ⬝) : R → R` is injective
  -- Flatness implies that corresponding map `R ⊗[R] M →ₗ[R] R ⊗[R] M` is injective
  have h := Flat.rTensor_preserves_injective_linearMap (M := M)
(toSpanSingleton R R r) hr.right
  -- But precomposing and postcomposing with the isomorphism `M ≃ₗ[R] (R ⊗[R] M)`
  -- we get a map `M →ₗ[R] M` which is just `(r • ·)`.
  have h2 : (fun (x : M) => r • x) = ((TensorProduct.lid R M) ∘ₗ
            (rTensor M (toSpanSingleton R R r)) ∘ₗ
            (TensorProduct.lid R M).symm) := by ext; simp
  -- Hence `(r • ·) : M → M` is also injective
  rw [IsSMulRegular]; rw [h2]
  simp [h, LinearEquiv.injective]
-/
lemma isSMulRegular_of_isRegular {r : R} (hr : IsRegular r) [Flat R M] :
    IsSMulRegular M r := by
  -- `r ∈ R⁰` implies that `toSpanSingleton R R r`, i.e. `(r * ⬝) : R → R` is injective
  -- Flatness implies that corresponding map `R ⊗[R] M →ₗ[R] R ⊗[R] M` is injective
  have h := Flat.rTensor_preserves_injective_linearMap (M := M)
(toSpanSingleton R R r) hr.right
  -- But precomposing and postcomposing with the isomorphism `M ≃ₗ[R] (R ⊗[R] M)`
  -- we get a map `M →ₗ[R] M` which is just `(r • ·)`.
  have h2 : (fun (x : M) => r • x) = ((TensorProduct.lid R M) ∘ₗ
            (rTensor M (toSpanSingleton R R r)) ∘ₗ
            (TensorProduct.lid R M).symm) := by ext; simp
  -- Hence `(r • ·) : M → M` is also injective
  rw [IsSMulRegular]; rw [h2]
  simp [h, LinearEquiv.injective]

/--
Instance `isTorsionFree` / 实例 `isTorsionFree`

English:
instance isTorsionFree
  signature: [Flat R M]
  body: ⟨fun _ hr => isSMulRegular_of_isRegular hr⟩

中文:
实例 isTorsionFree
  签名: [平坦 R M]
  定义体: ⟨fun _ hr => isSMulRegular_of_isRegular hr⟩

Depends on / 依赖: isSMulRegular_of_isRegular
-/
instance isTorsionFree [Flat R M] : IsTorsionFree R M :=
  ⟨fun _ hr => isSMulRegular_of_isRegular hr⟩

end Semiring

section Ring

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open scoped nonZeroDivisors

open LinearMap in
/--
lemma `isSMulRegular_of_nonZeroDivisors` / 引理 `isSMulRegular_of_nonZeroDivisors`

English:
lemma isSMulRegular_of_nonZeroDivisors
  given: {r : R} (hr : r in R⁰) [Flat R M]
  statement: IsSMulRegular M r
  proof: by
  apply isSMulRegular_of_isRegular
  exact le_nonZeroDivisors_iff_isRegular.mp (le_refl R⁰) ⟨r, hr⟩

中文:
引理 isSMulRegular_of_nonZeroDivisors
  条件: {r : R} (hr : r in R⁰) [平坦 R M]
  结论: IsSMulRegular M r
  证明: by
  apply isSMulRegular_of_isRegular
  exact le_nonZeroDivisors_iff_isRegular.mp (le_refl R⁰) ⟨r, hr⟩

Depends on / 依赖: isSMulRegular_of_isRegular, le_nonZeroDivisors_iff_isRegular, le_nonZeroDivisors_iff_isRegular.mp, le_refl
-/
lemma isSMulRegular_of_nonZeroDivisors {r : R} (hr : r in R⁰) [Flat R M] : IsSMulRegular M r := by
  apply isSMulRegular_of_isRegular
  exact le_nonZeroDivisors_iff_isRegular.mp (le_refl R⁰) ⟨r, hr⟩

/--
theorem `torsion_eq_bot` / 定理 `torsion_eq_bot`

English:
theorem torsion_eq_bot
  given: [Flat R M]
  statement: torsion R M = ⊥
  proof: by
  rw [eq_bot_iff]
  -- indeed the definition of torsion means "annihilated by a nonzerodivisor"
  rintro m ⟨⟨r, hr⟩, h⟩
  -- and we just showed that 0 is the only element with this property
  exact isSMulRegular_of_nonZeroDivisors hr (by simpa using h)

中文:
定理 torsion_eq_bot
  条件: [平坦 R M]
  结论: torsion R M = ⊥
  证明: by
  rw [eq_bot_iff]
  -- indeed the definition of torsion means "annihilated by a nonzerodivisor"
  rintro m ⟨⟨r, hr⟩, h⟩
  -- and we just showed that 0 is the only element with this property
  exact isSMulRegular_of_nonZeroDivisors hr (by simpa using h)

Depends on / 依赖: eq_bot_iff
-/
theorem torsion_eq_bot [Flat R M] : torsion R M = ⊥ := by
  rw [eq_bot_iff]
  -- indeed the definition of torsion means "annihilated by a nonzerodivisor"
  rintro m ⟨⟨r, hr⟩, h⟩
  -- and we just showed that 0 is the only element with this property
  exact isSMulRegular_of_nonZeroDivisors hr (by simpa using h)

/-- If `R` is Bezout then an `R`-module is flat iff it has no torsion. -/
@[stacks 0539 "Generalized valuation ring to Bezout domain"]
/--
theorem `flat_iff_torsion_eq_bot_of_isBezout` / 定理 `flat_iff_torsion_eq_bot_of_isBezout`

English:
theorem flat_iff_torsion_eq_bot_of_isBezout
  given: [IsBezout R] [IsDomain R]
  proof: by
  -- one way is true in general
  refine ⟨fun _ => torsion_eq_bot, ?_⟩
  -- now assume R is a Bezout domain and M is a torsionfree R-module
  intro htors
  -- we need to show that if I is an ideal of R then the natural map I ⊗ M → M is injective
  rw [iff_lift_lsmul_comp_subtype_injective]
  rintro I hFG
  -- If I = 0 this is obvious because I ⊗ M is a subsingleton (i.e. has ≤1 element)
  obtain (rfl | h) := eq_or_ne I ⊥
  · rintro x y -
    apply Subsingleton.elim
  · -- If I ≠ 0 then I ≅ R because R is Bezout and I is finitely generated
    have hprinc : I.IsPrincipal := IsBezout.isPrincipal_of_FG I hFG
    have : IsPrincipal.generator I != 0 := by
      rwa [ne_eq, ← IsPrincipal.eq_bot_iff_generator_eq_zero]
    apply Function.Injective.of_comp_right _
      (LinearEquiv.rTensor M (Ideal.isoBaseOfIsPrincipal h)).surjective
    rw [← LinearEquiv.coe_toLinearMap]; rw [← LinearMap.coe_comp]; rw [LinearEquiv.coe_rTensor]; rw [rTensor]; rw [lift_comp_map]; rw [LinearMap.compl₂_id]; rw [LinearMap.comp_assoc]; rw [Ideal.subtype_isoBaseOfIsPrincipal_eq_mul]; rw [LinearMap.lift_lsmul_mul_eq_lsmul_lift_lsmul]; rw [LinearMap.coe_comp]
    rw [← Submodule.isTorsionFree_iff_torsion_eq_bot] at htors
    refine Function.Injective.comp (LinearMap.lsmul_injective this) ?_
    rw [← Equiv.injective_comp (TensorProduct.lid R M).symm.toEquiv]
    convert! Function.injective_id
    ext
    simp

中文:
定理 flat_iff_torsion_eq_bot_of_isBezout
  条件: [是Bezout R] [是整环 R]
  证明: by
  -- one way is true in general
  refine ⟨fun _ => torsion_eq_bot, ?_⟩
  -- now assume R is a Bezout domain and M is a torsionfree R-module
  intro htors
  -- we need to show that if I is an ideal of R then the natural map I ⊗ M → M is injective
  rw [iff_lift_lsmul_comp_subtype_injective]
  rintro I hFG
  -- If I = 0 this is obvious because I ⊗ M is a subsingleton (i.e. has ≤1 element)
  obtain (rfl | h) := eq_or_ne I ⊥
  · rintro x y -
    apply Subsingleton.elim
  · -- If I ≠ 0 then I ≅ R because R is Bezout and I is finitely generated
    have hprinc : I.IsPrincipal := IsBezout.isPrincipal_of_FG I hFG
    have : IsPrincipal.generator I != 0 := by
      rwa [ne_eq, ← IsPrincipal.eq_bot_iff_generator_eq_zero]
    apply Function.Injective.of_comp_right _
      (LinearEquiv.rTensor M (Ideal.isoBaseOfIsPrincipal h)).surjective
    rw [← LinearEquiv.coe_toLinearMap]; rw [← LinearMap.coe_comp]; rw [LinearEquiv.coe_rTensor]; rw [rTensor]; rw [lift_comp_map]; rw [LinearMap.compl₂_id]; rw [LinearMap.comp_assoc]; rw [Ideal.subtype_isoBaseOfIsPrincipal_eq_mul]; rw [LinearMap.lift_lsmul_mul_eq_lsmul_lift_lsmul]; rw [LinearMap.coe_comp]
    rw [← Submodule.isTorsionFree_iff_torsion_eq_bot] at htors
    refine Function.Injective.comp (LinearMap.lsmul_injective this) ?_
    rw [← Equiv.injective_comp (TensorProduct.lid R M).symm.toEquiv]
    convert! Function.injective_id
    ext
    simp
-/
theorem flat_iff_torsion_eq_bot_of_isBezout [IsBezout R] [IsDomain R] :
    Flat R M ↔ torsion R M = ⊥ := by
  -- one way is true in general
  refine ⟨fun _ => torsion_eq_bot, ?_⟩
  -- now assume R is a Bezout domain and M is a torsionfree R-module
  intro htors
  -- we need to show that if I is an ideal of R then the natural map I ⊗ M → M is injective
  rw [iff_lift_lsmul_comp_subtype_injective]
  rintro I hFG
  -- If I = 0 this is obvious because I ⊗ M is a subsingleton (i.e. has ≤1 element)
  obtain (rfl | h) := eq_or_ne I ⊥
  · rintro x y -
    apply Subsingleton.elim
  · -- If I ≠ 0 then I ≅ R because R is Bezout and I is finitely generated
    have hprinc : I.IsPrincipal := IsBezout.isPrincipal_of_FG I hFG
    have : IsPrincipal.generator I != 0 := by
      rwa [ne_eq, ← IsPrincipal.eq_bot_iff_generator_eq_zero]
    apply Function.Injective.of_comp_right _
      (LinearEquiv.rTensor M (Ideal.isoBaseOfIsPrincipal h)).surjective
    rw [← LinearEquiv.coe_toLinearMap]; rw [← LinearMap.coe_comp]; rw [LinearEquiv.coe_rTensor]; rw [rTensor]; rw [lift_comp_map]; rw [LinearMap.compl₂_id]; rw [LinearMap.comp_assoc]; rw [Ideal.subtype_isoBaseOfIsPrincipal_eq_mul]; rw [LinearMap.lift_lsmul_mul_eq_lsmul_lift_lsmul]; rw [LinearMap.coe_comp]
    rw [← Submodule.isTorsionFree_iff_torsion_eq_bot] at htors
    refine Function.Injective.comp (LinearMap.lsmul_injective this) ?_
    rw [← Equiv.injective_comp (TensorProduct.lid R M).symm.toEquiv]
    convert! Function.injective_id
    ext
    simp

/--
theorem `flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal` / 定理 `flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal`

English:
theorem flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
  statement: [IsDomain R]
  proof: by
  refine ⟨fun _ => Flat.torsion_eq_bot, fun h => ?_⟩
  apply flat_of_localized_maximal
  intro P hP
  rw [← Submodule.isTorsionFree_iff_torsion_eq_bot] at h
  rw [← flat_iff_of_isLocalization (Localization P.primeCompl) P.primeCompl]; rw [Flat.flat_iff_torsion_eq_bot_of_isBezout]; rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

中文:
定理 flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
  结论: [是整环 R]
  证明: by
  refine ⟨fun _ => Flat.torsion_eq_bot, fun h => ?_⟩
  apply flat_of_localized_maximal
  intro P hP
  rw [← Submodule.isTorsionFree_iff_torsion_eq_bot] at h
  rw [← flat_iff_of_isLocalization (Localization P.primeCompl) P.primeCompl]; rw [Flat.flat_iff_torsion_eq_bot_of_isBezout]; rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

Depends on / 依赖: Flat.flat_iff_torsion_eq_bot_of_isBezout, Flat.torsion_eq_bot, Localization, P.primeCompl, Submodule, Submodule.isTorsionFree_iff_torsion_eq_bot, flat_iff_of_isLocalization, flat_iff_torsion_eq_bot_of_isBezout, flat_of_localized_maximal, infer_instance, isTorsionFree_iff_torsion_eq_bot, primeCompl, torsion_eq_bot
-/
theorem flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal [IsDomain R]
    (h : forall (P : Ideal R), [P.IsMaximal] -> ValuationRing (Localization P.primeCompl)) :
    Flat R M ↔ torsion R M = ⊥ := by
  refine ⟨fun _ => Flat.torsion_eq_bot, fun h => ?_⟩
  apply flat_of_localized_maximal
  intro P hP
  rw [← Submodule.isTorsionFree_iff_torsion_eq_bot] at h
  rw [← flat_iff_of_isLocalization (Localization P.primeCompl) P.primeCompl]; rw [Flat.flat_iff_torsion_eq_bot_of_isBezout]; rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

/-- If `R` is a Dedekind domain then an `R`-module is flat iff it has no torsion. -/
@[stacks 0AUW "(1)"]
/--
theorem `_root_.IsDedekindDomain.flat_iff_torsion_eq_bot` / 定理 `_root_.IsDedekindDomain.flat_iff_torsion_eq_bot`

English:
theorem _root_.IsDedekindDomain.flat_iff_torsion_eq_bot
  given: [IsDedekindDomain R]
  proof: by
  apply flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
  exact fun P => inferInstance

中文:
定理 _root_.是Dedekind整环.flat_iff_torsion_eq_bot
  条件: [是Dedekind整环 R]
  证明: by
  apply flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
  exact fun P => inferInstance

Depends on / 依赖: flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
-/
theorem _root_.IsDedekindDomain.flat_iff_torsion_eq_bot [IsDedekindDomain R] :
    Flat R M ↔ torsion R M = ⊥ := by
  apply flat_iff_torsion_eq_bot_of_valuationRing_localization_isMaximal
  exact fun P => inferInstance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsDedekindDomain
  signature: R] [IsTorsionFree R M] : Flat R M
  body: by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot]; rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

中文:
实例 [是Dedekind整环
  签名: R] [是无挠 R M] : 平坦 R M
  定义体: by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot]; rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

Depends on / 依赖: IsDedekindDomain, IsDedekindDomain.flat_iff_torsion_eq_bot, Submodule, Submodule.isTorsionFree_iff_torsion_eq_bot, flat_iff_torsion_eq_bot, infer_instance, isTorsionFree_iff_torsion_eq_bot
-/
instance [IsDedekindDomain R] [IsTorsionFree R M] : Flat R M := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot]; rw [← Submodule.isTorsionFree_iff_torsion_eq_bot]
  infer_instance

end Ring

end Module.Flat
