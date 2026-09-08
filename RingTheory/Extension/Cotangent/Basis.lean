/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Extension.Cotangent.LocalizationAway

/-!
# Basis of cotangent space can be realized as a presentation

Let `S` be a finitely presented `R`-algebra and suppose `P : R[X] → S` generates `S` with
kernel `I`.

In this file we show `Algebra.Generators.exists_presentation_of_free`: If `I/I²` is free, there
exists an `R`-presentation `P'` of `S` extending `P` with kernel `I'`, such that `I'/I'²` is
free on the images of the relations of `P'`.

## References

- https://stacks.math.columbia.edu/tag/07CF
-/

open scoped Pointwise
open MvPolynomial TensorProduct

namespace Algebra.Generators

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] {σ : Type*}

noncomputable section

namespace PresentationOfFreeCotangent

variable {ι : Type*} (P : Generators R S ι) {σ : Type*}
  (b : Module.Basis σ S P.toExtension.Cotangent)

/-- An auxiliary structure containing the data to construct the presentation in
`Generators.exists_presentation_of_free`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux** 是 Mathlib 中的一个结构，位于命名空间 `
Algebra.Generators.PresentationOfFreeCotangent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary structure containing the data to construct the presentation in
`Generators.exists_presentation_of_free`.
-/
structure Aux where
  /-- A section of the projection `I → I/I²`. -/
  f : P.toExtension.Cotangent → P.toExtension.ker
  hf : ∀ (b : P.toExtension.Cotangent), Extension.Cotangent.mk (f b) = b
  /-- An element `g` that becomes invertible in `S = R[X₁, ..., Xₙ] / I`. -/
  g : P.Ring
  hgmem : g - 1 ∈ P.ker
  hg : g • P.ker ≤ Ideal.span (Set.range <| Subtype.val ∘ f ∘ b)

namespace Aux

variable {P} {b}
variable (D : Aux P b)

/-- `T = R[X₁, ..., Xₙ] / (b₁, ..., bᵣ)` where the `bᵢ` are lifts of the basis elements
of `I/I²` in `I`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.T** 是 Mathlib 中的一个缩写定义，位于命名
空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：T
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`T = R[X₁, ..., Xₙ] / (b₁, ..., bᵣ)` where the `bᵢ` are lifts of the basis eleme
nts
of `I/I²` in `I`.
-/
abbrev T :=
  MvPolynomial ι R ⧸ (Ideal.span <| Set.range <| Subtype.val ∘ D.f ∘ b)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The map `R[X₁, ..., Xₙ] → S` factors via `T`, because the `bᵢ` are in `I`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.hom** 是 Mathlib 中的一个定义，位于命名
空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：hom : D.T ->ₐ[R] S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `R[X₁, ..., Xₙ] → S` factors via `T`, because the `bᵢ` are in `I`.
-/
def hom : D.T →ₐ[R] S := Ideal.Quotient.liftₐ _ (aeval P.val) <| by
  simp_rw [← RingHom.mem_ker, ← SetLike.le_def, Ideal.span_le, Set.range_subset_iff]
  intro i
  simpa only [Generators.toExtension_Ring, Generators.toExtension_commRing, Function.comp_apply,
    SetLike.mem_coe, RingHom.mem_ker, ← P.algebraMap_apply] using (D.f _).property
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.** 是 Mathlib 中的一个实例，位于命名空间 
`Algebra.Generators.PresentationOfFreeCotangent.Aux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra D.T S := D.hom.toAlgebra
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.** 是 Mathlib 中的一个实例，位于命名空间 
`Algebra.Generators.PresentationOfFreeCotangent.Aux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial S] : Nontrivial D.T := RingHom.domain_nontrivial (algebraMap D.T S)

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.** 是 Mathlib 中的一个实例，位于命名空间 
`Algebra.Generators.PresentationOfFreeCotangent.Aux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower P.Ring D.T S := by
  refine ⟨fun x y z ↦ ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, rfl⟩ := P.algebraMap_surjective z
  simp only [Algebra.smul_def, map_mul, Generators.algebraMap_apply, ← mul_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The image of `g : R[X₁, ..., Xₙ]` in `T`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.gbar** 是 Mathlib 中的一个缩写定义，位
于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：gbar : D.T
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `g : R[X₁, ..., Xₙ]` in `T`.
-/
abbrev gbar : D.T := D.g

set_option backward.isDefEq.respectTransparency false in
/-- `S` is the localization of `T` away from `S`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.** 是 Mathlib 中的一个实例，位于命名空间 
`Algebra.Generators.PresentationOfFreeCotangent.Aux`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`S` is the localization of `T` away from `S`.
-/
instance : IsLocalization.Away D.gbar S := by
  refine .of_surjective_of_isScalarTower (n := 1) ?_ ?_ _ ?_ (by simpa using! D.hg)
  · refine .of_comp (g := algebraMap P.Ring D.T) ?_
    convert! P.algebraMap_surjective
    ext x
    exact (IsScalarTower.algebraMap_apply _ D.T S x).symm
  · simp [T, Ideal.Quotient.mk_surjective]
  · suffices h : (algebraMap P.Ring S) D.g = 1 by simp [h]
    rw [← map_one (algebraMap P.Ring S), ← sub_eq_zero, ← map_sub, ← RingHom.mem_ker]
    exact D.hgmem

open scoped Classical in
/-- The "naive" presentation of `T = R[X₁, ..., Xₙ] / (b₁, ..., bᵣ)` over `R`.
We make sure the section `T → R[X₁, ..., Xₙ]` maps `-1` to `-1` and `0` to `0`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.presLeft** 是 Mathlib 中的一个定义
，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：presLeft : Presentation R D.T ι σ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "naive" presentation of `T = R[X₁, ..., Xₙ] / (b₁, ..., bᵣ)` over `R`.
We make sure the section `T → R[X₁, ..., Xₙ]` maps `-1` to `-1` and `0` to `0`.
-/
def presLeft : Presentation R D.T ι σ :=
  .naive (fun x ↦ if x = 0 then 0 else if x = -1 then -1 else
      Function.surjInv Ideal.Quotient.mk_surjective x) fun x ↦ by
    split_ifs
    · next h => subst h; rfl
    · next h => subst h; rfl
    · simp [Function.surjInv_eq]

/-- The `i`-th generator of the kernel `(b₁, ..., bᵣ)` of the naive presentation of `T`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.kerGen** 是 Mathlib 中的一个定义，位
于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：kerGen (i : σ) : D.presLeft.toExtension.ker
参数：i : σ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th generator of the kernel `(b₁, ..., bᵣ)` of the naive presentation of 
`T`.
-/
def kerGen (i : σ) : D.presLeft.toExtension.ker :=
  ⟨(D.f (b i)).val, Presentation.mem_ker_naive _ _ i⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The identity on `R[X₁, ..., Xₙ]` as a map of presentations of `T` to `S`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.fhom** 是 Mathlib 中的一个定义，位于命
名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：fhom : D.presLeft.Hom P where val i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity on `R[X₁, ..., Xₙ]` as a map of presentations of `T` to `S`.
-/
def fhom : D.presLeft.Hom P where
  val i := X i
  aeval_val i := by simp [RingHom.algebraMap_toAlgebra, presLeft, hom, T]

@[simp]
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.toAlgHom_fhom** 是 Mathlib 中
的一个引理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：toAlgHom_fhom : D.fhom.toAlgHom = AlgHom.id R P.Ring
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAlgHom_fhom : D.fhom.toAlgHom = AlgHom.id R P.Ring := by
  ext : 1
  simp [fhom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.ker_presLeft_le** 是 Mathlib
 中的一个引理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：ker_presLeft_le : D.presLeft.ker <= P.ker
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ker_presLeft_le : D.presLeft.ker ≤ P.ker := by
  intro x hx
  simpa only [toExtension_commRing, toExtension_Ring, RingHom.mem_ker,
    toExtension_algebra₂, algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    map_zero] using! (algebraMap D.T S).congr_arg hx

set_option backward.isDefEq.respectTransparency.types false in
/-- The forward direction of the isomorphism `S ⊗[T] J/J² ≃ₗ[S] I/I²`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentHom** 是 Math
lib 中的一个定义，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：tensorCotangentHom : S otimes[D.T] D.presLeft.toExtension.Cotangent ->ₗ[S]
 P.toExtension.Cotangent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forward direction of the isomorphism `S ⊗[T] J/J² ≃ₗ[S] I/I²`.
-/
def tensorCotangentHom : S ⊗[D.T] D.presLeft.toExtension.Cotangent →ₗ[S] P.toExtension.Cotangent :=
  LinearMap.liftBaseChange _ (Extension.Cotangent.map D.fhom.toExtensionHom)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentHom_tmul** 是
 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：tensorCotangentHom_tmul (x : D.presLeft.toExtension.ker) : D.tensorCotange
ntHom (1 otimesₜ[D.T] Extension.Cotangent.mk x) = .mk ⟨x.val, D.ker_presLeft_le 
x.2⟩
参数：x : D.presLeft.toExtension.ker。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorCotangentHom_tmul (x : D.presLeft.toExtension.ker) :
    D.tensorCotangentHom (1 ⊗ₜ[D.T] Extension.Cotangent.mk x) =
      .mk ⟨x.val, D.ker_presLeft_le x.2⟩ := by
  simp_rw +instances [tensorCotangentHom, LinearMap.liftBaseChange_tmul, one_smul, presLeft,
    Extension.Cotangent.map_mk, Extension.Hom.toAlgHom_apply, Hom.toExtensionHom_toRingHom,
    toAlgHom_fhom, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, toExtension_Ring,
    toExtension_commRing, toExtension_algebra₂, Presentation.naive_toGenerators, RingHom.id_apply]

/-- The backwards direction of the isomorphism `S ⊗[T] J/J² ≃ₗ[S] I/I²`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentInv** 是 Math
lib 中的一个定义，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：tensorCotangentInv : P.toExtension.Cotangent ->ₗ[S] S otimes[D.T] D.presLe
ft.toExtension.Cotangent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The backwards direction of the isomorphism `S ⊗[T] J/J² ≃ₗ[S] I/I²`.
-/
def tensorCotangentInv : P.toExtension.Cotangent →ₗ[S] S ⊗[D.T] D.presLeft.toExtension.Cotangent :=
  b.constr S fun i : σ ↦ 1 ⊗ₜ Extension.Cotangent.mk (D.kerGen i)

@[simp]
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentInv_apply** 
是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：tensorCotangentInv_apply (i : σ) : D.tensorCotangentInv (b i) = 1 otimesₜ 
Extension.Cotangent.mk (D.kerGen i)
参数：i : σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorCotangentInv_apply (i : σ) :
    D.tensorCotangentInv (b i) = 1 ⊗ₜ Extension.Cotangent.mk (D.kerGen i) :=
  Module.Basis.constr_basis _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.span_range_mk_kerGen** 是 Ma
thlib 中的一个引理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：span_range_mk_kerGen : Submodule.span D.T (Set.range fun i => Extension.Co
tangent.mk (D.kerGen i)) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma span_range_mk_kerGen : Submodule.span D.T
    (Set.range fun i ↦ Extension.Cotangent.mk (D.kerGen i)) = ⊤ := by
  refine Extension.Cotangent.span_eq_top_of_span_eq_ker _ ?_
  dsimp only [presLeft, Presentation.naive_toGenerators]
  exact (Generators.ker_naive _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-- The linear isomorphism `S ⊗[T] J/J² ≃ₗ[S] I/I²`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentEquiv** 是 Ma
thlib 中的一个定义，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：tensorCotangentEquiv : S otimes[D.T] D.presLeft.toExtension.Cotangent ≃ₗ[S
] P.toExtension.Cotangent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear isomorphism `S ⊗[T] J/J² ≃ₗ[S] I/I²`.
-/
def tensorCotangentEquiv :
    S ⊗[D.T] D.presLeft.toExtension.Cotangent ≃ₗ[S] P.toExtension.Cotangent := by
  refine LinearEquiv.ofLinearMap D.tensorCotangentHom D.tensorCotangentInv ?_ ?_
  · refine b.ext fun i ↦ ?_
    simpa only [LinearMap.coe_comp, Function.comp_apply, tensorCotangentInv_apply,
      tensorCotangentHom_tmul] using! D.hf (b i)
  · ext : 2
    refine LinearMap.ext_on_range D.span_range_mk_kerGen fun i ↦ ?_
    simp [-toExtension_commRing, -toExtension_Ring, -toExtension_algebra₂, tensorCotangentHom_tmul,
      kerGen, D.hf]

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.tensorCotangentEquiv_symm_a
pply** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.A
ux`。
形式化陈述：tensorCotangentEquiv_symm_apply (i : σ) : D.tensorCotangentEquiv.symm (b i
) = 1 otimesₜ Extension.Cotangent.mk (D.kerGen i)
参数：i : σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorCotangentEquiv_symm_apply (i : σ) :
    D.tensorCotangentEquiv.symm (b i) = 1 ⊗ₜ Extension.Cotangent.mk (D.kerGen i) :=
  D.tensorCotangentInv_apply i

set_option backward.isDefEq.respectTransparency false in
/-- The canonical presentation of `S` as the localization of `T` away from `g`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.presRight** 是 Mathlib 中的一个定
义，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：presRight : Presentation D.T S Unit Unit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical presentation of `S` as the localization of `T` away from `g`.
-/
def presRight : Presentation D.T S Unit Unit :=
  Presentation.localizationAway S D.gbar

set_option backward.isDefEq.respectTransparency false in
/-- The presentation of `S` over `R` obtained from composing the naive presentation of
`T = R[X₁, ..., Xₙ]/(b₁, ..., bᵣ)` with the presentation of the localization away from `g`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.pres** 是 Mathlib 中的一个定义，位于命
名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：pres : Presentation R S (Unit oplus ι) (Unit oplus σ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presentation of `S` over `R` obtained from composing the naive presentation 
of
`T = R[X₁, ..., Xₙ]/(b₁, ..., bᵣ)` with the presentation of the localization awa
y from `g`.
-/
def pres : Presentation R S (Unit ⊕ ι) (Unit ⊕ σ) :=
  D.presRight.comp D.presLeft

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.map_ofComp_mk** 是 Mathlib 中
的一个引理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：map_ofComp_mk [Nontrivial S] : (Extension.Cotangent.map ((localizationAway
 S D.gbar).ofComp D.presLeft.toGenerators).toExtensionHom) (Extension.Cotangent.
mk ⟨D.pres.relation (Sum.inl ()), D.pres.relation_mem_ker _⟩) = Generators.cMulX
SubOneCotangent S D.gbar
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_ofComp_mk [Nontrivial S] :
    (Extension.Cotangent.map
      ((localizationAway S D.gbar).ofComp D.presLeft.toGenerators).toExtensionHom)
      (Extension.Cotangent.mk ⟨D.pres.relation (Sum.inl ()), D.pres.relation_mem_ker _⟩) =
      Generators.cMulXSubOneCotangent S D.gbar := by
  simp_rw [Extension.Cotangent.map_mk, Generators.Hom.toExtensionHom_toAlgHom_apply]
  congr 2
  have : Nontrivial D.T := inferInstance
  dsimp only [T, Generators.toExtension_Ring, Generators.toExtension_commRing] at this
  rw [pres, presLeft, presRight, Presentation.relation_comp_localizationAway_inl]
  · exact Generators.toAlgHom_ofComp_localizationAway _ _
  · rw [Presentation.naive, Generators.naive_σ];
    simp
  · rw [Presentation.naive, Generators.naive_σ]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The cotangent space of the constructed presentation is isomorphic
to `(g X - 1)/(g X - 1)² × S ⊗[T] J/J²`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.cotangentEquivProd** 是 Math
lib 中的一个定义，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：cotangentEquivProd [Nontrivial S] : D.pres.toExtension.Cotangent ≃ₗ[S] D.p
resRight.toExtension.Cotangent × S otimes[D.T] D.presLeft.toExtension.Cotangent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cotangent space of the constructed presentation is isomorphic
to `(g X - 1)/(g X - 1)² × S ⊗[T] J/J²`.
-/
def cotangentEquivProd [Nontrivial S] : D.pres.toExtension.Cotangent ≃ₗ[S]
    D.presRight.toExtension.Cotangent × S ⊗[D.T] D.presLeft.toExtension.Cotangent :=
  (D.presLeft.cotangentCompLocalizationAwayEquiv (T := S) D.gbar D.map_ofComp_mk) ≪≫ₗ
    LinearEquiv.prodComm _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.cotangentEquivProd_symm_app
ly** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux
`。
形式化陈述：cotangentEquivProd_symm_apply [Nontrivial S] (x : D.presRight.toExtension.
Cotangent) (y : S otimes[D.T] D.presLeft.toExtension.Cotangent) : D.cotangentEqu
ivProd.symm (x, y) = (D.presLeft.cotangentCompLocalizationAwayEquiv (T
参数：x : D.presRight.toExtension.Cotangent；y : S otimes[D.T] D.presLeft.toExtensio
n.Cotangent。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma cotangentEquivProd_symm_apply [Nontrivial S] (x : D.presRight.toExtension.Cotangent)
      (y : S ⊗[D.T] D.presLeft.toExtension.Cotangent) :
    D.cotangentEquivProd.symm (x, y) =
      (D.presLeft.cotangentCompLocalizationAwayEquiv (T := S) D.gbar D.map_ofComp_mk).symm (y, x) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The basis of `S ⊗[T] J/J²` induced from the basis on `I/I²`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.basisLeft** 是 Mathlib 中的一个定
义，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：basisLeft : Module.Basis σ S (S otimes[D.T] D.presLeft.toExtension.Cotange
nt)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis of `S ⊗[T] J/J²` induced from the basis on `I/I²`.
-/
def basisLeft : Module.Basis σ S (S ⊗[D.T] D.presLeft.toExtension.Cotangent) :=
  b.map D.tensorCotangentEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/-- The canonical basis on `(g X - 1)/(g X - 1)²`. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.basisRight** 是 Mathlib 中的一个
定义，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：basisRight : Module.Basis Unit S D.presRight.toExtension.Cotangent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical basis on `(g X - 1)/(g X - 1)²`.
-/
def basisRight : Module.Basis Unit S D.presRight.toExtension.Cotangent :=
  Generators.basisCotangentAway S D.gbar

set_option backward.isDefEq.respectTransparency.types false in
/-- The basis on the cotangent space of the constructed presentation. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.basis** 是 Mathlib 中的一个定义，位于
命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：basis [Nontrivial S] : Module.Basis (Unit oplus σ) S D.pres.toExtension.Co
tangent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basis on the cotangent space of the constructed presentation.
-/
def basis [Nontrivial S] : Module.Basis (Unit ⊕ σ) S D.pres.toExtension.Cotangent :=
  (Module.Basis.prod D.basisRight D.basisLeft).map D.cotangentEquivProd.symm

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.basis_inl** 是 Mathlib 中的一个引
理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：basis_inl [Nontrivial S] : D.basis (.inl ()) = D.cotangentEquivProd.symm (
Generators.cMulXSubOneCotangent S D.gbar, 0)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma basis_inl [Nontrivial S] :
    D.basis (.inl ()) =
      D.cotangentEquivProd.symm (Generators.cMulXSubOneCotangent S D.gbar, 0) := by
  simpa [basis] using! Generators.basisCotangentAway_apply _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.basis_inr** 是 Mathlib 中的一个引
理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：basis_inr [Nontrivial S] (i : σ) : D.basis (.inr i) = D.cotangentEquivProd
.symm (0, D.basisLeft i)
参数：i : σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma basis_inr [Nontrivial S] (i : σ) :
    D.basis (.inr i) = D.cotangentEquivProd.symm (0, D.basisLeft i) := by
  simp [basis]
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.pres_val_comp_inr** 是 Mathl
ib 中的一个引理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：pres_val_comp_inr : D.pres.val ∘ Sum.inr = P.val
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pres_val_comp_inr : D.pres.val ∘ Sum.inr = P.val := funext (aeval_X _)

set_option backward.isDefEq.respectTransparency false in
/-- The constructed basis indeed is given by the images of the relations. -/
/-
**Algebra.Generators.PresentationOfFreeCotangent.Aux.basis_apply** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.Generators.PresentationOfFreeCotangent.Aux`。
形式化陈述：basis_apply [Nontrivial S] (r : Unit oplus σ) : D.basis r = Extension.Cota
ngent.mk ⟨D.pres.relation r, D.pres.relation_mem_ker r⟩
参数：r : Unit oplus σ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructed basis indeed is given by the images of the relations.
-/
lemma basis_apply [Nontrivial S] (r : Unit ⊕ σ) :
    D.basis r = Extension.Cotangent.mk ⟨D.pres.relation r, D.pres.relation_mem_ker r⟩ := by
  obtain (r | r) := r
  · rw [basis_inl, cotangentEquivProd_symm_apply]
    exact cotangentCompLocalizationAwayEquiv_symm_inr _ _ _
  · rw [basis_inr, cotangentEquivProd_symm_apply, cotangentCompLocalizationAwayEquiv_symm_inl,
      basisLeft, Module.Basis.map_apply, tensorCotangentEquiv_symm_apply,
      LinearMap.liftBaseChange_tmul, one_smul, Extension.Cotangent.map_mk]
    simp only [Extension.Hom.toAlgHom_apply, Hom.toExtensionHom_toRingHom, AlgHom.toRingHom_eq_coe]
    congr! 2 with x
    simp [pres, Presentation.comp_relation_inr, kerGen, presLeft, Generators.toComp_toAlgHom]
    rfl

end PresentationOfFreeCotangent.Aux

end

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open PresentationOfFreeCotangent in
/--
Version of `Algebra.Generators.exists_presentation_of_free_cotangent` taking a basis instead
of a `Module.Free` assumption.
Note that the basis `b₀` only serves as a way of saying
that `I/I²` is free of rank `σ`, which gives more definitional control over `σ`.
If this does not matter, use `Algebra.Generators.exists_presentation_of_free_cotangent` instead.
-/
@[stacks 07CF]
public lemma exists_presentation_of_basis_cotangent [Algebra.FinitePresentation R S]
    {α : Type*} (P : Generators R S α) [Finite α] {σ : Type*}
    (b₀ : Module.Basis σ S P.toExtension.Cotangent) :
    ∃ (P' : Presentation R S (Unit ⊕ α) (Unit ⊕ σ))
      (b : Module.Basis (Unit ⊕ σ) S P'.toExtension.Cotangent),
      P'.val ∘ Sum.inr = P.val ∧
      ∀ r, b r = Extension.Cotangent.mk ⟨P'.relation r, P'.relation_mem_ker r⟩ := by
  cases subsingleton_or_nontrivial S
  · let P' : Presentation R S (Unit ⊕ α) (Unit ⊕ σ) :=
      { toGenerators := .ofSurjective (fun i : Unit ⊕ α ↦ 0) (Function.surjective_to_subsingleton _)
        relation _ := 1
        span_range_relation_eq_ker := by simpa using (RingHom.ker_eq_top_of_subsingleton _).symm }
    have : Subsingleton P'.toExtension.Cotangent := Module.subsingleton S _
    exact ⟨P', default, by subsingleton, by subsingleton⟩
  choose f hf using Extension.Cotangent.mk_surjective (P := P.toExtension)
  let v (i : σ) : P.ker := f (b₀ i)
  let J : Ideal P.Ring := Ideal.span (Set.range <| Subtype.val ∘ v)
  have hJfg : P.ker.FG := by
    rw [P.ker_eq_ker_aeval_val]
    apply FinitePresentation.ker_fG_of_surjective
    convert! P.algebraMap_surjective
    simp [P.algebraMap_eq]
  have hJ : J ≤ P.ker := by simp [J, Ideal.span_le, Set.range_subset_iff]
  suffices hJ : P.ker ≤ J ⊔ P.ker • P.ker by
    obtain ⟨g, hgmem, hg⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup hJfg le_rfl hJ
    let D : Aux P b₀ := { f := f, hf := hf, g := g, hgmem := hgmem, hg := hg }
    exact ⟨D.pres, D.basis, D.pres_val_comp_inr, D.basis_apply⟩
  rw [← Submodule.comap_le_comap_iff_of_le_range (f := P.ker.subtype) (by simp),
    Submodule.comap_subtype_self,
    Submodule.comap_sup_of_injective P.ker.subtype_injective (by simpa using hJ)
    (by simp [Ideal.mul_le_right]),
    Submodule.comap_smul'' P.ker.subtype_injective (by simp)]
  simp only [Submodule.comap_subtype_self, J]
  rw [← Submodule.coe_subtype, Ideal.span, Set.range_comp, ← Submodule.map_span,
    Submodule.comap_map_eq_of_injective P.ker.subtype_injective,
    ← Extension.Cotangent.ker_mk]
  dsimp
  simp only [← LinearMap.map_le_map_iff, Submodule.map_span, ← Set.range_comp,
    Function.comp_def, ← Submodule.restrictScalars_span P.Ring S P.algebraMap_surjective]
  refine le_trans le_top (top_le_iff.mpr ?_)
  rw [Submodule.restrictScalars_eq_top_iff]
  convert! b₀.span_eq
  exact hf _

open PresentationOfFreeCotangent in
/-- Let `S` be a finitely presented `R`-algebra and suppose `P : R[X] → S` generates `S` with
kernel `I`. If `I/I²` is free, there exists an `R`-presentation `P'` of `S` extending `P` with
kernel `I'`, such that `I'/I'²` is free on the images of the relations of `P'`.
See `Algebra.Generators.exists_presentation_of_basis_cotangent` for a version taking
a basis of `I/I²` instead. -/
@[stacks 07CF]
public lemma exists_presentation_of_free_cotangent [Algebra.FinitePresentation R S]
    {α : Type*} (P : Generators R S α) [Finite α]
    [Module.Free S P.toExtension.Cotangent] :
    ∃ (P' : Presentation R S (Unit ⊕ α) (Unit ⊕ Fin (Module.finrank S P.toExtension.Cotangent)))
      (b : Module.Basis (Unit ⊕ Fin (Module.finrank S P.toExtension.Cotangent))
        S P'.toExtension.Cotangent),
      P'.val ∘ Sum.inr = P.val ∧
      ∀ r, b r = Extension.Cotangent.mk ⟨P'.relation r, P'.relation_mem_ker r⟩ := by
  cases subsingleton_or_nontrivial S
  · let P' : Presentation R S (Unit ⊕ α) (Unit ⊕ Fin (Module.finrank S P.toExtension.Cotangent)) :=
      { toGenerators := .ofSurjective (fun i : Unit ⊕ α ↦ 0) (Function.surjective_to_subsingleton _)
        relation _ := 1
        span_range_relation_eq_ker := by simpa using! (RingHom.ker_eq_top_of_subsingleton _).symm }
    have : Subsingleton P'.toExtension.Cotangent := Module.subsingleton S _
    exact ⟨P', default, by subsingleton, by subsingleton⟩
  have : Module.Finite S P.toExtension.Cotangent :=
    Algebra.Extension.Cotangent.finite P.fg_ker_of_finitePresentation
  exact exists_presentation_of_basis_cotangent _ <| Module.finBasis S P.toExtension.Cotangent

end Algebra.Generators

