/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic

/-! # Continuous functional calculus

In this file we construct the `continuousFunctionalCalculus` for a normal element `a` of a
(unital) C⋆-algebra over `ℂ`. This is a star algebra equivalence
`C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental ℂ a` which sends the (restriction of) the
identity map `ContinuousMap.id ℂ` to the (unique) preimage of `a` under the coercion of
`elemental ℂ a` to `A`.

Being a star algebra equivalence between C⋆-algebras, this map is continuous (even an isometry),
and by the Stone-Weierstrass theorem it is the unique star algebra equivalence which extends the
polynomial functional calculus (i.e., `Polynomial.aeval`).

For any continuous function `f : spectrum ℂ a → ℂ`, this makes it possible to define an element
`f a` (not valid notation) in the original algebra, which heuristically has the same eigenspaces as
`a` and acts on eigenvector of `a` for an eigenvalue `λ` as multiplication by `f λ`. This
description is perfectly accurate in finite dimension, but only heuristic in infinite dimension as
there might be no genuine eigenvector. In particular, when `f` is a polynomial `∑ cᵢ Xⁱ`, then
`f a` is `∑ cᵢ aⁱ`. Also, `id a = a`.

The result we have established here is the strongest possible, but it is not the version which is
most useful in practice. The generic API for the continuous functional calculus can be found in
`Analysis.CStarAlgebra.ContinuousFunctionalCalculus` in the `Unital` and `NonUnital` files. The
relevant instances on C⋆-algebra can be found in the `Instances` file.

## Main definitions

* `continuousFunctionalCalculus : C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental ℂ a`: this
  is the composition of the inverse of the `gelfandStarTransform` with the natural isomorphism
  induced by the homeomorphism `elemental.characterSpaceHomeo`.
* `elemental.characterSpaceHomeo` :
  `characterSpace ℂ (elemental ℂ a) ≃ₜ spectrum ℂ a`: this homeomorphism is defined
  by evaluating a character `φ` at `a`, and noting that `φ a ∈ spectrum ℂ a` since `φ` is an
  algebra homomorphism. Moreover, this map is continuous and bijective and since the spaces involved
  are compact Hausdorff, it is a homeomorphism.
* `IsStarNormal.instContinuousFunctionalCalculus`: the continuous functional calculus for normal
  elements in a unital C⋆-algebra over `ℂ`.
* `CStarAlgebra.instNonnegSpectrumClass`: In a unital C⋆-algebra over `ℂ` which is also a
  `StarOrderedRing`, the spectrum of a nonnegative element is nonnegative.

-/

@[expose] public section


open scoped Pointwise ENNReal NNReal ComplexOrder CStarAlgebra

open WeakDual WeakDual.CharacterSpace

variable {A : Type*}

namespace StarAlgebra.elemental

variable [CStarAlgebra A]

/-
**StarAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgebra.elemental`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R A : Type*} [CommRing R] [StarRing R] [NormedRing A] [Algebra R A] [StarRing A]
    [ContinuousStar A] [StarModule R A] (a : A) [IsStarNormal a] :
    NormedCommRing (elemental R a) :=
  { SubringClass.toNormedRing (elemental R a) with
    mul_comm := mul_comm }
/-
**StarAlgebra.elemental.** 是 Mathlib 中的一个实例，位于命名空间 `StarAlgebra.elemental`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (a : A) [IsStarNormal a] : CommCStarAlgebra (elemental ℂ a) where

variable (a : A) [IsStarNormal a]

set_option backward.isDefEq.respectTransparency false in
/-- The natural map from `characterSpace ℂ (elemental ℂ x)` to `spectrum ℂ x` given
by evaluating `φ` at `x`. This is essentially just evaluation of the `gelfandTransform` of `x`,
but because we want something in `spectrum ℂ x`, as opposed to
`spectrum ℂ ⟨x, elemental.self_mem ℂ x⟩` there is slightly more work to do. -/
@[simps]
/-
**StarAlgebra.elemental.characterSpaceToSpectrum** 是 Mathlib 中的一个定义，位于命名空间 `Star
Algebra.elemental`。
形式化陈述：characterSpaceToSpectrum (x : A) (φ : characterSpace Complex (elemental Co
mplex x)) : spectrum Complex x where val
参数：x : A；φ : characterSpace Complex (elemental Complex x)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A

--- 原说明 ---
The natural map from `characterSpace ℂ (elemental ℂ x)` to `spectrum ℂ x` given
by evaluating `φ` at `x`. This is essentially just evaluation of the `gelfandTra
nsform` of `x`,
but because we want something in `spectrum ℂ x`, as opposed to
`spectrum ℂ ⟨x, elemental.self_mem ℂ x⟩` there is slightly more work to do.
-/
noncomputable def characterSpaceToSpectrum (x : A)
    (φ : characterSpace ℂ (elemental ℂ x)) : spectrum ℂ x where
  val := φ ⟨x, self_mem ℂ x⟩
  property := by
    simpa only [StarSubalgebra.spectrum_eq (hS := isClosed ℂ x)
      (a := ⟨x, self_mem ℂ x⟩)] using AlgHom.apply_mem_spectrum φ ⟨x, self_mem ℂ x⟩
/-
**StarAlgebra.elemental.continuous_characterSpaceToSpectrum** 是 Mathlib 中的一个定理，位
于命名空间 `StarAlgebra.elemental`。
形式化陈述：continuous_characterSpaceToSpectrum (x : A) : Continuous (characterSpaceTo
Spectrum x)
参数：x : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `continuous_induced_rng`：continuous_induced_rng {g : γ -> α} {t₂ : Topolo
gicalSpace β} {t₁ : TopologicalSpace γ} : Continuous[t₁, induced f t₂] g ↔ Conti
nuous[t₁, t₂…
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `StarAlgebra.elemental.self_mem`：self_mem (x : A) : x in elemental R x
-/
theorem continuous_characterSpaceToSpectrum (x : A) :
    Continuous (characterSpaceToSpectrum x) :=
  continuous_induced_rng.2
    (map_continuous <| gelfandTransform ℂ (elemental ℂ x) ⟨x, self_mem ℂ x⟩)

set_option backward.isDefEq.respectTransparency false in
/-
**StarAlgebra.elemental.bijective_characterSpaceToSpectrum** 是 Mathlib 中的一个定理，位于
命名空间 `StarAlgebra.elemental`。
形式化陈述：bijective_characterSpaceToSpectrum : Function.Bijective (characterSpaceToS
pectrum a)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `StarAlgebra.elemental.starAlgHomClass_ext`：starAlgHomClass_ext [T2Space 
B] {F : Type*} {a : A} [FunLike F (elemental R a) B] [AlgHomClass F R _ B] [Star
HomClass F _ B] {φ ψ : F} (hφ :…
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `StarAlgebra.elemental.self_mem`：self_mem (x : A) : x in elemental R x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `StarSubalgebra.spectrum_eq`：spectrum_eq {a : S} : spectrum Complex a = s
pectrum Complex (a : A)
· 使用定理 `StarAlgebra.elemental.isClosed`：isClosed (x : A) : IsClosed (elemental R
 x : Set A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeakDual.CharacterSpace.mem_spectrum_iff_exists`：WeakDual.CharacterSpace
.mem_spectrum_iff_exists {a : A} {z : Complex} : z in spectrum Complex a ↔ exist
s f : characterSpace Complex A, f a =…
· 使用定理 `StarAlgebra.elemental.instCompleteSpaceSubtypeMemStarSubalgebra`：∀ (R : 
Type u_1) [inst : CommSemiring R] [inst_1 : StarRing R] {A : Type u_4} [inst_2 :
 UniformSpace A]   [CompleteSpace A] [inst_4 : Semiri…
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
-/
theorem bijective_characterSpaceToSpectrum :
    Function.Bijective (characterSpaceToSpectrum a) := by
  refine ⟨fun φ ψ h => starAlgHomClass_ext ℂ ?_ ?_ ?_, ?_⟩
  · exact (map_continuous φ)
  · exact (map_continuous ψ)
  · simpa only [characterSpaceToSpectrum, Subtype.mk_eq_mk,
      ContinuousMap.coe_mk] using h
  · rintro ⟨z, hz⟩
    have hz' := (StarSubalgebra.spectrum_eq (hS := isClosed ℂ a)
      (a := ⟨a, self_mem ℂ a⟩) ▸ hz)
    rw [CharacterSpace.mem_spectrum_iff_exists] at hz'
    obtain ⟨φ, rfl⟩ := hz'
    exact ⟨φ, rfl⟩

/-- The homeomorphism between the character space of the unital C⋆-subalgebra generated by a
single normal element `a : A` and `spectrum ℂ a`. -/
/-
**StarAlgebra.elemental.characterSpaceHomeo** 是 Mathlib 中的一个定义，位于命名空间 `StarAlgeb
ra.elemental`。
形式化陈述：characterSpaceHomeo : characterSpace Complex (elemental Complex a) ≃ₜ spec
trum Complex a
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `StarAlgebra.elemental.bijective_characterSpaceToSpectrum`：bijective_char
acterSpaceToSpectrum : Function.Bijective (characterSpaceToSpectrum a)
· 使用定理 `StarAlgebra.elemental.continuous_characterSpaceToSpectrum`：continuous_ch
aracterSpaceToSpectrum (x : A) : Continuous (characterSpaceToSpectrum x)

--- 原说明 ---
The homeomorphism between the character space of the unital C⋆-subalgebra genera
ted by a
single normal element `a : A` and `spectrum ℂ a`.
-/
noncomputable def characterSpaceHomeo :
    characterSpace ℂ (elemental ℂ a) ≃ₜ spectrum ℂ a :=
  @Continuous.homeoOfEquivCompactToT2 _ _ _ _ _ _
    (Equiv.ofBijective (characterSpaceToSpectrum a)
      (bijective_characterSpaceToSpectrum a))
    (continuous_characterSpaceToSpectrum a)

end StarAlgebra.elemental

open StarAlgebra elemental


/-- **Continuous functional calculus.** Given a normal element `a : A` of a unital C⋆-algebra,
the continuous functional calculus is a `StarAlgEquiv` from the complex-valued continuous
functions on the spectrum of `a` to the unital C⋆-subalgebra generated by `a`. Moreover, this
equivalence identifies `(ContinuousMap.id ℂ).restrict (spectrum ℂ a))` with `a`; see
`continuousFunctionalCalculus_map_id`. As such it extends the polynomial functional calculus. -/
/-
**continuousFunctionalCalculus** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：continuousFunctionalCalculus [CStarAlgebra A] (a : A) [IsStarNormal a] : C
(spectrum Complex a, Complex) ≃⋆ₐ[Complex] elemental Complex a
参数：a : A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ

--- 原说明 ---
**Continuous functional calculus.** Given a normal element `a : A` of a unital C
⋆-algebra,
the continuous functional calculus is a `StarAlgEquiv` from the complex-valued c
ontinuous
functions on the spectrum of `a` to the unital C⋆-subalgebra generated by `a`. M
oreover, this
equivalence identifies `(ContinuousMap.id ℂ).restrict (spectrum ℂ a))` with `a`;
 see
`continuousFunctionalCalculus_map_id`. As such it extends the polynomial functio
nal calculus.
-/
noncomputable def continuousFunctionalCalculus [CStarAlgebra A] (a : A) [IsStarNormal a] :
    C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental ℂ a :=
  ((characterSpaceHomeo a).compStarAlgEquiv' ℂ ℂ).trans
    (gelfandStarTransform (elemental ℂ a)).symm
/-
**continuousFunctionalCalculus_map_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousFunctionalCalculus_map_id [CStarAlgebra A] (a : A) [IsStarNormal
 a] : continuousFunctionalCalculus a ((ContinuousMap.id Complex).restrict (spect
rum Complex a)) = ⟨a, self_mem Complex a⟩
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StarAlgEquiv.symm_apply_apply`：symm_apply_apply (e : A ≃⋆ₐ[R] B) : foral
l x, e.symm (e x) = x
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
-/
theorem continuousFunctionalCalculus_map_id [CStarAlgebra A] (a : A) [IsStarNormal a] :
    continuousFunctionalCalculus a ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) =
      ⟨a, self_mem ℂ a⟩ :=
  (gelfandStarTransform (elemental ℂ a)).symm_apply_apply _

/-!
### Continuous functional calculus for normal elements
-/

local notation "σₙ" => quasispectrum

section Normal

section Unital

variable [CStarAlgebra A]

/-
**IsStarNormal.instContinuousFunctionalCalculus** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStarNormal.instContinuousFunctionalCalculus : ContinuousFunctionalCalcul
us Complex A IsStarNormal where predicate_zero
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsStarNormal.zero`：∀ {R : Type u_1} [inst : NonUnitalNonAssocSemiring R]
 [inst_1 : StarAddMonoid R], IsStarNormal 0
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `spectrum.nonempty`：∀ {A : Type u_2} [inst : NormedRing A] [inst_1 : Norm
edAlgebra ℂ A] [CompleteSpace A] [Nontrivial A] (a : A),   (spectrum ℂ a).Nonemp
ty
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `instAlgEquivClassOfNonUnitalAlgEquivClass`：∀ (F : Type u_1) (R : Type u_
2) (A : Type u_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]  
 [inst_2 : Algebra R A] [inst_3…
· 使用定理 `StarAlgEquiv.instNonUnitalAlgEquivClass`：∀ {R : Type u_2} {A : Type u_3}
 {B : Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B
]   [inst_4 : SMul R A] [inst…
· 使用定理 `NonUnitalStarRingHomClass.toStarHomClass`：∀ {F : Type u_1} {A : outParam
 (Type u_2)} {B : outParam (Type u_3)} {inst : NonUnitalNonAssocSemiring A}   {i
nst_1 : Star A} {inst_2 : NonU…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `StarRingEquivClass.toRingEquivClass`：∀ {F : Type u_1} {A : outParam (Typ
e u_2)} {B : outParam (Type u_3)} {inst : Add A} {inst_1 : Mul A} {inst_2 : Star
 A}   {inst_3 : Add B} {i…
· 使用定理 `StarAlgEquiv.instStarRingEquivClass`：∀ {R : Type u_2} {A : Type u_3} {B 
: Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B]   
[inst_4 : SMul R A] [inst…
· 使用定理 `StarRingEquivClass.instNonUnitalStarRingHomClass`：∀ {F : Type u_1} {A : 
Type u_2} {B : Type u_3} [inst : NonUnitalNonAssocSemiring A] [inst_1 : Star A] 
  [inst_2 : NonUnitalNonAssocSemiring …
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用定理 `isometry_subtype_coe`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {s : 
Set α}, Isometry Subtype.val
（共 53 条，此处仅展示前 30 条）
-/
theorem IsStarNormal.instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℂ A IsStarNormal where
  predicate_zero := .zero
  spectrum_nonempty a _ := spectrum.nonempty a
  exists_cfc_of_predicate a ha := by
    have : Isometry ((StarAlgebra.elemental ℂ a).subtype.comp <| continuousFunctionalCalculus a :
        C(spectrum ℂ a, ℂ) →⋆ₐ[ℂ] A) :=
      isometry_subtype_coe.comp <| StarAlgEquiv.isometry (continuousFunctionalCalculus a)
    refine ⟨_, this.continuous, this.injective, ?hom_id, ?hom_map_spectrum, ?predicate_hom⟩
    case hom_id => exact congr_arg Subtype.val <| continuousFunctionalCalculus_map_id a
    case hom_map_spectrum =>
      intro f
      simp only [StarAlgHom.comp_apply, StarAlgHom.coe_coe, StarSubalgebra.coe_subtype]
      rw [← StarSubalgebra.spectrum_eq (hS := StarAlgebra.elemental.isClosed ℂ a),
        AlgEquiv.spectrum_eq (continuousFunctionalCalculus a), ContinuousMap.spectrum_eq_range]
    case predicate_hom => exact fun f ↦ ⟨by rw [← map_star]; exact Commute.all (star f) f |>.map _⟩

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus
/-
**cfcHom_eq_of_isStarNormal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：cfcHom_eq_of_isStarNormal (a : A) [ha : IsStarNormal a] : cfcHom ha = (Sta
rAlgebra.elemental Complex a).subtype.comp (continuousFunctionalCalculus a)
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfcHom_eq_of_continuous_of_map_id`：cfcHom_eq_of_continuous_of_map_id [Un
iqueHom R A] (φ : C(spectrum R a, R) ->⋆ₐ[R] A) (hφ₁ : Continuous φ) (hφ₂ : φ (.
restrict (spectrum R a)…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsStarNormal.instContinuousFunctionalCalculus`：IsStarNormal.instContinuo
usFunctionalCalculus : ContinuousFunctionalCalculus Complex A IsStarNormal where
 predicate_zero
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `instAlgEquivClassOfNonUnitalAlgEquivClass`：∀ (F : Type u_1) (R : Type u_
2) (A : Type u_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]  
 [inst_2 : Algebra R A] [inst_3…
· 使用定理 `StarAlgEquiv.instNonUnitalAlgEquivClass`：∀ {R : Type u_2} {A : Type u_3}
 {B : Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B
]   [inst_4 : SMul R A] [inst…
· 使用定理 `NonUnitalStarRingHomClass.toStarHomClass`：∀ {F : Type u_1} {A : outParam
 (Type u_2)} {B : outParam (Type u_3)} {inst : NonUnitalNonAssocSemiring A}   {i
nst_1 : Star A} {inst_2 : NonU…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `StarRingEquivClass.toRingEquivClass`：∀ {F : Type u_1} {A : outParam (Typ
e u_2)} {B : outParam (Type u_3)} {inst : Add A} {inst_1 : Mul A} {inst_2 : Star
 A}   {inst_3 : Add B} {i…
· 使用定理 `StarAlgEquiv.instStarRingEquivClass`：∀ {R : Type u_2} {A : Type u_3} {B 
: Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B]   
[inst_4 : SMul R A] [inst…
· 使用定理 `StarRingEquivClass.instNonUnitalStarRingHomClass`：∀ {F : Type u_1} {A : 
Type u_2} {B : Type u_3} [inst : NonUnitalNonAssocSemiring A] [inst_1 : Star A] 
  [inst_2 : NonUnitalNonAssocSemiring …
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Isometry.continuous`：∀ {α : Type u} {β : Type v} [inst : PseudoEMetricSp
ace α] [inst_1 : PseudoEMetricSpace β] {f : α → β},   Isometry f → Continuous f
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
（共 42 条，此处仅展示前 30 条）
-/
lemma cfcHom_eq_of_isStarNormal (a : A) [ha : IsStarNormal a] :
    cfcHom ha = (StarAlgebra.elemental ℂ a).subtype.comp (continuousFunctionalCalculus a) := by
  refine cfcHom_eq_of_continuous_of_map_id ha _ ?_ ?_
  · exact continuous_subtype_val.comp <|
      (StarAlgEquiv.isometry (continuousFunctionalCalculus a)).continuous
  · simp [continuousFunctionalCalculus_map_id a]
/-
**IsStarNormal.instIsometricContinuousFunctionalCalculus** 是 Mathlib 中的一个实例，位于命名
空间 ``。
形式化陈述：IsStarNormal.instIsometricContinuousFunctionalCalculus : IsometricContinuo
usFunctionalCalculus Complex A IsStarNormal where isometric a ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `IsStarNormal.instContinuousFunctionalCalculus`：IsStarNormal.instContinuo
usFunctionalCalculus : ContinuousFunctionalCalculus Complex A IsStarNormal where
 predicate_zero
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `instAlgEquivClassOfNonUnitalAlgEquivClass`：∀ (F : Type u_1) (R : Type u_
2) (A : Type u_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]  
 [inst_2 : Algebra R A] [inst_3…
· 使用定理 `StarAlgEquiv.instNonUnitalAlgEquivClass`：∀ {R : Type u_2} {A : Type u_3}
 {B : Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B
]   [inst_4 : SMul R A] [inst…
· 使用定理 `NonUnitalStarRingHomClass.toStarHomClass`：∀ {F : Type u_1} {A : outParam
 (Type u_2)} {B : outParam (Type u_3)} {inst : NonUnitalNonAssocSemiring A}   {i
nst_1 : Star A} {inst_2 : NonU…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `StarRingEquivClass.toRingEquivClass`：∀ {F : Type u_1} {A : outParam (Typ
e u_2)} {B : outParam (Type u_3)} {inst : Add A} {inst_1 : Mul A} {inst_2 : Star
 A}   {inst_3 : Add B} {i…
· 使用定理 `StarAlgEquiv.instStarRingEquivClass`：∀ {R : Type u_2} {A : Type u_3} {B 
: Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B]   
[inst_4 : SMul R A] [inst…
· 使用定理 `StarRingEquivClass.instNonUnitalStarRingHomClass`：∀ {F : Type u_1} {A : 
Type u_2} {B : Type u_3} [inst : NonUnitalNonAssocSemiring A] [inst_1 : Star A] 
  [inst_2 : NonUnitalNonAssocSemiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcHom_eq_of_isStarNormal`：cfcHom_eq_of_isStarNormal (a : A) [ha : IsSta
rNormal a] : cfcHom ha = (StarAlgebra.elemental Complex a).subtype.comp (continu
ousFunctionalCa…
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用定理 `isometry_subtype_coe`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {s : 
Set α}, Isometry Subtype.val
（共 36 条，此处仅展示前 30 条）
-/
instance IsStarNormal.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℂ A IsStarNormal where
  isometric a ha := by
    rw [cfcHom_eq_of_isStarNormal]
    exact isometry_subtype_coe.comp <| StarAlgEquiv.isometry (continuousFunctionalCalculus a)
/-
**IsSelfAdjoint.instIsometricContinuousFunctionalCalculus** 是 Mathlib 中的一个实例，位于命
名空间 ``。
形式化陈述：IsSelfAdjoint.instIsometricContinuousFunctionalCalculus : IsometricContinu
ousFunctionalCalculus Real A IsSelfAdjoint
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SpectrumRestricts.isometric_cfc`：∀ {R : Type u_1} {S : Type u_2} {A : Ty
pe u_3} {p q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : 
MetricSpace R] [inst_…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Complex.instStarModuleReal`：StarModule ℝ ℂ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Complex.isometry_ofReal`：Isometry Complex.ofReal
· 使用定理 `IsSelfAdjoint.zero`：∀ (R : Type u_1) [inst : AddMonoid R] [inst_1 : Star
AddMonoid R], IsSelfAdjoint 0
· 使用引理 `isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts`：isSelfAdjoint
_iff_isStarNormal_and_quasispectrumRestricts {a : A} : IsSelfAdjoint a ↔ IsStarN
ormal a ∧ QuasispectrumRestricts a Complex.reCL…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
-/
instance IsSelfAdjoint.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  SpectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

end Unital

section NonUnital

variable [NonUnitalCStarAlgebra A]

open Unitization

/-
**IsStarNormal.instNonUnitalContinuousFunctionalCalculus** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：IsStarNormal.instNonUnitalContinuousFunctionalCalculus : NonUnitalClosedEm
beddingContinuousFunctionalCalculus Complex A IsStarNormal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding`：RCLike.no
nUnitalContinuousFunctionalCalculusIsClosedEmbedding : NonUnitalClosedEmbeddingC
ontinuousFunctionalCalculus 𝕜 A p where toNonUnital…
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用引理 `Unitization.isStarNormal_inr`：isStarNormal_inr : IsStarNormal (a : Uniti
zation R A) ↔ IsStarNormal a
· 使用定理 `instClosedEmbeddingContinuousFunctionalCalculusOfCompleteSpace`：∀ {R : T
ype u_1} {A : Type u_2} {p : A → Prop} [inst : CommSemiring R] [inst_1 : StarRin
g R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologi…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `NonUnitalCStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], CompleteSpace A
-/
theorem IsStarNormal.instNonUnitalContinuousFunctionalCalculus :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℂ A IsStarNormal :=
  RCLike.nonUnitalContinuousFunctionalCalculusIsClosedEmbedding Unitization.isStarNormal_inr

attribute [local instance] IsStarNormal.instNonUnitalContinuousFunctionalCalculus

open scoped CStarAlgebra in
/-
**inr_comp_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inr_comp_cfcₙHom_eq_cfcₙAux (a : A) [ha : IsStarNormal a] :
    (inrNonUnitalStarAlgHom ℂ A).comp (cfcₙHom ha) = cfcₙAux (isStarNormal_inr (R := ℂ)) a ha :=
  inrNonUnitalStarAlgHom_comp_cfcₙHom_eq_cfcₙAux isStarNormal_inr a ha

open ContinuousMapZero in
/-
**IsStarNormal.instNonUnitalIsometricContinuousFunctionalCalculus** 是 Mathlib 中的
一个实例，位于命名空间 ``。
形式化陈述：IsStarNormal.instNonUnitalIsometricContinuousFunctionalCalculus : NonUnita
lIsometricContinuousFunctionalCalculus Complex A IsStarNormal where isometric a 
ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalClosedEmbeddingContinuousFunctionalCalculus.toNonUnitalContinuo
usFunctionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} 
{inst : CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 
: …
· 使用定理 `IsStarNormal.instNonUnitalContinuousFunctionalCalculus`：IsStarNormal.ins
tNonUnitalContinuousFunctionalCalculus : NonUnitalClosedEmbeddingContinuousFunct
ionalCalculus Complex A IsStarNormal
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `quasispectrum.instCompactSpace`：∀ {𝕜 : Type u_1} [inst : NormedField 𝕜] 
{B : Type u_3} [inst_1 : NonUnitalNormedRing B] [inst_2 : NormedSpace 𝕜 B]   [Co
mpleteSpace B] [IsSc…
· 使用定理 `NonUnitalCStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], CompleteSpace A
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Unitization.norm_inr`：norm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖ = ‖a‖
· 使用定理 `Unitization.inrNonUnitalStarAlgHom_apply`：∀ (R : Type u_1) (A : Type u_2
) [inst : CommSemiring R] [inst_1 : StarAddMonoid R] [inst_2 : NonUnitalSemiring
 A]   [inst_3 : Star A] [inst_…
· 使用定理 `NonUnitalStarAlgHom.comp_apply`：comp_apply (f : B ->⋆ₙₐ[R] C) (g : A ->⋆
ₙₐ[R] B) (a : A) : comp f g a = f (g a)
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用引理 `Unitization.isStarNormal_inr`：isStarNormal_inr : IsStarNormal (a : Uniti
zation R A) ↔ IsStarNormal a
· 使用定理 `instClosedEmbeddingContinuousFunctionalCalculusOfCompleteSpace`：∀ {R : T
ype u_1} {A : Type u_2} {p : A → Prop} [inst : CommSemiring R] [inst_1 : StarRin
g R] [inst_2 : MetricSpace R]   [inst_3 : IsTopologi…
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
（共 46 条，此处仅展示前 30 条）
-/
instance IsStarNormal.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus ℂ A IsStarNormal where
  isometric a ha := by
    refine AddMonoidHomClass.isometry_of_norm _ fun f ↦ ?_
    rw [← norm_inr (𝕜 := ℂ), ← inrNonUnitalStarAlgHom_apply, ← NonUnitalStarAlgHom.comp_apply,
      inr_comp_cfcₙHom_eq_cfcₙAux a, cfcₙAux]
    simp only [NonUnitalStarAlgHom.comp_assoc, NonUnitalStarAlgHom.comp_apply,
      NonUnitalStarAlgHom.coe_coe]
    rw [norm_cfcHom (a : Unitization ℂ A), StarAlgEquiv.norm_map]
    rfl
/-
**IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus** 是 Mathlib 中
的一个实例，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus : NonUnit
alIsometricContinuousFunctionalCalculus Real A IsSelfAdjoint
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasispectrumRestricts.isometric_cfc`：∀ {R : Type u_1} {S : Type u_2} {A
 : Type u_3} {p q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst
_2 : MetricSpace R] [inst_…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `Complex.instStarModuleReal`：StarModule ℝ ℂ
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousSemilinearMapClass.toContinuousMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `Complex.isometry_ofReal`：Isometry Complex.ofReal
· 使用定理 `IsSelfAdjoint.zero`：∀ (R : Type u_1) [inst : AddMonoid R] [inst_1 : Star
AddMonoid R], IsSelfAdjoint 0
· 使用引理 `isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts`：isSelfAdjoint
_iff_isStarNormal_and_quasispectrumRestricts {a : A} : IsSelfAdjoint a ↔ IsStarN
ormal a ∧ QuasispectrumRestricts a Complex.reCL…
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
-/
instance IsSelfAdjoint.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint :=
  QuasispectrumRestricts.isometric_cfc Complex.reCLM Complex.isometry_ofReal (.zero _)
    fun _ ↦ isSelfAdjoint_iff_isStarNormal_and_quasispectrumRestricts

end NonUnital

end Normal

/-!
### The spectrum of a nonnegative element is nonnegative
-/

section SpectrumRestricts

open NNReal ENNReal

variable [CStarAlgebra A]

/-
**SpectrumRestricts.nnreal_iff_nnnorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SpectrumRestricts.nnreal_iff_nnnorm {a : A} {t : Real>=0} (ha : IsSelfAdjo
int a) (ht : ‖a‖₊ <= t) : SpectrumRestricts a ContinuousMap.realToNNReal ↔ ‖alge
braMap Real A t - a‖₊ <= t
参数：ha : IsSelfAdjoint a；ht : ‖a‖₊ <= t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.sub`：sub {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x - y)
· 使用定理 `IsSelfAdjoint.algebraMap`：∀ {R : Type u_1} (A : Type u_2) [inst : CommSe
miring R] [inst_1 : StarRing R] [inst_2 : Semiring A] [inst_3 : StarMul A]   [in
st_4 : Algebra…
· 使用定理 `StarModule.complexToReal`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst
_1 : Star E] [inst_2 : _root_.Module ℂ E] [StarModule ℂ E], StarModule ℝ E
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `IsSelfAdjoint.all`：all [Star R] [TrivialStar R] (r : R) : IsSelfAdjoint 
r
· 使用定理 `instTrivialStarReal`：TrivialStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `IsSelfAdjoint.spectralRadius_eq_nnnorm`：IsSelfAdjoint.spectralRadius_eq_
nnnorm {a : A} (ha : IsSelfAdjoint a) : spectralRadius Complex a = ‖a‖₊
· 使用引理 `SpectrumRestricts.spectralRadius_eq`：spectralRadius_eq {𝕜₁ 𝕜₂ A : Type*}
 [NormedField 𝕜₁] [NormedField 𝕜₂] [NormedRing A] [NormedAlgebra 𝕜₁ A] [NormedAl
gebra 𝕜₂ A] [NormedAlgebr…
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用引理 `SpectrumRestricts.nnreal_iff_spectralRadius_le`：nnreal_iff_spectralRadiu
s_le [Algebra Real A] {a : A} {t : Real>=0} (ht : spectralRadius Real a <= t) : 
SpectrumRestricts a ContinuousMap.re…
-/
lemma SpectrumRestricts.nnreal_iff_nnnorm {a : A} {t : ℝ≥0} (ha : IsSelfAdjoint a) (ht : ‖a‖₊ ≤ t) :
    SpectrumRestricts a ContinuousMap.realToNNReal ↔ ‖algebraMap ℝ A t - a‖₊ ≤ t := by
  have : IsSelfAdjoint (algebraMap ℝ A t - a) := IsSelfAdjoint.algebraMap A (.all (t : ℝ)) |>.sub ha
  rw [← ENNReal.coe_le_coe, ← IsSelfAdjoint.spectralRadius_eq_nnnorm,
    ← SpectrumRestricts.spectralRadius_eq (f := Complex.reCLM)] at ht ⊢
  · exact SpectrumRestricts.nnreal_iff_spectralRadius_le ht
  all_goals
    try apply IsSelfAdjoint.spectrumRestricts
    assumption
/-
**SpectrumRestricts.nnreal_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SpectrumRestricts.nnreal_add {a b : A} (ha₁ : IsSelfAdjoint a) (hb₁ : IsSe
lfAdjoint b) (ha₂ : SpectrumRestricts a ContinuousMap.realToNNReal) (hb₂ : Spect
rumRestricts b ContinuousMap.realToNNReal) : SpectrumRestricts (a + b) Continuou
sMap.realToNNReal
参数：ha₁ : IsSelfAdjoint a；hb₁ : IsSelfAdjoint b；ha₂ : SpectrumRestricts a Continu
ousMap.realToNNReal；hb₂ : SpectrumRestricts b ContinuousMap.realToNNReal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SpectrumRestricts.nnreal_iff_nnnorm`：SpectrumRestricts.nnreal_iff_nnnorm
 {a : A} {t : Real>=0} (ha : IsSelfAdjoint a) (ht : ‖a‖₊ <= t) : SpectrumRestric
ts a ContinuousMap.realTo…
· 使用定理 `IsSelfAdjoint.add`：add {x y : R} (hx : IsSelfAdjoint x) (hy : IsSelfAdjo
int y) : IsSelfAdjoint (x + y)
· 使用定理 `nnnorm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E),
 ‖a + b‖₊ ≤ ‖a‖₊ + ‖b‖₊
· 使用定理 `NNReal.coe_add`：∀ (r₁ r₂ : NNReal), ↑(r₁ + r₂) = ↑r₁ + ↑r₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma SpectrumRestricts.nnreal_add {a b : A} (ha₁ : IsSelfAdjoint a)
    (hb₁ : IsSelfAdjoint b) (ha₂ : SpectrumRestricts a ContinuousMap.realToNNReal)
    (hb₂ : SpectrumRestricts b ContinuousMap.realToNNReal) :
    SpectrumRestricts (a + b) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff_nnnorm (ha₁.add hb₁) (nnnorm_add_le a b), NNReal.coe_add,
    map_add, add_sub_add_comm]
  refine nnnorm_add_le _ _ |>.trans ?_
  gcongr
  all_goals rw [← SpectrumRestricts.nnreal_iff_nnnorm] <;> first | rfl | assumption
/-
**IsSelfAdjoint.sq_spectrumRestricts** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.sq_spectrumRestricts {a : A} (ha : IsSelfAdjoint a) : Spectr
umRestricts (a ^ 2) ContinuousMap.realToNNReal
参数：ha : IsSelfAdjoint a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SpectrumRestricts.nnreal_iff`：nnreal_iff {a : A} : SpectrumRestricts a C
ontinuousMap.realToNNReal ↔ forall x in spectrum Real a, 0 <= x
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `cfc_pow`：cfc_pow (f : R -> R) (n : Nat) (a : A) (hf : ContinuousOn f (sp
ectrum R a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用引理 `cfc_map_spectrum`：cfc_map_spectrum (ha : p a
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `StarOrderedRing.toExistsAddOfLE`：∀ {R : Type u_1} [inst : NonUnitalSemir
ing R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],   Ex
istsAddOfLE R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma IsSelfAdjoint.sq_spectrumRestricts {a : A} (ha : IsSelfAdjoint a) :
    SpectrumRestricts (a ^ 2) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff, ← cfc_id (R := ℝ) a, ← cfc_pow .., cfc_map_spectrum ..]
  rintro - ⟨x, -, rfl⟩
  exact sq_nonneg x

open ComplexStarModule
/-
**SpectrumRestricts.eq_zero_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SpectrumRestricts.eq_zero_of_neg {a : A} (ha : IsSelfAdjoint a) (ha₁ : Spe
ctrumRestricts a ContinuousMap.realToNNReal) (ha₂ : SpectrumRestricts (-a) Conti
nuousMap.realToNNReal) : a = 0
参数：ha : IsSelfAdjoint a；ha₁ : SpectrumRestricts a ContinuousMap.realToNNReal；ha₂
 : SpectrumRestricts (-a) ContinuousMap.realToNNReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CFC.eq_zero_of_spectrum_subset_zero`：CFC.eq_zero_of_spectrum_subset_zero
 (h_spec : spectrum R a subseteq {0}) (ha : p a
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_singleton_iff`：subset_singleton_iff {α : Type*} {s : Set α} {
x : α} : s subseteq {x} ↔ forall y in s, y = x
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 49 条，此处仅展示前 30 条）
-/
lemma SpectrumRestricts.eq_zero_of_neg {a : A} (ha : IsSelfAdjoint a)
    (ha₁ : SpectrumRestricts a ContinuousMap.realToNNReal)
    (ha₂ : SpectrumRestricts (-a) ContinuousMap.realToNNReal) :
    a = 0 := by
  rw [SpectrumRestricts.nnreal_iff] at ha₁ ha₂
  apply CFC.eq_zero_of_spectrum_subset_zero (R := ℝ) a
  rw [Set.subset_singleton_iff]
  simp only [← spectrum.neg_eq, Set.mem_neg] at ha₂
  peel ha₁ with x hx _
  linarith [ha₂ (-x) ((neg_neg x).symm ▸ hx)]
/-
**SpectrumRestricts.smul_of_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SpectrumRestricts.smul_of_nonneg {A : Type*} [Ring A] [Algebra Real A] {a 
: A} (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : Real} (hr : 0 <=
 r) : SpectrumRestricts (r • a) ContinuousMap.realToNNReal
参数：ha : SpectrumRestricts a ContinuousMap.realToNNReal；hr : 0 <= r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SpectrumRestricts.nnreal_iff`：nnreal_iff {a : A} : SpectrumRestricts a C
ontinuousMap.realToNNReal ↔ forall x in spectrum Real a, 0 <= x
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `spectrum.zero_eq`：zero_eq [Nontrivial A] : σ (0 : A) = {0}
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `instCanLiftUnitsValIsUnit`：∀ {M : Type u_1} [inst : Monoid M], CanLift M
 Mˣ Units.val IsUnit
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用引理 `le_of_smul_le_smul_left`：le_of_smul_le_smul_left [PosSMulReflectLE α β] 
(h : a • b₁ <= a • b₂) (ha : 0 < a) : b₁ <= b₂
· 使用定理 `Real.instIsDomain`：IsDomain ℝ
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `Set.mem_smul_set_iff_inv_smul_mem`：mem_smul_set_iff_inv_smul_mem : x in 
a • A ↔ a⁻¹ • x in A
（共 37 条，此处仅展示前 30 条）
-/
lemma SpectrumRestricts.smul_of_nonneg {A : Type*} [Ring A] [Algebra ℝ A] {a : A}
    (ha : SpectrumRestricts a ContinuousMap.realToNNReal) {r : ℝ} (hr : 0 ≤ r) :
    SpectrumRestricts (r • a) ContinuousMap.realToNNReal := by
  rw [SpectrumRestricts.nnreal_iff] at ha ⊢
  nontriviality A
  intro x hx
  by_cases hr' : r = 0
  · simp only [hr', zero_smul, spectrum.zero_eq, Set.mem_singleton_iff] at hx ⊢
    exact hx.symm.le
  · lift r to ℝˣ using IsUnit.mk0 r hr'
    rw [← Units.smul_def, spectrum.unit_smul_eq_smul, Set.mem_smul_set_iff_inv_smul_mem] at hx
    refine le_of_smul_le_smul_left ?_ (inv_pos.mpr <| lt_of_le_of_ne hr <| ne_comm.mpr hr')
    simpa [Units.smul_def] using ha _ hx

/-- The `ℝ`-spectrum of an element of the form `star b * b` in a C⋆-algebra is nonnegative.

This is the key result used to establish `CStarAlgebra.instNonnegSpectrumClass`. -/
/-
**spectrum_star_mul_self_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：spectrum_star_mul_self_nonneg {b : A} : forall x in spectrum Real (star b 
* b), 0 <= x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StarMul.star_mul`：∀ {R : Type u} {inst : Mul R} [self : StarMul R] (r s 
: R), star (r * s) = star s * star r
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `IsSelfAdjoint.cfcₙ`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring
 R] [inst_1 : Nontrivial R] [inst_2 : StarRing R]   [inst_3 : MetricSpace R] [in
st_4 : I…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CFC.posPart_sub_negPart`：posPart_sub_negPart (a : A) (ha : IsSelfAdjoint
 a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用引理 `CFC.negPart_mul_posPart`：negPart_mul_posPart (a : A) : a⁻ * a⁺ = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
（共 85 条，此处仅展示前 30 条）

--- 原说明 ---
The `ℝ`-spectrum of an element of the form `star b * b` in a C⋆-algebra is nonne
gative.

This is the key result used to establish `CStarAlgebra.instNonnegSpectrumClass`.
-/
lemma spectrum_star_mul_self_nonneg {b : A} : ∀ x ∈ spectrum ℝ (star b * b), 0 ≤ x := by
  -- for convenience we'll work with `a := star b * b`, which is selfadjoint.
  set a := star b * b with a_def
  have ha : IsSelfAdjoint a := by simp [a_def]
  -- the key element to consider is `c := b * a⁻`, which satisfies `- (star c * c) = a⁻ ^ 3`.
  set c := b * a⁻
  have h_eq_negPart_a : -(star c * c) = a⁻ ^ 3 := calc
    -(star c * c) = - a⁻ * a * a⁻ := by
      simp only [star_mul, c, mul_assoc, ← mul_assoc (star b), ← a_def, CFC.negPart_def,
        neg_mul, IsSelfAdjoint.cfcₙ (f := (·⁻)).star_eq]
    _ = - a⁻ * (a⁺ - a⁻) * a⁻ :=
      congr(- a⁻ * $(CFC.posPart_sub_negPart a ha) * a⁻).symm
    _ = a⁻ ^ 3 := by simp [mul_sub, pow_succ]
  -- the spectrum of `- (star c * c) = a⁻ ^ 3` is nonnegative, since the function on the right
  -- is nonnegative on the spectrum of `a`.
  have h_c_spec₀ : SpectrumRestricts (-(star c * c)) (ContinuousMap.realToNNReal ·) := by
    simp only [SpectrumRestricts.nnreal_iff, h_eq_negPart_a, CFC.negPart_def]
    rw [cfcₙ_eq_cfc (hf0 := by simp), ← cfc_pow (ha := ha) .., cfc_map_spectrum (ha := ha) ..]
    rintro - ⟨x, -, rfl⟩
    positivity
  -- the spectrum of `c * star c` is nonnegative, since squares of selfadjoint elements have
  -- nonnegative spectrum, and `c * star c = 2 • (ℜ c ^ 2 + ℑ c ^ 2) + (- (star c * c))`,
  -- and selfadjoint elements with nonnegative spectrum are closed under addition.
  have h_c_spec₁ : SpectrumRestricts (c * star c) ContinuousMap.realToNNReal := by
    rw [eq_sub_iff_add_eq'.mpr <| star_mul_self_add_self_mul_star c, sub_eq_add_neg, ← sq, ← sq]
    refine SpectrumRestricts.nnreal_add ?_ ?_ ?_ h_c_spec₀
    · exact .smul (star_trivial _) <| ((ℜ c).prop.pow 2).add ((ℑ c).prop.pow 2)
    · exact .neg <| .star_mul_self c
    · rw [← Nat.cast_smul_eq_nsmul ℝ]
      refine (ℜ c).2.sq_spectrumRestricts.nnreal_add ((ℜ c).2.pow 2) ((ℑ c).2.pow 2)
        (ℑ c).2.sq_spectrumRestricts |>.smul_of_nonneg <| by simp
  -- therefore `- (star c * c) = 0` and so `a⁻ ^ 3 = 0`. By properties of the continuous functional
  -- calculus, `fun x ↦ x⁻ ^ 3` is zero on the spectrum of `a`, `0 ≤ x` for `x ∈ spectrum ℝ a`.
  rw [h_c_spec₁.mul_comm.eq_zero_of_neg (.star_mul_self c) h_c_spec₀, neg_zero, CFC.negPart_def,
    cfcₙ_eq_cfc (hf0 := by simp), ← cfc_pow _ _ (ha := ha), ← cfc_zero a (R := ℝ)] at h_eq_negPart_a
  have h_eqOn := eqOn_of_cfc_eq_cfc (ha := ha) h_eq_negPart_a
  exact fun x hx ↦ negPart_eq_zero.mp <| eq_zero_of_pow_eq_zero (h_eqOn hx).symm
/-
**IsSelfAdjoint.coe_mem_spectrum_complex** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.coe_mem_spectrum_complex {A : Type*} [TopologicalSpace A] [R
ing A] [StarRing A] [Algebra Complex A] [ContinuousFunctionalCalculus Complex A 
IsStarNormal] {a : A} {x : Real} (ha : IsSelfAdjoint a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsSelfAdjoint.coe_mem_spectrum_complex {A : Type*} [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra ℂ A] [ContinuousFunctionalCalculus ℂ A IsStarNormal]
    {a : A} {x : ℝ} (ha : IsSelfAdjoint a := by cfc_tac) :
    (x : ℂ) ∈ spectrum ℂ a ↔ x ∈ spectrum ℝ a := by
  simp [← ha.spectrumRestricts.algebraMap_image]

end SpectrumRestricts

section NonnegSpectrumClass

variable [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-
**CStarAlgebra.instNonnegSpectrumClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CStarAlgebra.instNonnegSpectrumClass : NonnegSpectrumClass Real A
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonnegSpectrumClass.of_spectrum_nonneg`：∀ {𝕜 : Type u_3} {A : Type u_4} 
[inst : Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [inst_2 : Ring A]   [inst_3 : Part
ialOrder A] [inst_4 : Algebr…
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用引理 `spectrum_star_mul_self_nonneg`：spectrum_star_mul_self_nonneg {b : A} : f
orall x in spectrum Real (star b * b), 0 <= x
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `spectrum.zero_eq`：zero_eq [Nontrivial A] : σ (0 : A) = {0}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SpectrumRestricts.nnreal_iff`：nnreal_iff {a : A} : SpectrumRestricts a C
ontinuousMap.realToNNReal ↔ forall x in spectrum Real a, 0 <= x
· 使用引理 `SpectrumRestricts.nnreal_add`：SpectrumRestricts.nnreal_add {a b : A} (ha
₁ : IsSelfAdjoint a) (hb₁ : IsSelfAdjoint b) (ha₂ : SpectrumRestricts a Continuo
usMap.realToNNReal…
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用引理 `StarOrderedRing.nonneg_iff`：nonneg_iff : 0 <= x ↔ x in AddSubmonoid.clos
ure (Set.range fun s : R => star s * s)
-/
instance CStarAlgebra.instNonnegSpectrumClass : NonnegSpectrumClass ℝ A :=
  .of_spectrum_nonneg fun a ha ↦ by
    rw [StarOrderedRing.nonneg_iff] at ha
    induction ha using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact spectrum_star_mul_self_nonneg
    | zero =>
      nontriviality A
      simp
    | add x y x_mem y_mem hx hy =>
      rw [← SpectrumRestricts.nnreal_iff] at hx hy ⊢
      rw [← StarOrderedRing.nonneg_iff] at x_mem y_mem
      exact hx.nnreal_add (.of_nonneg x_mem) (.of_nonneg y_mem) hy

open ComplexOrder in
/-
**CStarAlgebra.instNonnegSpectrumClassComplexUnital** 是 Mathlib 中的一个实例，位于命名空间 ``
。
形式化陈述：CStarAlgebra.instNonnegSpectrumClassComplexUnital : NonnegSpectrumClass Co
mplex A where quasispectrum_nonneg_of_nonneg a ha x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mem_quasispectrum_iff`：mem_quasispectrum_iff {R A : Type*} [Semifield R]
 [Ring A] [Algebra R A] {a : A} {x : R} : x in quasispectrum R a ↔ x = 0 ∨ x in 
spectrum R …
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SpectrumRestricts.algebraMap_image`：algebraMap_image (h : SpectrumRestri
cts a f) : algebraMap R S '' spectrum R a = spectrum S a
· 使用引理 `IsSelfAdjoint.spectrumRestricts`：IsSelfAdjoint.spectrumRestricts {a : A}
 (ha : IsSelfAdjoint a) : SpectrumRestricts a Complex.reCLM
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用引理 `spectrum_nonneg_of_nonneg`：spectrum_nonneg_of_nonneg {𝕜 A : Type*} [Comm
Semiring 𝕜] [PartialOrder 𝕜] [Ring A] [PartialOrder A] [Algebra 𝕜 A] [NonnegSpec
trumClass 𝕜 A] …
-/
instance CStarAlgebra.instNonnegSpectrumClassComplexUnital : NonnegSpectrumClass ℂ A where
  quasispectrum_nonneg_of_nonneg a ha x := by
    rw [mem_quasispectrum_iff]
    refine (Or.elim · ge_of_eq fun hx ↦ ?_)
    obtain ⟨y, hy, rfl⟩ := (IsSelfAdjoint.of_nonneg ha).spectrumRestricts.algebraMap_image ▸ hx
    simpa using spectrum_nonneg_of_nonneg ha hy

end NonnegSpectrumClass

section SpectralOrder

variable [NonUnitalCStarAlgebra A]

open scoped CStarAlgebra

variable (A) in
/-- The partial order on a C⋆-algebra defined by `x ≤ y` if and only if `y - x` is
selfadjoint and has nonnegative spectrum.

This is not declared as an instance because one may already have a partial order with better
definitional properties. However, it can be useful to invoke this as an instance in proofs. -/
@[reducible]
/-
**CStarAlgebra.spectralOrder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：CStarAlgebra.spectralOrder : PartialOrder A where le x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The partial order on a C⋆-algebra defined by `x ≤ y` if and only if `y - x` is
selfadjoint and has nonnegative spectrum.

This is not declared as an instance because one may already have a partial order
 with better
definitional properties. However, it can be useful to invoke this as an instance
 in proofs.
-/
def CStarAlgebra.spectralOrder : PartialOrder A where
  le x y := IsSelfAdjoint (y - x) ∧ QuasispectrumRestricts (y - x) ContinuousMap.realToNNReal
  le_refl := by
    simp only [sub_self, IsSelfAdjoint.zero, true_and, forall_const]
    rw [quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ, SpectrumRestricts.nnreal_iff]
    nontriviality A
    simp
  le_antisymm x y hxy hyx := by
    rw [← Unitization.isSelfAdjoint_inr (R := ℂ),
      quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ, Unitization.inr_sub ℂ] at hxy hyx
    rw [← sub_eq_zero]
    apply Unitization.inr_injective (R := ℂ)
    rw [Unitization.inr_zero, Unitization.inr_sub]
    exact hyx.2.eq_zero_of_neg hyx.1 (neg_sub (x : A⁺¹) (y : A⁺¹) ▸ hxy.2)
  le_trans x y z hxy hyz := by
    simp +singlePass only [← Unitization.isSelfAdjoint_inr (R := ℂ),
      quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ] at hxy hyz ⊢
    exact ⟨by simpa using hyz.1.add hxy.1, by simpa using hyz.2.nnreal_add hyz.1 hxy.1 hxy.2⟩

variable (A) in
/-- The `CStarAlgebra.spectralOrder` on a C⋆-algebra is a `StarOrderedRing`. -/
/-
**CStarAlgebra.spectralOrderedRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CStarAlgebra.spectralOrderedRing : @StarOrderedRing A _ (CStarAlgebra.spec
tralOrder A) _
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts`：CFC.exists_s
qrt_of_isSelfAdjoint_of_quasispectrumRestricts {A : Type*} [NonUnitalRing A] [St
arRing A] [TopologicalSpace A] [Module Real A] […
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `SMulCommClass.complexToReal`：∀ {M : Type u_1} {E : Type u_2} [inst : Add
CommGroup E] [inst_1 : _root_.Module ℂ E] [inst_2 : SMul M E]   [SMulCommClass ℂ
 M E], SMulCommCl…
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AddSubmonoid.subset_closure`：∀ {M : Type u_1} [inst : AddZeroClass M] {s
 : Set M}, s ⊆ ↑(AddSubmonoid.closure s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSelfAdjoint.star_eq`：star_eq [Star R] {x : R} (hx : IsSelfAdjoint x) :
 star x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `IsSelfAdjoint.star_mul_self`：star_mul_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (star x * x)
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用引理 `quasispectrumRestricts_iff_spectrumRestricts_inr'`：quasispectrumRestrict
s_iff_spectrumRestricts_inr' {R S' A : Type*} (S : Type*) [Semifield R] [Semifie
ld S'] [Field S] [NonUnitalRing A] [Mod…
· 使用引理 `SpectrumRestricts.nnreal_iff`：nnreal_iff {a : A} : SpectrumRestricts a C
ontinuousMap.realToNNReal ↔ forall x in spectrum Real a, 0 <= x
· 使用定理 `Unitization.inr_mul`：inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [
SMulWithZero R A] (a₁ a₂ : A) : (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂
· 使用定理 `Unitization.inr_star`：inr_star [AddMonoid R] [StarAddMonoid R] [Star A] 
(a : A) : ↑(star a) = star (a : Unitization R A)
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
The `CStarAlgebra.spectralOrder` on a C⋆-algebra is a `StarOrderedRing`.
-/
lemma CStarAlgebra.spectralOrderedRing : @StarOrderedRing A _ (CStarAlgebra.spectralOrder A) _ :=
  let _ := CStarAlgebra.spectralOrder A
  { le_iff := by
      intro x y
      constructor
      · intro h
        obtain ⟨s, hs₁, _, hs₂⟩ :=
          CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts h.1 h.2
        refine ⟨s * s, ?_, by rwa [eq_sub_iff_add_eq', eq_comm] at hs₂⟩
        exact AddSubmonoid.subset_closure ⟨s, by simp [hs₁.star_eq]⟩
      · rintro ⟨p, hp, rfl⟩
        simp +instances only [spectralOrder, add_sub_cancel_left]
        induction hp using AddSubmonoid.closure_induction with
        | mem x hx =>
          obtain ⟨s, rfl⟩ := hx
          refine ⟨IsSelfAdjoint.star_mul_self s, ?_⟩
          rw [quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ,
            SpectrumRestricts.nnreal_iff, Unitization.inr_mul, Unitization.inr_star]
          exact spectrum_star_mul_self_nonneg
        | zero =>
          rw [quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ, SpectrumRestricts.nnreal_iff]
          simp
        | add x y _ _ hx hy =>
          simp +singlePass only [← Unitization.isSelfAdjoint_inr (R := ℂ),
            quasispectrumRestricts_iff_spectrumRestricts_inr' ℂ] at hx hy ⊢
          rw [Unitization.inr_add]
          exact ⟨hx.1.add hy.1, hx.2.nnreal_add hx.1 hy.1 hy.2⟩ }

end SpectralOrder

section NonnegSpectrumClass

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped CStarAlgebra in
/-
**CStarAlgebra.instNonnegSpectrumClass'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CStarAlgebra.instNonnegSpectrumClass' : NonnegSpectrumClass Real A where q
uasispectrum_nonneg_of_nonneg a ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr'`：quasispectrum_eq_spectrum_in
r' (R S : Type*) {A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra 
R S] [Module S A] [IsScalarTower…
· 使用引理 `CStarAlgebra.spectralOrderedRing`：CStarAlgebra.spectralOrderedRing : @St
arOrderedRing A _ (CStarAlgebra.spectralOrder A) _
· 使用引理 `spectrum_nonneg_of_nonneg`：spectrum_nonneg_of_nonneg {𝕜 A : Type*} [Comm
Semiring 𝕜] [PartialOrder 𝕜] [Ring A] [PartialOrder A] [Algebra 𝕜 A] [NonnegSpec
trumClass 𝕜 A] …
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用引理 `StarOrderedRing.nonneg_iff`：nonneg_iff : 0 <= x ↔ x in AddSubmonoid.clos
ure (Set.range fun s : R => star s * s)
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalStarAlgHom.instNonUnitalAlgHomClass`：∀ {R : Type u_1} {A : Type
 u_2} {B : Type u_3} [inst : Monoid R] [inst_1 : NonUnitalNonAssocSemiring A]   
[inst_2 : DistribMulAction R A] [i…
· 使用定理 `AddSubmonoid.mem_map_of_mem`：∀ {M : Type u_1} {N : Type u_2} [inst : Add
ZeroClass M] [inst_1 : AddZeroClass N] {F : Type u_4}   [inst_2 : FunLike F M N]
 [mc : AddMonoidH…
· 使用定理 `AddSubmonoid.closure_mono`：∀ {M : Type u_1} [inst : AddZeroClass M] ⦃s t
 : Set M⦄, s ⊆ t → AddSubmonoid.closure s ≤ AddSubmonoid.closure t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unitization.inrNonUnitalStarAlgHom_apply`：∀ (R : Type u_1) (A : Type u_2
) [inst : CommSemiring R] [inst_1 : StarAddMonoid R] [inst_2 : NonUnitalSemiring
 A]   [inst_3 : Star A] [inst_…
· 使用定理 `Unitization.inr_mul`：inr_mul [MulZeroClass R] [AddZeroClass A] [Mul A] [
SMulWithZero R A] (a₁ a₂ : A) : (↑(a₁ * a₂) : Unitization R A) = a₁ * a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Unitization.inr_star`：inr_star [AddMonoid R] [StarAddMonoid R] [Star A] 
(a : A) : ↑(star a) = star (a : Unitization R A)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `AddMonoidHom.map_mclosure`：∀ {M : Type u_1} {N : Type u_2} [inst : AddZe
roClass M] [inst_1 : AddZeroClass N] {F : Type u_4}   [inst_2 : FunLike F M N] [
mc : AddMonoidH…
-/
instance CStarAlgebra.instNonnegSpectrumClass' : NonnegSpectrumClass ℝ A where
  quasispectrum_nonneg_of_nonneg a ha := by
    rw [Unitization.quasispectrum_eq_spectrum_inr' _ ℂ]
    -- should this actually be an instance on the `Unitization`? (probably scoped)
    let _ := CStarAlgebra.spectralOrder A⁺¹
    have := CStarAlgebra.spectralOrderedRing A⁺¹
    apply spectrum_nonneg_of_nonneg
    rw [StarOrderedRing.nonneg_iff] at ha ⊢
    have := AddSubmonoid.mem_map_of_mem (Unitization.inrNonUnitalStarAlgHom ℂ A) ha
    rw [AddMonoidHom.map_mclosure, ← Set.range_comp] at this
    apply AddSubmonoid.closure_mono ?_ this
    rintro _ ⟨s, rfl⟩
    exact ⟨s, by simp⟩

end NonnegSpectrumClass

section cfc_inr

open CStarAlgebra

variable [NonUnitalCStarAlgebra A]

open scoped NonUnitalContinuousFunctionalCalculus in
/-- This lemma requires a lot from type class synthesis, and so one should instead favor the bespoke
versions for `ℝ≥0`, `ℝ`, and `ℂ`. -/
/-
**Unitization.cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This lemma requires a lot from type class synthesis, and so one should instead f
avor the bespoke
versions for `ℝ≥0`, `ℝ`, and `ℂ`.
-/
lemma Unitization.cfcₙ_eq_cfc_inr {R : Type*} [Semifield R] [StarRing R] [MetricSpace R]
    [IsTopologicalSemiring R] [ContinuousStar R] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [Algebra R ℂ] [IsScalarTower R ℂ A]
    {p : A → Prop} {p' : A⁺¹ → Prop} [NonUnitalContinuousFunctionalCalculus R A p]
    [ContinuousFunctionalCalculus R A⁺¹ p']
    [ContinuousMapZero.UniqueHom R (Unitization ℂ A)]
    (hp : ∀ {a : A}, p' (a : A⁺¹) ↔ p a) (a : A) (f : R → R) (hf₀ : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f (a : A⁺¹) := by
  by_cases h : ContinuousOn f (σₙ R a) ∧ p a
  · obtain ⟨hf, ha⟩ := h
    rw [← cfcₙ_eq_cfc (quasispectrum_inr_eq R ℂ a ▸ hf)]
    exact (inrNonUnitalStarAlgHom ℂ A).map_cfcₙ f a
  · obtain (hf | ha) := not_and_or.mp h
    · rw [cfcₙ_apply_of_not_continuousOn a hf, inr_zero,
        cfc_apply_of_not_continuousOn _ (quasispectrum_eq_spectrum_inr' R ℂ a ▸ hf)]
    · rw [cfcₙ_apply_of_not_predicate a ha, inr_zero,
        cfc_apply_of_not_predicate _ (not_iff_not.mpr hp |>.mpr ha)]
/-
**Unitization.complex_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Unitization.complex_cfcₙ_eq_cfc_inr (a : A) (f : ℂ → ℂ) (hf₀ : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f (a : A⁺¹) :=
  Unitization.cfcₙ_eq_cfc_inr isStarNormal_inr ..

/-- note: the version for `ℝ≥0`, `Unitization.nnreal_cfcₙ_eq_cfc_inr`, can be found in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean` -/
/-
**Unitization.real_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
note: the version for `ℝ≥0`, `Unitization.nnreal_cfcₙ_eq_cfc_inr`, can be found 
in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean`
-/
lemma Unitization.real_cfcₙ_eq_cfc_inr (a : A) (f : ℝ → ℝ) (hf₀ : f 0 = 0 := by cfc_zero_tac) :
    cfcₙ f a = cfc f (a : A⁺¹) :=
  Unitization.cfcₙ_eq_cfc_inr isSelfAdjoint_inr ..

end cfc_inr

