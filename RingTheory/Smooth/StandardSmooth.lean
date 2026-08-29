/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Submersive

/-!
# Standard smooth algebras

A standard smooth algebra is an algebra that admits a `SubmersivePresentation`. A standard
smooth algebra is of relative dimension `n` if it admits a submersive presentation of
dimension `n`.

While every standard smooth algebra is smooth, the converse does not hold. But if `S` is `R`-smooth,
then `S` is `R`-standard smooth locally on `S`, i.e. there exists a set `{ t }` of `S` that
generates the unit ideal, such that `Sₜ` is `R`-standard smooth for every `t` (TODO, see below).

## Main definitions

All of these are in the `Algebra` namespace. Let `S` be an `R`-algebra.

- `Algebra.IsStandardSmooth`: `S` is `R`-standard smooth if `S` admits a submersive
  `R`-presentation.
- `Algebra.IsStandardSmooth.relativeDimension`: If `S` is `R`-standard smooth this is the dimension
  of an arbitrary submersive `R`-presentation of `S`. This is independent of the choice
  of the presentation (TODO, see below).
- `Algebra.IsStandardSmoothOfRelativeDimension n`: `S` is `R`-standard smooth of relative dimension
  `n` if it admits a submersive `R`-presentation of dimension `n`.

## TODO

- Show that locally on the target, smooth algebras are standard smooth.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

@[expose] public section

universe t t' w w' u v

open TensorProduct Module MvPolynomial

variable (n m : Nat)

namespace Algebra

variable (R : Type u) (S : Type v) (ι : Type w) (σ : Type t) [CommRing R] [CommRing S] [Algebra R S]

attribute [local instance] Fintype.ofFinite

/--
Definition of `IsStandardSmooth` / `IsStandardSmooth` 的定义

English:
class IsStandardSmooth
  parameters: : Prop where
  axioms and operations (1):
    - out : exists (ι σ : Type) (_ : Finite σ), Finite ι ∧ Nonempty (SubmersivePresentation R S ι σ)

中文:
类 是StandardSmooth
  参数: : 命题 where
  公理与运算 (1 个):
    - out : 存在 (ι σ : 类型) (_ : 有限 σ), 有限 ι ∧ 非空 (浸没呈现 R S ι σ)
-/
class IsStandardSmooth : Prop where
  out : exists (ι σ : Type) (_ : Finite σ), Finite ι ∧ Nonempty (SubmersivePresentation R S ι σ)

variable [Finite σ]

variable {R S ι σ} in
/--
lemma `SubmersivePresentation.isStandardSmooth` / 引理 `SubmersivePresentation.isStandardSmooth`

English:
lemma SubmersivePresentation.isStandardSmooth
  given: [Finite ι] (P : SubmersivePresentation R S ι σ)
  proof: by
  exact ⟨_, _, _, inferInstance, ⟨P.reindex (Fintype.equivFin _).symm (Fintype.equivFin _).symm⟩⟩

中文:
引理 浸没呈现.isStandardSmooth
  条件: [有限 ι] (P : 浸没呈现 R S ι σ)
  证明: by
  exact ⟨_, _, _, inferInstance, ⟨P.reindex (Fintype.equivFin _).symm (Fintype.equivFin _).symm⟩⟩

Depends on / 依赖: Fintype, Fintype.equivFin, P.reindex, equivFin, reindex
-/
lemma SubmersivePresentation.isStandardSmooth [Finite ι] (P : SubmersivePresentation R S ι σ) :
    IsStandardSmooth R S := by
  exact ⟨_, _, _, inferInstance, ⟨P.reindex (Fintype.equivFin _).symm (Fintype.equivFin _).symm⟩⟩

/--
Definition of `IsStandardSmooth.relativeDimension` / `IsStandardSmooth.relativeDimension` 的定义

English:
definition IsStandardSmooth.relativeDimension
  signature: [IsStandardSmooth R S]
  body: letI := ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose
  ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose_spec.2.some.dimension

中文:
定义 是StandardSmooth.relativeDimension
  签名: [是StandardSmooth R S]
  定义体: letI := ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose
  ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose_spec.2.some.dimension

Depends on / 依赖: IsStandardSmooth, choose_spec, dimension, out.choose_spec.choose_spec.choose, out.choose_spec.choose_spec.choose_spec, some.dimension
-/
noncomputable def IsStandardSmooth.relativeDimension [IsStandardSmooth R S] : Nat :=
  letI := ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose
  ‹IsStandardSmooth R S›.out.choose_spec.choose_spec.choose_spec.2.some.dimension

/--
Definition of `IsStandardSmoothOfRelativeDimension` / `IsStandardSmoothOfRelativeDimension` 的定义

English:
class IsStandardSmoothOfRelativeDimension
  parameters: : Prop where
  axioms and operations (1):
    - out : exists (ι σ : Type) (_ : Finite σ) (_ : Finite ι) (P : SubmersivePresentation R S ι σ), P.dimension = n

中文:
类 是StandardSmoothOfRelativeDimension
  参数: : 命题 where
  公理与运算 (1 个):
    - out : 存在 (ι σ : 类型) (_ : 有限 σ) (_ : 有限 ι) (P : 浸没呈现 R S ι σ), P.dimension = n
-/
class IsStandardSmoothOfRelativeDimension : Prop where
  out : exists (ι σ : Type) (_ : Finite σ) (_ : Finite ι) (P : SubmersivePresentation R S ι σ),
    P.dimension = n

variable {R S ι σ n} in
/--
lemma `SubmersivePresentation.isStandardSmoothOfRelativeDimension` / 引理 `SubmersivePresentation.isStandardSmoothOfRelativeDimension`

English:
lemma SubmersivePresentation.isStandardSmoothOfRelativeDimension
  statement: [Finite ι]
  proof: by
  refine ⟨⟨_, _, _, inferInstance,
    P.reindex (Fintype.equivFin _).symm (Fintype.equivFin σ).symm, ?_⟩⟩
  simp [hP]

中文:
引理 浸没呈现.isStandardSmoothOfRelativeDimension
  结论: [有限 ι]
  证明: by
  refine ⟨⟨_, _, _, inferInstance,
    P.reindex (Fintype.equivFin _).symm (Fintype.equivFin σ).symm, ?_⟩⟩
  simp [hP]

Depends on / 依赖: Fintype, Fintype.equivFin, P.reindex, equivFin, reindex
-/
lemma SubmersivePresentation.isStandardSmoothOfRelativeDimension [Finite ι]
    (P : SubmersivePresentation R S ι σ) (hP : P.dimension = n) :
    IsStandardSmoothOfRelativeDimension n R S := by
  refine ⟨⟨_, _, _, inferInstance,
    P.reindex (Fintype.equivFin _).symm (Fintype.equivFin σ).symm, ?_⟩⟩
  simp [hP]

variable {R} {S}

/--
lemma `IsStandardSmoothOfRelativeDimension.isStandardSmooth` / 引理 `IsStandardSmoothOfRelativeDimension.isStandardSmooth`

English:
lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth
  proof: ⟨_, _, _, H.out.choose_spec.choose_spec.choose_spec.choose,
    H.out.choose_spec.choose_spec.choose_spec.choose_spec.nonempty⟩

中文:
引理 是StandardSmoothOfRelativeDimension.isStandardSmooth
  证明: ⟨_, _, _, H.out.choose_spec.choose_spec.choose_spec.choose,
    H.out.choose_spec.choose_spec.choose_spec.choose_spec.nonempty⟩
-/
lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth
    [H : IsStandardSmoothOfRelativeDimension n R S] : IsStandardSmooth R S :=
  ⟨_, _, _, H.out.choose_spec.choose_spec.choose_spec.choose,
    H.out.choose_spec.choose_spec.choose_spec.choose_spec.nonempty⟩

/--
lemma `IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective` / 引理 `IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective`

English:
lemma IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
  proof: ⟨_, _, _, inferInstance,
    SubmersivePresentation.ofBijectiveAlgebraMap h, Presentation.ofBijectiveAlgebraMap_dimension h⟩

中文:
引理 是StandardSmoothOfRelativeDimension.of_algebraMap_bijective
  证明: ⟨_, _, _, inferInstance,
    SubmersivePresentation.ofBijectiveAlgebraMap h, Presentation.ofBijectiveAlgebraMap_dimension h⟩

Depends on / 依赖: Presentation, Presentation.ofBijectiveAlgebraMap_dimension, SubmersivePresentation, SubmersivePresentation.ofBijectiveAlgebraMap, ofBijectiveAlgebraMap, ofBijectiveAlgebraMap_dimension
-/
lemma IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
    (h : Function.Bijective (algebraMap R S)) :
    IsStandardSmoothOfRelativeDimension 0 R S :=
  ⟨_, _, _, inferInstance,
    SubmersivePresentation.ofBijectiveAlgebraMap h, Presentation.ofBijectiveAlgebraMap_dimension h⟩

variable (R) in
/--
Instance `IsStandardSmoothOfRelativeDimension.id` / 实例 `IsStandardSmoothOfRelativeDimension.id`

English:
instance IsStandardSmoothOfRelativeDimension.id
  signature: :
  body: IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective Function.bijective_id

中文:
实例 是StandardSmoothOfRelativeDimension.id
  签名: :
  定义体: IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective Function.bijective_id
-/
instance IsStandardSmoothOfRelativeDimension.id :
    IsStandardSmoothOfRelativeDimension 0 R R :=
  IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective Function.bijective_id

instance (priority := 100) IsStandardSmooth.finitePresentation [IsStandardSmooth R S] :
    FinitePresentation R S := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.finitePresentation_of_isFinite

/--
lemma `IsStandardSmooth.of_algEquiv` / 引理 `IsStandardSmooth.of_algEquiv`

English:
lemma IsStandardSmooth.of_algEquiv
  statement: {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T)
  proof: by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact (P.ofAlgEquiv e).isStandardSmooth

中文:
引理 是StandardSmooth.of_algEquiv
  结论: {T : 类型} [交换环 T] [代数 R T] (e : S ≃ₐ[R] T)
  证明: by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact (P.ofAlgEquiv e).isStandardSmooth

Depends on / 依赖: IsStandardSmooth, P.ofAlgEquiv, isStandardSmooth, ofAlgEquiv
-/
lemma IsStandardSmooth.of_algEquiv {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T)
    [IsStandardSmooth R S] : IsStandardSmooth R T := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact (P.ofAlgEquiv e).isStandardSmooth

/--
lemma `IsStandardSmoothOfRelativeDimension.of_algEquiv` / 引理 `IsStandardSmoothOfRelativeDimension.of_algEquiv`

English:
lemma IsStandardSmoothOfRelativeDimension.of_algEquiv
  statement: {T : Type*} [CommRing T] [Algebra R T]
  proof: by
  obtain ⟨_, _, _, _, ⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  exact (P.ofAlgEquiv e).isStandardSmoothOfRelativeDimension (by simpa)

中文:
引理 是StandardSmoothOfRelativeDimension.of_algEquiv
  结论: {T : 类型} [交换环 T] [代数 R T]
  证明: by
  obtain ⟨_, _, _, _, ⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  exact (P.ofAlgEquiv e).isStandardSmoothOfRelativeDimension (by simpa)

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, P.ofAlgEquiv, isStandardSmoothOfRelativeDimension, ofAlgEquiv
-/
lemma IsStandardSmoothOfRelativeDimension.of_algEquiv {T : Type*} [CommRing T] [Algebra R T]
    (e : S ≃ₐ[R] T) [IsStandardSmoothOfRelativeDimension n R S] :
    IsStandardSmoothOfRelativeDimension n R T := by
  obtain ⟨_, _, _, _, ⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  exact (P.ofAlgEquiv e).isStandardSmoothOfRelativeDimension (by simpa)

section Composition

variable (R S T) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/--
lemma `IsStandardSmooth.trans` / 引理 `IsStandardSmooth.trans`

English:
lemma IsStandardSmooth.trans
  given: [IsStandardSmooth R S] [IsStandardSmooth S T]
  proof: by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    obtain ⟨_, _, _, _, ⟨Q⟩⟩ := ‹IsStandardSmooth S T›
    exact ⟨_, _, _, inferInstance, ⟨Q.comp P⟩⟩

中文:
引理 是StandardSmooth.trans
  条件: [是StandardSmooth R S] [是StandardSmooth S T]
  证明: by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    obtain ⟨_, _, _, _, ⟨Q⟩⟩ := ‹IsStandardSmooth S T›
    exact ⟨_, _, _, inferInstance, ⟨Q.comp P⟩⟩

Depends on / 依赖: IsStandardSmooth, Q.comp
-/
lemma IsStandardSmooth.trans [IsStandardSmooth R S] [IsStandardSmooth S T] :
    IsStandardSmooth R T where
  out := by
    obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    obtain ⟨_, _, _, _, ⟨Q⟩⟩ := ‹IsStandardSmooth S T›
    exact ⟨_, _, _, inferInstance, ⟨Q.comp P⟩⟩

/--
lemma `IsStandardSmoothOfRelativeDimension.trans` / 引理 `IsStandardSmoothOfRelativeDimension.trans`

English:
lemma IsStandardSmoothOfRelativeDimension.trans
  statement: [IsStandardSmoothOfRelativeDimension n R S]
  proof: by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    obtain ⟨_, _, _, _, Q, hQ⟩ := ‹IsStandardSmoothOfRelativeDimension m S T›
    refine ⟨_, _, _, inferInstance, Q.comp P, hP ▸ hQ ▸ ?_⟩
    apply PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension

中文:
引理 是StandardSmoothOfRelativeDimension.trans
  结论: [是StandardSmoothOfRelativeDimension n R S]
  证明: by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    obtain ⟨_, _, _, _, Q, hQ⟩ := ‹IsStandardSmoothOfRelativeDimension m S T›
    refine ⟨_, _, _, inferInstance, Q.comp P, hP ▸ hQ ▸ ?_⟩
    apply PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, PreSubmersivePresentation, PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension, Q.comp, dimension_comp_eq_dimension_add_dimension
-/
lemma IsStandardSmoothOfRelativeDimension.trans [IsStandardSmoothOfRelativeDimension n R S]
    [IsStandardSmoothOfRelativeDimension m S T] :
    IsStandardSmoothOfRelativeDimension (m + n) R T where
  out := by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    obtain ⟨_, _, _, _, Q, hQ⟩ := ‹IsStandardSmoothOfRelativeDimension m S T›
    refine ⟨_, _, _, inferInstance, Q.comp P, hP ▸ hQ ▸ ?_⟩
    apply PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension

end Composition

/--
lemma `IsStandardSmooth.localization_away` / 引理 `IsStandardSmooth.localization_away`

English:
lemma IsStandardSmooth.localization_away
  given: (r : R) [IsLocalization.Away r S]
  proof: ⟨_, _, _, inferInstance, ⟨SubmersivePresentation.localizationAway S r⟩⟩

中文:
引理 是StandardSmooth.localization_away
  条件: (r : R) [是Localization.Away r S]
  证明: ⟨_, _, _, inferInstance, ⟨SubmersivePresentation.localizationAway S r⟩⟩

Depends on / 依赖: SubmersivePresentation, SubmersivePresentation.localizationAway, localizationAway
-/
lemma IsStandardSmooth.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmooth R S where
  out := ⟨_, _, _, inferInstance, ⟨SubmersivePresentation.localizationAway S r⟩⟩

/--
lemma `IsStandardSmoothOfRelativeDimension.localization_away` / 引理 `IsStandardSmoothOfRelativeDimension.localization_away`

English:
lemma IsStandardSmoothOfRelativeDimension.localization_away
  given: (r : R) [IsLocalization.Away r S]
  proof: ⟨_, _, _, inferInstance, SubmersivePresentation.localizationAway S r,
    Presentation.localizationAway_dimension_zero r⟩

中文:
引理 是StandardSmoothOfRelativeDimension.localization_away
  条件: (r : R) [是Localization.Away r S]
  证明: ⟨_, _, _, inferInstance, SubmersivePresentation.localizationAway S r,
    Presentation.localizationAway_dimension_zero r⟩

Depends on / 依赖: SubmersivePresentation, SubmersivePresentation.localizationAway, localizationAway
-/
lemma IsStandardSmoothOfRelativeDimension.localization_away (r : R) [IsLocalization.Away r S] :
    IsStandardSmoothOfRelativeDimension 0 R S where
  out := ⟨_, _, _, inferInstance, SubmersivePresentation.localizationAway S r,
    Presentation.localizationAway_dimension_zero r⟩

section BaseChange

variable (T) [CommRing T] [Algebra R T]

/--
Instance `IsStandardSmooth.baseChange` / 实例 `IsStandardSmooth.baseChange`

English:
instance IsStandardSmooth.baseChange
  signature: [IsStandardSmooth R S]
  body: by
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    exact ⟨ι, σ, _, inferInstance, ⟨P.baseChange T⟩⟩

中文:
实例 是StandardSmooth.baseChange
  签名: [是StandardSmooth R S]
  定义体: by
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    exact ⟨ι, σ, _, inferInstance, ⟨P.baseChange T⟩⟩

Depends on / 依赖: IsStandardSmooth, P.baseChange, baseChange
-/
instance IsStandardSmooth.baseChange [IsStandardSmooth R S] :
    IsStandardSmooth T (T otimes[R] S) where
  out := by
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
    exact ⟨ι, σ, _, inferInstance, ⟨P.baseChange T⟩⟩

/--
Instance `IsStandardSmoothOfRelativeDimension.baseChange` / 实例 `IsStandardSmoothOfRelativeDimension.baseChange`

English:
instance IsStandardSmoothOfRelativeDimension.baseChange
  body: by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    exact ⟨_, _, _, inferInstance, P.baseChange T, hP⟩

中文:
实例 是StandardSmoothOfRelativeDimension.baseChange
  定义体: by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    exact ⟨_, _, _, inferInstance, P.baseChange T, hP⟩

Depends on / 依赖: IsStandardSmoothOfRelativeDimension, P.baseChange, baseChange
-/
instance IsStandardSmoothOfRelativeDimension.baseChange
    [IsStandardSmoothOfRelativeDimension n R S] :
    IsStandardSmoothOfRelativeDimension n T (T otimes[R] S) where
  out := by
    obtain ⟨_, _, _, _, P, hP⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
    exact ⟨_, _, _, inferInstance, P.baseChange T, hP⟩

end BaseChange

@[nontriviality]
instance (priority := 100) [Subsingleton S] : IsStandardSmooth R S :=
  ⟨Unit, Unit, inferInstance, inferInstance, ⟨.ofSubsingleton R S⟩⟩

@[nontriviality]
instance (priority := 100) [Subsingleton S] : IsStandardSmoothOfRelativeDimension 0 R S :=
  ⟨Unit, Unit, inferInstance, inferInstance, .ofSubsingleton R S, by simp [Presentation.dimension]⟩

end Algebra
