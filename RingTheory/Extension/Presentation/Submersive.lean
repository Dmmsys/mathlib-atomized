/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jung Tao Cheng, Christian Merten, Andrew Yang
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# Submersive presentations

In this file we define `PreSubmersivePresentation`. This is a presentation `P` that has
fewer relations than generators. More precisely there exists an injective map from `σ`
to `ι`. To such a presentation we may associate a Jacobian. `P` is then a submersive
presentation, if its Jacobian is invertible.

Algebras that admit such a presentation are called standard smooth. See
`Mathlib.RingTheory.Smooth.StandardSmooth` for applications.

## Main definitions

All of these are in the `Algebra` namespace. Let `S` be an `R`-algebra.

- `PreSubmersivePresentation`: A `Presentation` of `S` as `R`-algebra, equipped with an injective
  map `P.map` from `σ` to `ι`. This map is used to define the differential of a
  presubmersive presentation.

For a presubmersive presentation `P` of `S` over `R` we make the following definitions:

- `PreSubmersivePresentation.differential`: A linear endomorphism of `σ → P.Ring` sending
  the `j`-th standard basis vector, corresponding to the `j`-th relation, to the vector
  of partial derivatives of `P.relation j` with respect to the coordinates `P.map i` for
  `i : σ`.
- `PreSubmersivePresentation.jacobian`: The determinant of `P.differential`.
- `PreSubmersivePresentation.jacobiMatrix`: If `σ` has a `Fintype` instance, we may form
  the matrix corresponding to `P.differential`. Its determinant is `P.jacobian`.
- `SubmersivePresentation`: A submersive presentation is a finite, presubmersive presentation `P`
  with in `S` invertible Jacobian.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

@[expose] public section

universe t t' w w' u v

open TensorProduct Module MvPolynomial

namespace Algebra

variable (R : Type u) (S : Type v) (ι : Type w) (σ : Type t) [CommRing R] [CommRing S] [Algebra R S]

/--
Definition of `PreSubmersivePresentation` / `PreSubmersivePresentation` 的定义

English:
structure PreSubmersivePresentation
  parameters: extends Algebra.Presentation R S ι σ
  extends: Algebra.Presentation R S ι σ
  axioms and operations (2):
    - map : σ -> ι
    - map_inj : Function.Injective map

中文:
结构 PreSubmersivePresentation
  参数: extends 代数.呈现 R S ι σ
  继承: 代数.呈现 R S ι σ
  公理与运算 (2 个):
    - map : σ -> ι
    - map_inj : 函数.单射 map
-/
structure PreSubmersivePresentation extends Algebra.Presentation R S ι σ where
  /-- A map from the relations type to the variables type. Used to compute the differential. -/
  map : σ -> ι
  map_inj : Function.Injective map

namespace PreSubmersivePresentation

variable {R S ι σ}
variable (P : PreSubmersivePresentation R S ι σ)

include P in
/--
lemma `card_relations_le_card_vars_of_isFinite` / 引理 `card_relations_le_card_vars_of_isFinite`

English:
lemma card_relations_le_card_vars_of_isFinite
  given: [Finite ι]
  proof: Nat.card_le_card_of_injective P.map P.map_inj

中文:
引理 card_relations_le_card_vars_of_isFinite
  条件: [有限 ι]
  证明: Nat.card_le_card_of_injective P.map P.map_inj

Depends on / 依赖: Nat.card_le_card_of_injective, P.map, P.map_inj, card_le_card_of_injective, map_inj
-/
lemma card_relations_le_card_vars_of_isFinite [Finite ι] :
    Nat.card σ <= Nat.card ι :=
  Nat.card_le_card_of_injective P.map P.map_inj

section

variable [Finite σ]

/--
Definition of `basis` / `basis` 的定义

English:
abbreviation basis
  signature: : Basis σ P.Ring (σ -> P.Ring)
  body: Pi.basisFun P.Ring σ

中文:
缩写 basis
  签名: : 基 σ P.环 (σ -> P.环)
  定义体: Pi.basisFun P.Ring σ

Depends on / 依赖: P.Ring, Pi.basisFun, basisFun
-/
noncomputable abbrev basis : Basis σ P.Ring (σ -> P.Ring) :=
  Pi.basisFun P.Ring σ

/--
Definition of `differential` / `differential` 的定义

English:
definition differential
  signature: : (σ -> P.Ring) ->ₗ[P.Ring] (σ -> P.Ring)
  body: Basis.constr P.basis P.Ring
    (fun j i : σ => MvPolynomial.pderiv (P.map i) (P.relation j))

中文:
定义 differential
  签名: : (σ -> P.环) ->ₗ[P.环] (σ -> P.环)
  定义体: Basis.constr P.basis P.Ring
    (fun j i : σ => MvPolynomial.pderiv (P.map i) (P.relation j))

Depends on / 依赖: Basis.constr, MvPolynomial, MvPolynomial.pderiv, P.Ring, P.basis, P.map, P.relation, constr, pderiv, relation
-/
noncomputable def differential : (σ -> P.Ring) ->ₗ[P.Ring] (σ -> P.Ring) :=
  Basis.constr P.basis P.Ring
    (fun j i : σ => MvPolynomial.pderiv (P.map i) (P.relation j))

/--
Definition of `aevalDifferential` / `aevalDifferential` 的定义

English:
definition aevalDifferential
  signature: : (σ -> S) ->ₗ[S] (σ -> S)
  body: (Pi.basisFun S σ).constr S
    (fun j i : σ => aeval P.val <| pderiv (P.map i) (P.relation j))

@[simp]

中文:
定义 aevalDifferential
  签名: : (σ -> S) ->ₗ[S] (σ -> S)
  定义体: (Pi.basisFun S σ).constr S
    (fun j i : σ => aeval P.val <| pderiv (P.map i) (P.relation j))

@[simp]

Depends on / 依赖: P.map, P.relation, P.val, Pi.basisFun, basisFun, constr, pderiv, relation
-/
noncomputable def aevalDifferential : (σ -> S) ->ₗ[S] (σ -> S) :=
  (Pi.basisFun S σ).constr S
    (fun j i : σ => aeval P.val <| pderiv (P.map i) (P.relation j))

@[simp]
/--
lemma `aevalDifferential_single` / 引理 `aevalDifferential_single`

English:
lemma aevalDifferential_single
  given: [DecidableEq σ] (i j : σ)
  proof: by
  dsimp only [aevalDifferential]
  rw [← Pi.basisFun_apply]; rw [Basis.constr_basis]

中文:
引理 aevalDifferential_single
  条件: [DecidableEq σ] (i j : σ)
  证明: by
  dsimp only [aevalDifferential]
  rw [← Pi.basisFun_apply]; rw [Basis.constr_basis]

Depends on / 依赖: Basis.constr_basis, Pi.basisFun_apply, aevalDifferential, basisFun_apply, constr_basis
-/
lemma aevalDifferential_single [DecidableEq σ] (i j : σ) :
    P.aevalDifferential (Pi.single i 1) j = aeval P.val (pderiv (P.map j) (P.relation i)) := by
  dsimp only [aevalDifferential]
  rw [← Pi.basisFun_apply]; rw [Basis.constr_basis]

/--
Definition of `jacobian` / `jacobian` 的定义

English:
definition jacobian
  signature: : S
  body: algebraMap P.Ring S LinearMap.det P.differential

中文:
定义 jacobian
  签名: : S
  定义体: algebraMap P.Ring S LinearMap.det P.differential

Depends on / 依赖: LinearMap, LinearMap.det, P.Ring, P.differential, algebraMap, differential
-/
noncomputable def jacobian : S :=
algebraMap P.Ring S LinearMap.det P.differential

end

section Matrix

variable [Fintype σ] [DecidableEq σ]

/--
Definition of `jacobiMatrix` / `jacobiMatrix` 的定义

English:
definition jacobiMatrix
  signature: : Matrix σ σ P.Ring
  body: LinearMap.toMatrix P.basis P.basis P.differential

中文:
定义 jacobiMatrix
  签名: : 矩阵 σ σ P.环
  定义体: LinearMap.toMatrix P.basis P.basis P.differential

Depends on / 依赖: LinearMap, LinearMap.toMatrix, P.basis, P.differential, differential, toMatrix
-/
noncomputable def jacobiMatrix : Matrix σ σ P.Ring :=
  LinearMap.toMatrix P.basis P.basis P.differential

/--
lemma `jacobian_eq_jacobiMatrix_det` / 引理 `jacobian_eq_jacobiMatrix_det`

English:
lemma jacobian_eq_jacobiMatrix_det
  statement: P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det
  proof: by
  simp [jacobiMatrix, jacobian]

中文:
引理 jacobian_eq_jacobiMatrix_det
  结论: P.jacobian = algebraMap P.环 S P.jacobiMatrix.det
  证明: by
  simp [jacobiMatrix, jacobian]

Depends on / 依赖: jacobiMatrix, jacobian
-/
lemma jacobian_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det := by
  simp [jacobiMatrix, jacobian]

/--
lemma `jacobiMatrix_apply` / 引理 `jacobiMatrix_apply`

English:
lemma jacobiMatrix_apply
  given: (i j : σ)
  proof: by
  simp [jacobiMatrix, LinearMap.toMatrix, differential, basis]

中文:
引理 jacobiMatrix_apply
  条件: (i j : σ)
  证明: by
  simp [jacobiMatrix, LinearMap.toMatrix, differential, basis]

Depends on / 依赖: LinearMap, LinearMap.toMatrix, differential, jacobiMatrix, toMatrix
-/
lemma jacobiMatrix_apply (i j : σ) :
    P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j) := by
  simp [jacobiMatrix, LinearMap.toMatrix, differential, basis]

/--
lemma `aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix` / 引理 `aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix`

English:
lemma aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix
  proof: by
  ext i j : 1
  rw [← LinearMap.toMatrix_eq_toMatrix']
  rw [LinearMap.toMatrix_apply]
  simp [jacobiMatrix_apply]

中文:
引理 aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix
  证明: by
  ext i j : 1
  rw [← LinearMap.toMatrix_eq_toMatrix']
  rw [LinearMap.toMatrix_apply]
  simp [jacobiMatrix_apply]

Depends on / 依赖: LinearMap, LinearMap.toMatrix_apply, LinearMap.toMatrix_eq_toMatrix, jacobiMatrix_apply, toMatrix_apply, toMatrix_eq_toMatrix
-/
lemma aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix :
    P.aevalDifferential.toMatrix' = (aeval P.val).mapMatrix P.jacobiMatrix := by
  ext i j : 1
  rw [← LinearMap.toMatrix_eq_toMatrix']
  rw [LinearMap.toMatrix_apply]
  simp [jacobiMatrix_apply]

end Matrix

section

variable [Finite σ]

/--
lemma `jacobian_eq_det_aevalDifferential` / 引理 `jacobian_eq_det_aevalDifferential`

English:
lemma jacobian_eq_det_aevalDifferential
  statement: P.jacobian = P.aevalDifferential.det
  proof: by
  classical
  cases nonempty_fintype σ
  simp [← LinearMap.det_toMatrix', P.aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix,
    jacobian_eq_jacobiMatrix_det, RingHom.map_det, P.algebraMap_eq]

中文:
引理 jacobian_eq_det_aevalDifferential
  结论: P.jacobian = P.aevalDifferential.det
  证明: by
  classical
  cases nonempty_fintype σ
  simp [← LinearMap.det_toMatrix', P.aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix,
    jacobian_eq_jacobiMatrix_det, RingHom.map_det, P.algebraMap_eq]

Depends on / 依赖: LinearMap, LinearMap.det_toMatrix, P.aevalDifferential_toMatrix, P.algebraMap_eq, RingHom, RingHom.map_det, _eq_mapMatrix_jacobiMatrix, aevalDifferential_toMatrix, algebraMap_eq, classical, det_toMatrix, jacobian_eq_jacobiMatrix_det, map_det, nonempty_fintype
-/
lemma jacobian_eq_det_aevalDifferential : P.jacobian = P.aevalDifferential.det := by
  classical
  cases nonempty_fintype σ
  simp [← LinearMap.det_toMatrix', P.aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix,
    jacobian_eq_jacobiMatrix_det, RingHom.map_det, P.algebraMap_eq]

/--
lemma `isUnit_jacobian_iff_aevalDifferential_bijective` / 引理 `isUnit_jacobian_iff_aevalDifferential_bijective`

English:
lemma isUnit_jacobian_iff_aevalDifferential_bijective
  proof: by
  rw [P.jacobian_eq_det_aevalDifferential]; rw [← LinearMap.isUnit_iff_isUnit_det]
  exact Module.End.isUnit_iff P.aevalDifferential

中文:
引理 isUnit_jacobian_iff_aevalDifferential_bijective
  证明: by
  rw [P.jacobian_eq_det_aevalDifferential]; rw [← LinearMap.isUnit_iff_isUnit_det]
  exact Module.End.isUnit_iff P.aevalDifferential

Depends on / 依赖: LinearMap, LinearMap.isUnit_iff_isUnit_det, Module, Module.End.isUnit_iff, P.aevalDifferential, P.jacobian_eq_det_aevalDifferential, aevalDifferential, isUnit_iff, isUnit_iff_isUnit_det, jacobian_eq_det_aevalDifferential
-/
lemma isUnit_jacobian_iff_aevalDifferential_bijective :
    IsUnit P.jacobian ↔ Function.Bijective P.aevalDifferential := by
  rw [P.jacobian_eq_det_aevalDifferential]; rw [← LinearMap.isUnit_iff_isUnit_det]
  exact Module.End.isUnit_iff P.aevalDifferential

/--
lemma `isUnit_jacobian_of_linearIndependent_of_span_eq_top` / 引理 `isUnit_jacobian_of_linearIndependent_of_span_eq_top`

English:
lemma isUnit_jacobian_of_linearIndependent_of_span_eq_top
  proof: by
  classical
  rw [isUnit_jacobian_iff_aevalDifferential_bijective]
  exact LinearMap.bijective_of_linearIndependent_of_span_eq_top (Pi.basisFun _ _).span_eq
    (by convert! hli; simp) (by convert! hsp; simp)

中文:
引理 isUnit_jacobian_of_linearIndependent_of_span_eq_top
  证明: by
  classical
  rw [isUnit_jacobian_iff_aevalDifferential_bijective]
  exact LinearMap.bijective_of_linearIndependent_of_span_eq_top (Pi.basisFun _ _).span_eq
    (by convert! hli; simp) (by convert! hsp; simp)

Depends on / 依赖: LinearMap, LinearMap.bijective_of_linearIndependent_of_span_eq_top, Pi.basisFun, basisFun, bijective_of_linearIndependent_of_span_eq_top, classical, convert, isUnit_jacobian_iff_aevalDifferential_bijective, span_eq
-/
lemma isUnit_jacobian_of_linearIndependent_of_span_eq_top
    (hli : LinearIndependent S (fun j i : σ => aeval P.val <| pderiv (P.map i) (P.relation j)))
    (hsp : Submodule.span S
      (Set.range <| (fun j i : σ => aeval P.val <| pderiv (P.map i) (P.relation j))) = ⊤) :
    IsUnit P.jacobian := by
  classical
  rw [isUnit_jacobian_iff_aevalDifferential_bijective]
  exact LinearMap.bijective_of_linearIndependent_of_span_eq_top (Pi.basisFun _ _).span_eq
    (by convert! hli; simp) (by convert! hsp; simp)

end

section Constructions

/-- Transport a pre-submersive presentation along an algebra isomorphism. -/
@[simps toPresentation map]
/--
Definition of `ofAlgEquiv` / `ofAlgEquiv` 的定义

English:
definition ofAlgEquiv
  body: P.toPresentation.ofAlgEquiv e
  map := P.map
  map_inj := P.map_inj

@[simp]

中文:
定义 ofAlgEquiv
  定义体: P.toPresentation.ofAlgEquiv e
  map := P.map
  map_inj := P.map_inj

@[simp]

Depends on / 依赖: P.toPresentation.ofAlgEquiv, ofAlgEquiv, toPresentation
-/
noncomputable def ofAlgEquiv
    (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    PreSubmersivePresentation R T ι σ where
  __ := P.toPresentation.ofAlgEquiv e
  map := P.map
  map_inj := P.map_inj

@[simp]
/--
lemma `jacobiMatrix_ofAlgEquiv` / 引理 `jacobiMatrix_ofAlgEquiv`

English:
lemma jacobiMatrix_ofAlgEquiv
  statement: (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T]
  proof: rfl

@[simp]

中文:
引理 jacobiMatrix_ofAlgEquiv
  结论: (P : PreSubmersivePresentation R S ι σ) {T : 类型} [交换环 T]
  证明: rfl

@[simp]
-/
lemma jacobiMatrix_ofAlgEquiv (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T]
    [Algebra R T] (e : S ≃ₐ[R] T) [Fintype σ] [DecidableEq σ] :
    (P.ofAlgEquiv e).jacobiMatrix = P.jacobiMatrix :=
  rfl

@[simp]
/--
lemma `jacobian_ofAlgEquiv` / 引理 `jacobian_ofAlgEquiv`

English:
lemma jacobian_ofAlgEquiv
  statement: (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T]
  proof: by
  classical
  cases nonempty_fintype σ
  rw [jacobian_eq_jacobiMatrix_det]; rw [jacobian_eq_jacobiMatrix_det]
  simp only [ofAlgEquiv_toPresentation, Presentation.ofAlgEquiv_toGenerators,
    jacobiMatrix_ofAlgEquiv, Generators.algebraMap_apply, Generators.ofAlgEquiv_val,
    ← AlgHom.coe_coe e, MvPolynomial.comp_aeval_apply]
  simp [Function.comp_def]

中文:
引理 jacobian_ofAlgEquiv
  结论: (P : PreSubmersivePresentation R S ι σ) {T : 类型} [交换环 T]
  证明: by
  classical
  cases nonempty_fintype σ
  rw [jacobian_eq_jacobiMatrix_det]; rw [jacobian_eq_jacobiMatrix_det]
  simp only [ofAlgEquiv_toPresentation, Presentation.ofAlgEquiv_toGenerators,
    jacobiMatrix_ofAlgEquiv, Generators.algebraMap_apply, Generators.ofAlgEquiv_val,
    ← AlgHom.coe_coe e, MvPolynomial.comp_aeval_apply]
  simp [Function.comp_def]

Depends on / 依赖: AlgHom, AlgHom.coe_coe, Function, Function.comp_def, Generators, Generators.algebraMap_apply, Generators.ofAlgEquiv_val, MvPolynomial, MvPolynomial.comp_aeval_apply, Presentation, Presentation.ofAlgEquiv_toGenerators, algebraMap_apply, classical, coe_coe, comp_aeval_apply, comp_def, jacobiMatrix_ofAlgEquiv, jacobian_eq_jacobiMatrix_det, nonempty_fintype, ofAlgEquiv_toGenerators
-/
lemma jacobian_ofAlgEquiv (P : PreSubmersivePresentation R S ι σ) {T : Type*} [CommRing T]
    [Algebra R T] (e : S ≃ₐ[R] T) [Finite σ] :
    (P.ofAlgEquiv e).jacobian = e P.jacobian := by
  classical
  cases nonempty_fintype σ
  rw [jacobian_eq_jacobiMatrix_det]; rw [jacobian_eq_jacobiMatrix_det]
  simp only [ofAlgEquiv_toPresentation, Presentation.ofAlgEquiv_toGenerators,
    jacobiMatrix_ofAlgEquiv, Generators.algebraMap_apply, Generators.ofAlgEquiv_val,
    ← AlgHom.coe_coe e, MvPolynomial.comp_aeval_apply]
  simp [Function.comp_def]

/--
Definition of `ofBijectiveAlgebraMap` / `ofBijectiveAlgebraMap` 的定义

English:
definition ofBijectiveAlgebraMap
  signature: (h : Function.Bijective (algebraMap R S))
  body: Presentation.ofBijectiveAlgebraMap.{t, w} h
  map := PEmpty.elim
  map_inj (a b : PEmpty) h := by contradiction

@[simp]

中文:
定义 ofBijectiveAlgebraMap
  签名: (h : 函数.双射 (algebraMap R S))
  定义体: Presentation.ofBijectiveAlgebraMap.{t, w} h
  map := PEmpty.elim
  map_inj (a b : PEmpty) h := by contradiction

@[simp]

Depends on / 依赖: Presentation, Presentation.ofBijectiveAlgebraMap, ofBijectiveAlgebraMap
-/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    PreSubmersivePresentation R S PEmpty.{w + 1} PEmpty.{t + 1} where
  toPresentation := Presentation.ofBijectiveAlgebraMap.{t, w} h
  map := PEmpty.elim
  map_inj (a b : PEmpty) h := by contradiction

@[simp]
/--
lemma `ofBijectiveAlgebraMap_jacobian` / 引理 `ofBijectiveAlgebraMap_jacobian`

English:
lemma ofBijectiveAlgebraMap_jacobian
  given: (h : Function.Bijective (algebraMap R S))
  proof: by
  have : (algebraMap (ofBijectiveAlgebraMap h).Ring S).mapMatrix
      (ofBijectiveAlgebraMap h).jacobiMatrix = 1 := by
    ext (i j : PEmpty)
    contradiction
  rw [jacobian_eq_jacobiMatrix_det]; rw [RingHom.map_det]; rw [this]; rw [Matrix.det_one]

中文:
引理 ofBijectiveAlgebraMap_jacobian
  条件: (h : 函数.双射 (algebraMap R S))
  证明: by
  have : (algebraMap (ofBijectiveAlgebraMap h).Ring S).mapMatrix
      (ofBijectiveAlgebraMap h).jacobiMatrix = 1 := by
    ext (i j : PEmpty)
    contradiction
  rw [jacobian_eq_jacobiMatrix_det]; rw [RingHom.map_det]; rw [this]; rw [Matrix.det_one]

Depends on / 依赖: Matrix, Matrix.det_one, PEmpty, RingHom, RingHom.map_det, algebraMap, det_one, jacobiMatrix, jacobian_eq_jacobiMatrix_det, mapMatrix, map_det, ofBijectiveAlgebraMap
-/
lemma ofBijectiveAlgebraMap_jacobian (h : Function.Bijective (algebraMap R S)) :
    (ofBijectiveAlgebraMap h).jacobian = 1 := by
  have : (algebraMap (ofBijectiveAlgebraMap h).Ring S).mapMatrix
      (ofBijectiveAlgebraMap h).jacobiMatrix = 1 := by
    ext (i j : PEmpty)
    contradiction
  rw [jacobian_eq_jacobiMatrix_det]; rw [RingHom.map_det]; rw [this]; rw [Matrix.det_one]

section Localization

variable (r : R) [IsLocalization.Away r S]

variable (S) in
/-- If `S` is the localization of `R` at `r`, this is the canonical submersive presentation
of `S` as `R`-algebra. -/
@[simps map]
/--
Definition of `localizationAway` / `localizationAway` 的定义

English:
definition localizationAway
  signature: : PreSubmersivePresentation R S Unit Unit where
  body: Presentation.localizationAway S r
  map _ := ()
  map_inj _ _ h := h

@[simp]

中文:
定义 localizationAway
  签名: : PreSubmersivePresentation R S 单元 单元 where
  定义体: Presentation.localizationAway S r
  map _ := ()
  map_inj _ _ h := h

@[simp]

Depends on / 依赖: Presentation, Presentation.localizationAway, localizationAway
-/
noncomputable def localizationAway : PreSubmersivePresentation R S Unit Unit where
  __ := Presentation.localizationAway S r
  map _ := ()
  map_inj _ _ h := h

@[simp]
/--
lemma `localizationAway_jacobiMatrix` / 引理 `localizationAway_jacobiMatrix`

English:
lemma localizationAway_jacobiMatrix
  proof: by
  have h : (pderiv ()) (C r * X () - 1) = C r := by simp
  ext (i : Unit) (j : Unit) : 1
  rwa [jacobiMatrix_apply]

@[simp]

中文:
引理 localizationAway_jacobiMatrix
  证明: by
  have h : (pderiv ()) (C r * X () - 1) = C r := by simp
  ext (i : Unit) (j : Unit) : 1
  rwa [jacobiMatrix_apply]

@[simp]

Depends on / 依赖: jacobiMatrix_apply, pderiv
-/
lemma localizationAway_jacobiMatrix :
    (localizationAway S r).jacobiMatrix = Matrix.diagonal (fun () => MvPolynomial.C r) := by
  have h : (pderiv ()) (C r * X () - 1) = C r := by simp
  ext (i : Unit) (j : Unit) : 1
  rwa [jacobiMatrix_apply]

@[simp]
/--
lemma `localizationAway_jacobian` / 引理 `localizationAway_jacobian`

English:
lemma localizationAway_jacobian
  statement: (localizationAway S r).jacobian = algebraMap R S r
  proof: by
  rw [jacobian_eq_jacobiMatrix_det]; rw [localizationAway_jacobiMatrix]
  simp [show Fintype.card (localizationAway r (S := S)).rels = 1 from rfl]

中文:
引理 localizationAway_jacobian
  结论: (localizationAway S r).jacobian = algebraMap R S r
  证明: by
  rw [jacobian_eq_jacobiMatrix_det]; rw [localizationAway_jacobiMatrix]
  simp [show Fintype.card (localizationAway r (S := S)).rels = 1 from rfl]

Depends on / 依赖: Fintype, Fintype.card, jacobian_eq_jacobiMatrix_det, localizationAway, localizationAway_jacobiMatrix
-/
lemma localizationAway_jacobian : (localizationAway S r).jacobian = algebraMap R S r := by
  rw [jacobian_eq_jacobiMatrix_det]; rw [localizationAway_jacobiMatrix]
  simp [show Fintype.card (localizationAway r (S := S)).rels = 1 from rfl]

end Localization

section Composition

variable {ι' σ' T : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (Q : PreSubmersivePresentation S T ι' σ') (P : PreSubmersivePresentation R S ι σ)

/-- Given an `R`-algebra `S` and an `S`-algebra `T` with pre-submersive presentations,
this is the canonical pre-submersive presentation of `T` as an `R`-algebra. -/
@[simps map]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : PreSubmersivePresentation R T (ι' oplus ι) (σ' oplus σ) where
  body: Q.toPresentation.comp P.toPresentation
  map := Sum.elim (fun rq => Sum.inl <| Q.map rq) (fun rp => Sum.inr <| P.map rp)
  map_inj := Function.Injective.sumElim ((Sum.inl_injective).comp (Q.map_inj))
((Sum.inr_injective).comp (P.map_inj)) by simp

中文:
定义 comp
  签名: : PreSubmersivePresentation R T (ι' oplus ι) (σ' oplus σ) where
  定义体: Q.toPresentation.comp P.toPresentation
  map := Sum.elim (fun rq => Sum.inl <| Q.map rq) (fun rp => Sum.inr <| P.map rp)
  map_inj := Function.Injective.sumElim ((Sum.inl_injective).comp (Q.map_inj))
((Sum.inr_injective).comp (P.map_inj)) by simp

Depends on / 依赖: P.toPresentation, Q.toPresentation.comp, toPresentation
-/
noncomputable def comp : PreSubmersivePresentation R T (ι' oplus ι) (σ' oplus σ) where
  __ := Q.toPresentation.comp P.toPresentation
  map := Sum.elim (fun rq => Sum.inl <| Q.map rq) (fun rp => Sum.inr <| P.map rp)
  map_inj := Function.Injective.sumElim ((Sum.inl_injective).comp (Q.map_inj))
((Sum.inr_injective).comp (P.map_inj)) by simp

/--
lemma `toPresentation_comp` / 引理 `toPresentation_comp`

English:
lemma toPresentation_comp
  statement: (Q.comp P).toPresentation = Q.toPresentation.comp P.toPresentation
  proof: rfl

中文:
引理 toPresentation_comp
  结论: (Q.comp P).toPresentation = Q.toPresentation.comp P.toPresentation
  证明: rfl
-/
lemma toPresentation_comp : (Q.comp P).toPresentation = Q.toPresentation.comp P.toPresentation :=
  rfl

/--
lemma `toGenerators_comp` / 引理 `toGenerators_comp`

English:
lemma toGenerators_comp
  statement: (Q.comp P).toGenerators = Q.toGenerators.comp P.toGenerators
  proof: rfl

中文:
引理 toGenerators_comp
  结论: (Q.comp P).toGenerators = Q.toGenerators.comp P.toGenerators
  证明: rfl
-/
lemma toGenerators_comp : (Q.comp P).toGenerators = Q.toGenerators.comp P.toGenerators := rfl

/--
lemma `dimension_comp_eq_dimension_add_dimension` / 引理 `dimension_comp_eq_dimension_add_dimension`

English:
lemma dimension_comp_eq_dimension_add_dimension
  given: [Finite ι] [Finite ι'] [Finite σ] [Finite σ']
  proof: by
  simp only [Presentation.dimension]
  have : Nat.card σ <= Nat.card ι :=
    card_relations_le_card_vars_of_isFinite P
  have : Nat.card σ' <= Nat.card ι' :=
    card_relations_le_card_vars_of_isFinite Q
  simp only [Nat.card_sum]
  lia

中文:
引理 dimension_comp_eq_dimension_add_dimension
  条件: [有限 ι] [有限 ι'] [有限 σ] [有限 σ']
  证明: by
  simp only [Presentation.dimension]
  have : Nat.card σ <= Nat.card ι :=
    card_relations_le_card_vars_of_isFinite P
  have : Nat.card σ' <= Nat.card ι' :=
    card_relations_le_card_vars_of_isFinite Q
  simp only [Nat.card_sum]
  lia

Depends on / 依赖: Nat.card, Nat.card_sum, Presentation, Presentation.dimension, card_relations_le_card_vars_of_isFinite, card_sum, dimension
-/
lemma dimension_comp_eq_dimension_add_dimension [Finite ι] [Finite ι'] [Finite σ] [Finite σ'] :
    (Q.comp P).dimension = Q.dimension + P.dimension := by
  simp only [Presentation.dimension]
  have : Nat.card σ <= Nat.card ι :=
    card_relations_le_card_vars_of_isFinite P
  have : Nat.card σ' <= Nat.card ι' :=
    card_relations_le_card_vars_of_isFinite Q
  simp only [Nat.card_sum]
  lia

section

/-!
### Jacobian of composition

Let `S` be an `R`-algebra and `T` be an `S`-algebra with presentations `P` and `Q` respectively.
In this section we compute the Jacobian of the composition of `Q` and `P` to be
the product of the Jacobians. For this we use a block decomposition of the Jacobi matrix and show
that the upper-right block vanishes, the upper-left block has determinant Jacobian of `Q` and
the lower-right block has determinant Jacobian of `P`.

-/

variable [Fintype σ] [Fintype σ']

open scoped Classical in
/--
lemma `jacobiMatrix_comp_inl_inr` / 引理 `jacobiMatrix_comp_inl_inr`

English:
lemma jacobiMatrix_comp_inl_inr
  given: (i : σ') (j : σ)
  proof: by
  rw [jacobiMatrix_apply]
  refine MvPolynomial.pderiv_eq_zero_of_notMem_vars (fun hmem => ?_)
  apply MvPolynomial.vars_rename at hmem
  simp at hmem

中文:
引理 jacobiMatrix_comp_inl_inr
  条件: (i : σ') (j : σ)
  证明: by
  rw [jacobiMatrix_apply]
  refine MvPolynomial.pderiv_eq_zero_of_notMem_vars (fun hmem => ?_)
  apply MvPolynomial.vars_rename at hmem
  simp at hmem
-/
private lemma jacobiMatrix_comp_inl_inr (i : σ') (j : σ) :
    (Q.comp P).jacobiMatrix (Sum.inl i) (Sum.inr j) = 0 := by
  rw [jacobiMatrix_apply]
  refine MvPolynomial.pderiv_eq_zero_of_notMem_vars (fun hmem => ?_)
  apply MvPolynomial.vars_rename at hmem
  simp at hmem

open scoped Classical in
/--
lemma `jacobiMatrix_comp_₁₂` / 引理 `jacobiMatrix_comp_₁₂`

English:
lemma jacobiMatrix_comp_₁₂
  statement: (Q.comp P).jacobiMatrix.toBlocks₁₂ = 0
  proof: by
  ext i j : 1
  simp [Matrix.toBlocks₁₂, jacobiMatrix_comp_inl_inr]

中文:
引理 jacobiMatrix_comp_₁₂
  结论: (Q.comp P).jacobiMatrix.toBlocks₁₂ = 0
  证明: by
  ext i j : 1
  simp [Matrix.toBlocks₁₂, jacobiMatrix_comp_inl_inr]
-/
private lemma jacobiMatrix_comp_₁₂ : (Q.comp P).jacobiMatrix.toBlocks₁₂ = 0 := by
  ext i j : 1
  simp [Matrix.toBlocks₁₂, jacobiMatrix_comp_inl_inr]

section Q

open scoped Classical in
/--
lemma `jacobiMatrix_comp_inl_inl` / 引理 `jacobiMatrix_comp_inl_inl`

English:
lemma jacobiMatrix_comp_inl_inl
  given: (i j : σ')
  proof: by
  rw [jacobiMatrix_apply]; rw [jacobiMatrix_apply]; rw [comp_map]; rw [Sum.elim_inl]; rw [← Q.comp_aeval_relation_inl P.toPresentation]
  apply aeval_sumElim_pderiv_inl

中文:
引理 jacobiMatrix_comp_inl_inl
  条件: (i j : σ')
  证明: by
  rw [jacobiMatrix_apply]; rw [jacobiMatrix_apply]; rw [comp_map]; rw [Sum.elim_inl]; rw [← Q.comp_aeval_relation_inl P.toPresentation]
  apply aeval_sumElim_pderiv_inl
-/
private lemma jacobiMatrix_comp_inl_inl (i j : σ') :
    aeval (Sum.elim X (MvPolynomial.C ∘ P.val))
      ((Q.comp P).jacobiMatrix (Sum.inl j) (Sum.inl i)) = Q.jacobiMatrix j i := by
  rw [jacobiMatrix_apply]; rw [jacobiMatrix_apply]; rw [comp_map]; rw [Sum.elim_inl]; rw [← Q.comp_aeval_relation_inl P.toPresentation]
  apply aeval_sumElim_pderiv_inl

open scoped Classical in
/--
lemma `jacobiMatrix_comp_₁₁_det` / 引理 `jacobiMatrix_comp_₁₁_det`

English:
lemma jacobiMatrix_comp_₁₁_det
  proof: by
  rw [jacobian_eq_jacobiMatrix_det]; rw [AlgHom.map_det (aeval (Q.comp P).val)]; rw [RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, ← Q.jacobiMatrix_comp_inl_inl P,
    Q.algebraMap_apply]
  apply aeval_sumElim

中文:
引理 jacobiMatrix_comp_₁₁_det
  证明: by
  rw [jacobian_eq_jacobiMatrix_det]; rw [AlgHom.map_det (aeval (Q.comp P).val)]; rw [RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, ← Q.jacobiMatrix_comp_inl_inl P,
    Q.algebraMap_apply]
  apply aeval_sumElim
-/
private lemma jacobiMatrix_comp_₁₁_det :
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det = Q.jacobian := by
  rw [jacobian_eq_jacobiMatrix_det]; rw [AlgHom.map_det (aeval (Q.comp P).val)]; rw [RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.map_apply, RingHom.mapMatrix_apply, ← Q.jacobiMatrix_comp_inl_inl P,
    Q.algebraMap_apply]
  apply aeval_sumElim

end Q

section P

open scoped Classical in
/--
lemma `jacobiMatrix_comp_inr_inr` / 引理 `jacobiMatrix_comp_inr_inr`

English:
lemma jacobiMatrix_comp_inr_inr
  given: (i j : σ)
  proof: by
  rw [jacobiMatrix_apply]; rw [jacobiMatrix_apply]
  simp only [comp_map, Sum.elim_inr]
  apply pderiv_rename Sum.inr_injective

中文:
引理 jacobiMatrix_comp_inr_inr
  条件: (i j : σ)
  证明: by
  rw [jacobiMatrix_apply]; rw [jacobiMatrix_apply]
  simp only [comp_map, Sum.elim_inr]
  apply pderiv_rename Sum.inr_injective
-/
private lemma jacobiMatrix_comp_inr_inr (i j : σ) :
    (Q.comp P).jacobiMatrix (Sum.inr i) (Sum.inr j) =
      MvPolynomial.rename Sum.inr (P.jacobiMatrix i j) := by
  rw [jacobiMatrix_apply]; rw [jacobiMatrix_apply]
  simp only [comp_map, Sum.elim_inr]
  apply pderiv_rename Sum.inr_injective

open scoped Classical in
/--
lemma `jacobiMatrix_comp_₂₂_det` / 引理 `jacobiMatrix_comp_₂₂_det`

English:
lemma jacobiMatrix_comp_₂₂_det
  proof: by
  rw [jacobian_eq_jacobiMatrix_det]
  rw [AlgHom.map_det (aeval (Q.comp P).val)]; rw [RingHom.map_det]; rw [RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.toBlocks₂₂, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    RingHom.mapMatrix_apply, Generators.algebraMap_apply, map_aeval, coe_eval₂Hom]
  rw [jacobiMatrix_comp_inr_inr]; rw [← IsScalarTower.algebraMap_eq]
  simp only [aeval]
  generalize P.jacobiMatrix i j = p
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [algHom_C, algebraMap_eq, eval₂_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, eval₂_mul, hp]
    simp [Presentation.toGenerators_comp, toPresentation_comp]

中文:
引理 jacobiMatrix_comp_₂₂_det
  证明: by
  rw [jacobian_eq_jacobiMatrix_det]
  rw [AlgHom.map_det (aeval (Q.comp P).val)]; rw [RingHom.map_det]; rw [RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.toBlocks₂₂, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    RingHom.mapMatrix_apply, Generators.algebraMap_apply, map_aeval, coe_eval₂Hom]
  rw [jacobiMatrix_comp_inr_inr]; rw [← IsScalarTower.algebraMap_eq]
  simp only [aeval]
  generalize P.jacobiMatrix i j = p
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [algHom_C, algebraMap_eq, eval₂_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, eval₂_mul, hp]
    simp [Presentation.toGenerators_comp, toPresentation_comp]
-/
private lemma jacobiMatrix_comp_₂₂_det :
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = algebraMap S T P.jacobian := by
  rw [jacobian_eq_jacobiMatrix_det]
  rw [AlgHom.map_det (aeval (Q.comp P).val)]; rw [RingHom.map_det]; rw [RingHom.map_det]
  congr
  ext i j : 1
  simp only [Matrix.toBlocks₂₂, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    RingHom.mapMatrix_apply, Generators.algebraMap_apply, map_aeval, coe_eval₂Hom]
  rw [jacobiMatrix_comp_inr_inr]; rw [← IsScalarTower.algebraMap_eq]
  simp only [aeval]
  generalize P.jacobiMatrix i j = p
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [algHom_C, algebraMap_eq, eval₂_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, eval₂_mul, hp]
    simp [Presentation.toGenerators_comp, toPresentation_comp]

end P

end

/-- The Jacobian of the composition of presentations is the product of the Jacobians. -/
@[simp]
/--
lemma `comp_jacobian_eq_jacobian_smul_jacobian` / 引理 `comp_jacobian_eq_jacobian_smul_jacobian`

English:
lemma comp_jacobian_eq_jacobian_smul_jacobian
  given: [Finite σ] [Finite σ']
  proof: by
  classical
  cases nonempty_fintype σ'
  cases nonempty_fintype σ
  rw [jacobian_eq_jacobiMatrix_det]; rw [← Matrix.fromBlocks_toBlocks ((Q.comp P).jacobiMatrix)]; rw [jacobiMatrix_comp_₁₂]
  convert_to
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det *
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = P.jacobian • Q.jacobian
  · simp only [Generators.algebraMap_apply, ← map_mul]
    congr
    convert!
      Matrix.det_fromBlocks_zero₁₂ (Q.comp P).jacobiMatrix.toBlocks₁₁
        (Q.comp P).jacobiMatrix.toBlocks₂₁ (Q.comp P).jacobiMatrix.toBlocks₂₂
  · rw [jacobiMatrix_comp_₁₁_det, jacobiMatrix_comp_₂₂_det, mul_comm, Algebra.smul_def]

中文:
引理 comp_jacobian_eq_jacobian_smul_jacobian
  条件: [有限 σ] [有限 σ']
  证明: by
  classical
  cases nonempty_fintype σ'
  cases nonempty_fintype σ
  rw [jacobian_eq_jacobiMatrix_det]; rw [← Matrix.fromBlocks_toBlocks ((Q.comp P).jacobiMatrix)]; rw [jacobiMatrix_comp_₁₂]
  convert_to
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det *
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = P.jacobian • Q.jacobian
  · simp only [Generators.algebraMap_apply, ← map_mul]
    congr
    convert!
      Matrix.det_fromBlocks_zero₁₂ (Q.comp P).jacobiMatrix.toBlocks₁₁
        (Q.comp P).jacobiMatrix.toBlocks₂₁ (Q.comp P).jacobiMatrix.toBlocks₂₂
  · rw [jacobiMatrix_comp_₁₁_det, jacobiMatrix_comp_₂₂_det, mul_comm, Algebra.smul_def]

Depends on / 依赖: Generators, Generators.algebraMap_apply, Matrix, Matrix.det_fromBlocks_zero, Matrix.fromBlocks_toBlocks, P.jacobian, Q.comp, Q.jacobian, algebraMap_apply, classical, convert, convert_to, fromBlocks_toBlocks, jacobiMa, jacobiMatrix, jacobiMatrix.toBlocks, jacobian, jacobian_eq_jacobiMatrix_det, map_mul, nonempty_fintype
-/
lemma comp_jacobian_eq_jacobian_smul_jacobian [Finite σ] [Finite σ'] :
    (Q.comp P).jacobian = P.jacobian • Q.jacobian := by
  classical
  cases nonempty_fintype σ'
  cases nonempty_fintype σ
  rw [jacobian_eq_jacobiMatrix_det]; rw [← Matrix.fromBlocks_toBlocks ((Q.comp P).jacobiMatrix)]; rw [jacobiMatrix_comp_₁₂]
  convert_to
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₁₁.det *
    (aeval (Q.comp P).val) (Q.comp P).jacobiMatrix.toBlocks₂₂.det = P.jacobian • Q.jacobian
  · simp only [Generators.algebraMap_apply, ← map_mul]
    congr
    convert!
      Matrix.det_fromBlocks_zero₁₂ (Q.comp P).jacobiMatrix.toBlocks₁₁
        (Q.comp P).jacobiMatrix.toBlocks₂₁ (Q.comp P).jacobiMatrix.toBlocks₂₂
  · rw [jacobiMatrix_comp_₁₁_det, jacobiMatrix_comp_₂₂_det, mul_comm, Algebra.smul_def]

end Composition

section BaseChange

variable (T : Type*) [CommRing T] [Algebra R T] (P : PreSubmersivePresentation R S ι σ)

/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: : PreSubmersivePresentation T (T otimes[R] S) ι σ where
  body: P.toPresentation.baseChange T
  map := P.map
  map_inj := P.map_inj

中文:
定义 baseChange
  签名: : PreSubmersivePresentation T (T otimes[R] S) ι σ where
  定义体: P.toPresentation.baseChange T
  map := P.map
  map_inj := P.map_inj

Depends on / 依赖: P.toPresentation.baseChange, baseChange, toPresentation
-/
noncomputable def baseChange : PreSubmersivePresentation T (T otimes[R] S) ι σ where
  __ := P.toPresentation.baseChange T
  map := P.map
  map_inj := P.map_inj

/--
lemma `baseChange_toPresentation` / 引理 `baseChange_toPresentation`

English:
lemma baseChange_toPresentation
  proof: rfl

中文:
引理 baseChange_toPresentation
  证明: rfl
-/
lemma baseChange_toPresentation :
    (P.baseChange R).toPresentation = P.toPresentation.baseChange R :=
  rfl

/--
lemma `baseChange_ring` / 引理 `baseChange_ring`

English:
lemma baseChange_ring
  statement: (P.baseChange R).Ring = P.Ring
  proof: rfl

@[simp]

中文:
引理 baseChange_ring
  结论: (P.baseChange R).环 = P.环
  证明: rfl

@[simp]
-/
lemma baseChange_ring : (P.baseChange R).Ring = P.Ring := rfl

@[simp]
/--
lemma `baseChange_jacobian` / 引理 `baseChange_jacobian`

English:
lemma baseChange_jacobian
  given: [Finite σ]
  statement: (P.baseChange T).jacobian = 1 otimesₜ P.jacobian
  proof: by
  classical
  cases nonempty_fintype σ
  simp_rw [jacobian_eq_jacobiMatrix_det]
  have h : (baseChange T P).jacobiMatrix =
      (MvPolynomial.map (algebraMap R T)).mapMatrix P.jacobiMatrix := by
    ext i j : 1
    simp only [baseChange, jacobiMatrix_apply, Presentation.baseChange_relation,
      RingHom.mapMatrix_apply, Matrix.map_apply,
      Presentation.baseChange_toGenerators, MvPolynomial.pderiv_map]
  rw [h]; rw [← RingHom.map_det]; rw [Generators.algebraMap_apply]; rw [aeval_map_algebraMap]; rw [P.algebraMap_apply]
  apply aeval_one_tmul

中文:
引理 baseChange_jacobian
  条件: [有限 σ]
  结论: (P.baseChange T).jacobian = 1 otimesₜ P.jacobian
  证明: by
  classical
  cases nonempty_fintype σ
  simp_rw [jacobian_eq_jacobiMatrix_det]
  have h : (baseChange T P).jacobiMatrix =
      (MvPolynomial.map (algebraMap R T)).mapMatrix P.jacobiMatrix := by
    ext i j : 1
    simp only [baseChange, jacobiMatrix_apply, Presentation.baseChange_relation,
      RingHom.mapMatrix_apply, Matrix.map_apply,
      Presentation.baseChange_toGenerators, MvPolynomial.pderiv_map]
  rw [h]; rw [← RingHom.map_det]; rw [Generators.algebraMap_apply]; rw [aeval_map_algebraMap]; rw [P.algebraMap_apply]
  apply aeval_one_tmul

Depends on / 依赖: Generators, Generators.algebraMap_apply, Matrix, Matrix.map_apply, MvPolynomial, MvPolynomial.map, MvPolynomial.pderiv_map, P.algebraMap_apply, P.jacobiMatrix, Presentation, Presentation.baseChange_relation, Presentation.baseChange_toGenerators, RingHom, RingHom.mapMatrix_apply, RingHom.map_det, aeval_map_algebraMap, algebraMap, algebraMap_apply, baseChange, baseChange_relation
-/
lemma baseChange_jacobian [Finite σ] : (P.baseChange T).jacobian = 1 otimesₜ P.jacobian := by
  classical
  cases nonempty_fintype σ
  simp_rw [jacobian_eq_jacobiMatrix_det]
  have h : (baseChange T P).jacobiMatrix =
      (MvPolynomial.map (algebraMap R T)).mapMatrix P.jacobiMatrix := by
    ext i j : 1
    simp only [baseChange, jacobiMatrix_apply, Presentation.baseChange_relation,
      RingHom.mapMatrix_apply, Matrix.map_apply,
      Presentation.baseChange_toGenerators, MvPolynomial.pderiv_map]
  rw [h]; rw [← RingHom.map_det]; rw [Generators.algebraMap_apply]; rw [aeval_map_algebraMap]; rw [P.algebraMap_apply]
  apply aeval_one_tmul

end BaseChange

/-- Given a pre-submersive presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced pre-submersive presentation with variables indexed
by `ι` and relations indexed by `κ`. -/
@[simps toPresentation, simps -isSimp map]
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (P : PreSubmersivePresentation R S ι σ)
  body: P.toPresentation.reindex e f
  map := e.symm ∘ P.map ∘ f
  map_inj := by
    rw [Function.Injective.of_comp_iff e.symm.injective]; rw [Function.Injective.of_comp_iff P.map_inj]
    exact f.injective

中文:
定义 reindex
  签名: (P : PreSubmersivePresentation R S ι σ)
  定义体: P.toPresentation.reindex e f
  map := e.symm ∘ P.map ∘ f
  map_inj := by
    rw [Function.Injective.of_comp_iff e.symm.injective]; rw [Function.Injective.of_comp_iff P.map_inj]
    exact f.injective

Depends on / 依赖: P.toPresentation.reindex, reindex, toPresentation
-/
noncomputable def reindex (P : PreSubmersivePresentation R S ι σ)
    {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) :
    PreSubmersivePresentation R S ι' σ' where
  __ := P.toPresentation.reindex e f
  map := e.symm ∘ P.map ∘ f
  map_inj := by
    rw [Function.Injective.of_comp_iff e.symm.injective]; rw [Function.Injective.of_comp_iff P.map_inj]
    exact f.injective

/--
lemma `jacobiMatrix_reindex` / 引理 `jacobiMatrix_reindex`

English:
lemma jacobiMatrix_reindex
  statement: {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ)
  proof: by
  ext i j : 1
  simp [jacobiMatrix_apply,
    MvPolynomial.pderiv_rename e.symm.injective, reindex, Presentation.reindex]

@[simp]

中文:
引理 jacobiMatrix_reindex
  结论: {ι' σ' : 类型} (e : ι' ≃ ι) (f : σ' ≃ σ)
  证明: by
  ext i j : 1
  simp [jacobiMatrix_apply,
    MvPolynomial.pderiv_rename e.symm.injective, reindex, Presentation.reindex]

@[simp]

Depends on / 依赖: MvPolynomial, MvPolynomial.pderiv_rename, Presentation, Presentation.reindex, e.symm.injective, injective, jacobiMatrix_apply, pderiv_rename, reindex
-/
lemma jacobiMatrix_reindex {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ)
    [Fintype σ'] [DecidableEq σ'] [Fintype σ] [DecidableEq σ] :
    (P.reindex e f).jacobiMatrix =
      (P.jacobiMatrix.reindex f.symm f.symm).map (MvPolynomial.rename e.symm) := by
  ext i j : 1
  simp [jacobiMatrix_apply,
    MvPolynomial.pderiv_rename e.symm.injective, reindex, Presentation.reindex]

@[simp]
/--
lemma `jacobian_reindex` / 引理 `jacobian_reindex`

English:
lemma jacobian_reindex
  statement: (P : PreSubmersivePresentation R S ι σ)
  proof: by
  classical
  cases nonempty_fintype σ
  cases nonempty_fintype σ'
  simp_rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  simp only [reindex_toPresentation, Presentation.reindex_toGenerators, jacobiMatrix_reindex,
    Matrix.reindex_apply, Equiv.symm_symm, Generators.algebraMap_apply, Generators.reindex_val]
  simp_rw [← MvPolynomial.aeval_rename,
    ← AlgHom.mapMatrix_apply, ← Matrix.det_submatrix_equiv_self f, AlgHom.map_det,
    AlgHom.mapMatrix_apply, Matrix.map_map]
  simp [← AlgHom.coe_comp, rename_comp_rename, rename_id]

中文:
引理 jacobian_reindex
  结论: (P : PreSubmersivePresentation R S ι σ)
  证明: by
  classical
  cases nonempty_fintype σ
  cases nonempty_fintype σ'
  simp_rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  simp only [reindex_toPresentation, Presentation.reindex_toGenerators, jacobiMatrix_reindex,
    Matrix.reindex_apply, Equiv.symm_symm, Generators.algebraMap_apply, Generators.reindex_val]
  simp_rw [← MvPolynomial.aeval_rename,
    ← AlgHom.mapMatrix_apply, ← Matrix.det_submatrix_equiv_self f, AlgHom.map_det,
    AlgHom.mapMatrix_apply, Matrix.map_map]
  simp [← AlgHom.coe_comp, rename_comp_rename, rename_id]

Depends on / 依赖: AlgHom, AlgHom.coe_comp, AlgHom.mapMatrix_apply, AlgHom.map_det, Equiv.symm_symm, Generators, Generators.algebraMap_apply, Generators.reindex_val, Matrix, Matrix.det_submatrix_equiv_self, Matrix.map_map, Matrix.reindex_apply, MvPolynomial, MvPolynomial.aeval_rename, PreSubmersivePresentation, PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Presentation, Presentation.reindex_toGenerators, aeval_rename, algebraMap_apply
-/
lemma jacobian_reindex (P : PreSubmersivePresentation R S ι σ)
    {ι' σ' : Type*} (e : ι' ≃ ι) (f : σ' ≃ σ) [Finite σ] [Finite σ'] :
    (P.reindex e f).jacobian = P.jacobian := by
  classical
  cases nonempty_fintype σ
  cases nonempty_fintype σ'
  simp_rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  simp only [reindex_toPresentation, Presentation.reindex_toGenerators, jacobiMatrix_reindex,
    Matrix.reindex_apply, Equiv.symm_symm, Generators.algebraMap_apply, Generators.reindex_val]
  simp_rw [← MvPolynomial.aeval_rename,
    ← AlgHom.mapMatrix_apply, ← Matrix.det_submatrix_equiv_self f, AlgHom.map_det,
    AlgHom.mapMatrix_apply, Matrix.map_map]
  simp [← AlgHom.coe_comp, rename_comp_rename, rename_id]

section

variable {v : ι -> MvPolynomial σ R} (a : ι -> σ) (ha : Function.Injective a)
  (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) -> MvPolynomial σ R)
  (hs : forall x, Ideal.Quotient.mk _ (s x) = x)

/--
The naive pre-submersive presentation of a quotient `R[Xᵢ] ⧸ (vⱼ)`.
If the definitional equality of the section matters, it can be explicitly provided.

To construct the associated submersive presentation, use
`PreSubmersivePresentation.jacobiMatrix_naive`.
-/
@[simps! toPresentation]
noncomputable
/--
Definition of `naive` / `naive` 的定义

English:
definition naive
  signature: {v : ι -> MvPolynomial σ R} (a : ι -> σ) (ha : Function.Injective a)
  body: Presentation.naive s hs
  map := a
  map_inj := ha

中文:
定义 naive
  签名: {v : ι -> 多元多项式 σ R} (a : ι -> σ) (ha : 函数.单射 a)
  定义体: Presentation.naive s hs
  map := a
  map_inj := ha

Depends on / 依赖: Function, Function.surjInv, Function.surjInv_eq, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Ideal.span, MvPolynomial, PreSubmersivePresentation, Presentation, Presentation.naive, Quotient, Set.range, map_inj, mk_surjective, surjInv, surjInv_eq
-/
def naive {v : ι -> MvPolynomial σ R} (a : ι -> σ) (ha : Function.Injective a)
    (s : MvPolynomial σ R ⧸ (Ideal.span <| Set.range v) -> MvPolynomial σ R :=
      Function.surjInv Ideal.Quotient.mk_surjective)
    (hs : forall x, Ideal.Quotient.mk _ (s x) = x := by apply Function.surjInv_eq) :
    PreSubmersivePresentation R (MvPolynomial σ R ⧸ (Ideal.span <| Set.range v)) σ ι where
  __ := Presentation.naive s hs
  map := a
  map_inj := ha

/--
lemma `jacobiMatrix_naive` / 引理 `jacobiMatrix_naive`

English:
lemma jacobiMatrix_naive
  given: [Fintype ι] [DecidableEq ι] (i j : ι)
  proof: jacobiMatrix_apply _ _ _

中文:
引理 jacobiMatrix_naive
  条件: [有限类型 ι] [DecidableEq ι] (i j : ι)
  证明: jacobiMatrix_apply _ _ _
-/
@[simp] lemma jacobiMatrix_naive [Fintype ι] [DecidableEq ι] (i j : ι) :
    (naive a ha s hs).jacobiMatrix i j = (v j).pderiv (a i) :=
  jacobiMatrix_apply _ _ _

end

end Constructions

end PreSubmersivePresentation

variable [Finite σ]

/--
Definition of `SubmersivePresentation` / `SubmersivePresentation` 的定义

English:
structure SubmersivePresentation
  parameters: extends PreSubmersivePresentation.{t, w} R S ι σ
  extends: PreSubmersivePresentation.{t, w} R S ι σ
  axioms and operations (1):
    - jacobian_isUnit : IsUnit toPreSubmersivePresentation.jacobian

中文:
结构 浸没呈现
  参数: extends PreSubmersivePresentation.{t, w} R S ι σ
  继承: PreSubmersivePresentation.{t, w} R S ι σ
  公理与运算 (1 个):
    - jacobian_isUnit : 是单位 toPreSubmersivePresentation.jacobian
-/
structure SubmersivePresentation extends PreSubmersivePresentation.{t, w} R S ι σ where
  jacobian_isUnit : IsUnit toPreSubmersivePresentation.jacobian

namespace SubmersivePresentation

open PreSubmersivePresentation

section Constructions

variable {R S ι σ} in
/-- Transport a submersive presentation along an algebra isomorphism. -/
@[simps toPreSubmersivePresentation]
/--
Definition of `ofAlgEquiv` / `ofAlgEquiv` 的定义

English:
definition ofAlgEquiv
  body: P.toPreSubmersivePresentation.ofAlgEquiv e
  jacobian_isUnit := by simp [P.jacobian_isUnit]

中文:
定义 ofAlgEquiv
  定义体: P.toPreSubmersivePresentation.ofAlgEquiv e
  jacobian_isUnit := by simp [P.jacobian_isUnit]

Depends on / 依赖: P.toPreSubmersivePresentation.ofAlgEquiv, ofAlgEquiv, toPreSubmersivePresentation
-/
noncomputable def ofAlgEquiv
    (P : SubmersivePresentation R S ι σ) {T : Type*} [CommRing T] [Algebra R T] (e : S ≃ₐ[R] T) :
    SubmersivePresentation R T ι σ where
  __ := P.toPreSubmersivePresentation.ofAlgEquiv e
  jacobian_isUnit := by simp [P.jacobian_isUnit]

variable {R S} in
/--
Definition of `ofBijectiveAlgebraMap` / `ofBijectiveAlgebraMap` 的定义

English:
definition ofBijectiveAlgebraMap
  signature: (h : Function.Bijective (algebraMap R S))
  body: PreSubmersivePresentation.ofBijectiveAlgebraMap.{t, w} h
  jacobian_isUnit := by
    rw [ofBijectiveAlgebraMap_jacobian]
    exact isUnit_one

中文:
定义 ofBijectiveAlgebraMap
  签名: (h : 函数.双射 (algebraMap R S))
  定义体: PreSubmersivePresentation.ofBijectiveAlgebraMap.{t, w} h
  jacobian_isUnit := by
    rw [ofBijectiveAlgebraMap_jacobian]
    exact isUnit_one

Depends on / 依赖: PreSubmersivePresentation, PreSubmersivePresentation.ofBijectiveAlgebraMap, ofBijectiveAlgebraMap
-/
noncomputable def ofBijectiveAlgebraMap (h : Function.Bijective (algebraMap R S)) :
    SubmersivePresentation R S PEmpty.{w + 1} PEmpty.{t + 1} where
  __ := PreSubmersivePresentation.ofBijectiveAlgebraMap.{t, w} h
  jacobian_isUnit := by
    rw [ofBijectiveAlgebraMap_jacobian]
    exact isUnit_one

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : SubmersivePresentation R R PEmpty.{w + 1} PEmpty.{t + 1}
  body: ofBijectiveAlgebraMap Function.bijective_id

中文:
定义 id
  签名: : 浸没呈现 R R 命题空.{w + 1} 命题空.{t + 1}
  定义体: ofBijectiveAlgebraMap Function.bijective_id

Depends on / 依赖: Function, Function.bijective_id, bijective_id, ofBijectiveAlgebraMap
-/
noncomputable def id : SubmersivePresentation R R PEmpty.{w + 1} PEmpty.{t + 1} :=
  ofBijectiveAlgebraMap Function.bijective_id

section Composition
variable {R S ι σ}
variable {T ι' σ' : Type*} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [Finite σ'] (Q : SubmersivePresentation S T ι' σ') (P : SubmersivePresentation R S ι σ)

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : SubmersivePresentation R T (ι' oplus ι) (σ' oplus σ) where
  body: Q.toPreSubmersivePresentation.comp P.toPreSubmersivePresentation
  jacobian_isUnit := by
    rw [comp_jacobian_eq_jacobian_smul_jacobian]; rw [Algebra.smul_def]; rw [IsUnit.mul_iff]
exact ⟨RingHom.isUnit_map _ P.jacobian_isUnit, Q.jacobian_isUnit⟩

中文:
定义 comp
  签名: : 浸没呈现 R T (ι' oplus ι) (σ' oplus σ) where
  定义体: Q.toPreSubmersivePresentation.comp P.toPreSubmersivePresentation
  jacobian_isUnit := by
    rw [comp_jacobian_eq_jacobian_smul_jacobian]; rw [Algebra.smul_def]; rw [IsUnit.mul_iff]
exact ⟨RingHom.isUnit_map _ P.jacobian_isUnit, Q.jacobian_isUnit⟩

Depends on / 依赖: P.toPreSubmersivePresentation, Q.toPreSubmersivePresentation.comp, toPreSubmersivePresentation
-/
noncomputable def comp : SubmersivePresentation R T (ι' oplus ι) (σ' oplus σ) where
  __ := Q.toPreSubmersivePresentation.comp P.toPreSubmersivePresentation
  jacobian_isUnit := by
    rw [comp_jacobian_eq_jacobian_smul_jacobian]; rw [Algebra.smul_def]; rw [IsUnit.mul_iff]
exact ⟨RingHom.isUnit_map _ P.jacobian_isUnit, Q.jacobian_isUnit⟩

end Composition

section Localization

variable {R} (r : R) [IsLocalization.Away r S]

/--
Definition of `localizationAway` / `localizationAway` 的定义

English:
definition localizationAway
  signature: : SubmersivePresentation R S Unit Unit where
  body: PreSubmersivePresentation.localizationAway S r
  jacobian_isUnit := by
    rw [localizationAway_jacobian]
    exact IsLocalization.map_units _ (⟨r, 1, by simp⟩ : Submonoid.powers r)

中文:
定义 localizationAway
  签名: : 浸没呈现 R S 单元 单元 where
  定义体: PreSubmersivePresentation.localizationAway S r
  jacobian_isUnit := by
    rw [localizationAway_jacobian]
    exact IsLocalization.map_units _ (⟨r, 1, by simp⟩ : Submonoid.powers r)

Depends on / 依赖: PreSubmersivePresentation, PreSubmersivePresentation.localizationAway, localizationAway
-/
noncomputable def localizationAway : SubmersivePresentation R S Unit Unit where
  __ := PreSubmersivePresentation.localizationAway S r
  jacobian_isUnit := by
    rw [localizationAway_jacobian]
    exact IsLocalization.map_units _ (⟨r, 1, by simp⟩ : Submonoid.powers r)

end Localization

section BaseChange

variable (T) [CommRing T] [Algebra R T] (P : SubmersivePresentation R S ι σ)

variable {R S ι σ} in
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: : SubmersivePresentation T (T otimes[R] S) ι σ where
  body: P.toPreSubmersivePresentation.baseChange T
  jacobian_isUnit :=
    P.baseChange_jacobian T ▸ P.jacobian_isUnit.map TensorProduct.includeRight

中文:
定义 baseChange
  签名: : 浸没呈现 T (T otimes[R] S) ι σ where
  定义体: P.toPreSubmersivePresentation.baseChange T
  jacobian_isUnit :=
    P.baseChange_jacobian T ▸ P.jacobian_isUnit.map TensorProduct.includeRight

Depends on / 依赖: P.toPreSubmersivePresentation.baseChange, baseChange, toPreSubmersivePresentation
-/
noncomputable def baseChange : SubmersivePresentation T (T otimes[R] S) ι σ where
  toPreSubmersivePresentation := P.toPreSubmersivePresentation.baseChange T
  jacobian_isUnit :=
    P.baseChange_jacobian T ▸ P.jacobian_isUnit.map TensorProduct.includeRight

end BaseChange

variable {R S ι σ} in
/-- Given a submersive presentation `P` and equivalences `ι' ≃ ι` and
`σ' ≃ σ`, this is the induced submersive presentation with variables indexed
by `ι'` and relations indexed by `σ'` -/
@[simps toPreSubmersivePresentation]
/--
Definition of `reindex` / `reindex` 的定义

English:
definition reindex
  signature: (P : SubmersivePresentation R S ι σ)
  body: P.toPreSubmersivePresentation.reindex e f
  jacobian_isUnit := by simp [P.jacobian_isUnit]

中文:
定义 reindex
  签名: (P : 浸没呈现 R S ι σ)
  定义体: P.toPreSubmersivePresentation.reindex e f
  jacobian_isUnit := by simp [P.jacobian_isUnit]

Depends on / 依赖: P.toPreSubmersivePresentation.reindex, reindex, toPreSubmersivePresentation
-/
noncomputable def reindex (P : SubmersivePresentation R S ι σ)
    {ι' σ' : Type*} [Finite σ'] (e : ι' ≃ ι) (f : σ' ≃ σ) : SubmersivePresentation R S ι' σ' where
  __ := P.toPreSubmersivePresentation.reindex e f
  jacobian_isUnit := by simp [P.jacobian_isUnit]

set_option backward.isDefEq.respectTransparency false in
/-- If `S = 0`, this is the submersive presentation on one generator and one relation. -/
@[simps]
/--
Definition of `ofSubsingleton` / `ofSubsingleton` 的定义

English:
definition ofSubsingleton
  signature: [Subsingleton S]
  body: 1
  σ' _ := 1
  aeval_val_σ' _ := Subsingleton.elim _ _
  relation _ := 1
  span_range_relation_eq_ker := by
    simp [Generators.ker, Extension.ker, RingHom.ker_eq_top_of_subsingleton]
  map _ := ⟨⟩
  map_inj _ _ _ := rfl
  jacobian_isUnit := isUnit_of_subsingleton _

中文:
定义 ofSubsingleton
  签名: [子单例 S]
  定义体: 1
  σ' _ := 1
  aeval_val_σ' _ := Subsingleton.elim _ _
  relation _ := 1
  span_range_relation_eq_ker := by
    simp [Generators.ker, Extension.ker, RingHom.ker_eq_top_of_subsingleton]
  map _ := ⟨⟩
  map_inj _ _ _ := rfl
  jacobian_isUnit := isUnit_of_subsingleton _
-/
noncomputable def ofSubsingleton [Subsingleton S] : SubmersivePresentation R S PUnit PUnit where
  val _ := 1
  σ' _ := 1
  aeval_val_σ' _ := Subsingleton.elim _ _
  relation _ := 1
  span_range_relation_eq_ker := by
    simp [Generators.ker, Extension.ker, RingHom.ker_eq_top_of_subsingleton]
  map _ := ⟨⟩
  map_inj _ _ _ := rfl
  jacobian_isUnit := isUnit_of_subsingleton _

end Constructions

variable {R S ι σ}

open scoped Classical in
/--
Definition of `aevalDifferentialEquiv` / `aevalDifferentialEquiv` 的定义

English:
definition aevalDifferentialEquiv
  signature: (P : SubmersivePresentation R S ι σ)
  body: haveI : Fintype σ := Fintype.ofFinite σ
  have :
      IsUnit (LinearMap.toMatrix (Pi.basisFun S σ) (Pi.basisFun S σ) P.aevalDifferential).det := by
    convert! P.jacobian_isUnit
    rw [LinearMap.toMatrix_eq_toMatrix']; rw [jacobian_eq_jacobiMatrix_det]; rw [aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix]; rw [P.algebraMap_eq]
    simp [RingHom.map_det]
  LinearEquiv.ofIsUnitDet this

中文:
定义 aevalDifferentialEquiv
  签名: (P : 浸没呈现 R S ι σ)
  定义体: haveI : Fintype σ := Fintype.ofFinite σ
  have :
      IsUnit (LinearMap.toMatrix (Pi.basisFun S σ) (Pi.basisFun S σ) P.aevalDifferential).det := by
    convert! P.jacobian_isUnit
    rw [LinearMap.toMatrix_eq_toMatrix']; rw [jacobian_eq_jacobiMatrix_det]; rw [aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix]; rw [P.algebraMap_eq]
    simp [RingHom.map_det]
  LinearEquiv.ofIsUnitDet this

Depends on / 依赖: Fintype, Fintype.ofFinite, IsUnit, LinearEquiv, LinearEquiv.ofIsUnitDet, LinearMap, LinearMap.toMatrix, LinearMap.toMatrix_eq_toMatrix, P.aevalDifferential, P.algebraMap_eq, P.jacobian_isUnit, Pi.basisFun, RingHom, RingHom.map_det, _eq_mapMatrix_jacobiMatrix, aevalDifferential, aevalDifferential_toMatrix, algebraMap_eq, basisFun, convert
-/
noncomputable def aevalDifferentialEquiv (P : SubmersivePresentation R S ι σ) :
    (σ -> S) ≃ₗ[S] (σ -> S) :=
  haveI : Fintype σ := Fintype.ofFinite σ
  have :
      IsUnit (LinearMap.toMatrix (Pi.basisFun S σ) (Pi.basisFun S σ) P.aevalDifferential).det := by
    convert! P.jacobian_isUnit
    rw [LinearMap.toMatrix_eq_toMatrix']; rw [jacobian_eq_jacobiMatrix_det]; rw [aevalDifferential_toMatrix'_eq_mapMatrix_jacobiMatrix]; rw [P.algebraMap_eq]
    simp [RingHom.map_det]
  LinearEquiv.ofIsUnitDet this

variable (P : SubmersivePresentation R S ι σ)

@[simp]
/--
lemma `aevalDifferentialEquiv_apply` / 引理 `aevalDifferentialEquiv_apply`

English:
lemma aevalDifferentialEquiv_apply
  given: (x : σ -> S)
  proof: rfl

中文:
引理 aevalDifferentialEquiv_apply
  条件: (x : σ -> S)
  证明: rfl
-/
lemma aevalDifferentialEquiv_apply (x : σ -> S) :
    P.aevalDifferentialEquiv x = P.aevalDifferential x :=
  rfl

/--
Definition of `basisDeriv` / `basisDeriv` 的定义

English:
definition basisDeriv
  signature: (P : SubmersivePresentation R S ι σ)
  body: Basis.map (Pi.basisFun S σ) P.aevalDifferentialEquiv

@[simp]

中文:
定义 basisDeriv
  签名: (P : 浸没呈现 R S ι σ)
  定义体: Basis.map (Pi.basisFun S σ) P.aevalDifferentialEquiv

@[simp]

Depends on / 依赖: Basis.map, P.aevalDifferentialEquiv, Pi.basisFun, aevalDifferentialEquiv, basisFun
-/
noncomputable def basisDeriv (P : SubmersivePresentation R S ι σ) : Basis σ S (σ -> S) :=
  Basis.map (Pi.basisFun S σ) P.aevalDifferentialEquiv

@[simp]
/--
lemma `basisDeriv_apply` / 引理 `basisDeriv_apply`

English:
lemma basisDeriv_apply
  given: (i j : σ)
  proof: by
  classical
  simp [basisDeriv]

中文:
引理 basisDeriv_apply
  条件: (i j : σ)
  证明: by
  classical
  simp [basisDeriv]

Depends on / 依赖: basisDeriv, classical
-/
lemma basisDeriv_apply (i j : σ) :
    P.basisDeriv i j = (aeval P.val) (pderiv (P.map j) (P.relation i)) := by
  classical
  simp [basisDeriv]

/--
lemma `linearIndependent_aeval_val_pderiv_relation` / 引理 `linearIndependent_aeval_val_pderiv_relation`

English:
lemma linearIndependent_aeval_val_pderiv_relation
  proof: by
  simp_rw [← SubmersivePresentation.basisDeriv_apply]
  exact P.basisDeriv.linearIndependent

中文:
引理 linearIndependent_aeval_val_pderiv_relation
  证明: by
  simp_rw [← SubmersivePresentation.basisDeriv_apply]
  exact P.basisDeriv.linearIndependent

Depends on / 依赖: P.basisDeriv.linearIndependent, SubmersivePresentation, SubmersivePresentation.basisDeriv_apply, basisDeriv, basisDeriv_apply, linearIndependent, simp_rw
-/
lemma linearIndependent_aeval_val_pderiv_relation :
    LinearIndependent S (fun i j => (aeval P.val) (pderiv (P.map j) (P.relation i))) := by
  simp_rw [← SubmersivePresentation.basisDeriv_apply]
  exact P.basisDeriv.linearIndependent

end SubmersivePresentation

end Algebra
