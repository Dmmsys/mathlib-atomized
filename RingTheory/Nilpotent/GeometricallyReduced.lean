/-
Copyright (c) 2025 Dion Leijnse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dion Leijnse
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Geometrically reduced algebras

In this file we introduce geometrically reduced algebras.
For a commutative ring `R` and an `R`-algebra `A`, we say that `A` is geometrically reduced
(`IsGeometricallyReduced`) if for every prime ideal `p` of `R`, the base change of `A`
to an algebraic closure of `κ(p)` is reduced.
In the case of `R = k` a field, this is equivalent to `AlgebraicClosure k ⊗[k] A` being reduced.

## Main results

- `Algebra.isGeometricallyReduced_field_iff` : for a field `k` and a commutative `k`-algebra `A`,
  `A` is geometrically reduced iff `AlgebraicClosure k ⊗[k] A` is reduced.

- `IsGeometricallyReduced.of_forall_fg`: for a field `k` and a commutative `k`-algebra `A`, if all
  finitely generated subalgebras `B` of `A` are geometrically reduced, then `A` is geometrically
  reduced.

## References
- See [https://stacks.math.columbia.edu/tag/05DS] for some theory of geometrically reduced algebras.
  Note that their definition differs from the one here, we still need a proof that these are
  equivalent (see TODO).

## TODO
- Prove that if `A` is a geometrically reduced `R`-algebra, then for every `R`-algebra `K` that is
  a field, the tensor product `K ⊗[R] A` is reduced. (@Thmoas-Guan)

-/

public section

open TensorProduct

noncomputable section

namespace Algebra

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

/-- An `R`-algebra `A` is geometrically reduced iff for every prime ideal `p` of R`
  the base change to `AlgebraicClosure p.ResidueField` is reduced. -/
@[mk_iff]
/--
Definition of `IsGeometricallyReduced` / `IsGeometricallyReduced` 的定义

English:
class IsGeometricallyReduced
  parameters: (R A : Type*) [CommRing R] [Ring A] [Algebra R A]
  axioms and operations (1):
    - isReduced_algebraicClosure_tensorProduct((p : Ideal R) [p.IsPrime]) : IsReduced (AlgebraicClosure p.ResidueField otimes[R] A)

中文:
类 IsGeometricallyReduced
  参数: (R A : 类型) [CommRing R] [Ring A] [Algebra R A]
  公理与运算 (1 个):
    - isReduced_algebraicClosure_tensorProduct((p : Ideal R) [p.IsPrime]) : IsReduced (AlgebraicClosure p.ResidueField otimes[R] A)
-/
class IsGeometricallyReduced (R A : Type*) [CommRing R] [Ring A] [Algebra R A] : Prop where
  isReduced_algebraicClosure_tensorProduct (p : Ideal R) [p.IsPrime] :
    IsReduced (AlgebraicClosure p.ResidueField otimes[R] A)

attribute [instance] IsGeometricallyReduced.isReduced_algebraicClosure_tensorProduct

section Field

/--
lemma `isGeometricallyReduced_field_iff` / 引理 `isGeometricallyReduced_field_iff`

English:
lemma isGeometricallyReduced_field_iff
  given: (k A : Type*) [Field k] [Ring A] [Algebra k A]
  proof: by
  let e (p : Ideal k) [p.IsPrime] : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure p.ResidueField :=
    have := p.algEquivResidueFieldOfField.isAlgebraic
    IsAlgClosure.equiv k _ _
  refine ⟨fun ⟨h⟩ => ?_, fun h => ⟨fun p hp => ?_⟩⟩
  · exact isReduced_of_injective _ (Algebra.TensorProduct.congr (e

中文:
引理 isGeometricallyReduced_field_iff
  条件: (k A : 类型) [Field k] [Ring A] [Algebra k A]
  证明: by
  let e (p : Ideal k) [p.IsPrime] : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure p.ResidueField :=
    have := p.algEquivResidueFieldOfField.isAlgebraic
    IsAlgClosure.equiv k _ _
  refine ⟨fun ⟨h⟩ => ?_, fun h => ⟨fun p hp => ?_⟩⟩
  · exact isReduced_of_injective _ (Algebra.TensorProduct.congr (e

Depends on / 依赖: AlgEquiv, AlgEquiv.refl, Algebra, Algebra.TensorProduct.congr, AlgebraicClosure, IsAlgClosure, IsAlgClosure.equiv, IsPrime, ResidueField, TensorProduct, algEquivResidueFieldOfField, injective, isAlgebraic, isReduced_of_injective, p.IsPrime, p.ResidueField, p.algEquivResidueFieldOfField.isAlgebraic
-/
lemma isGeometricallyReduced_field_iff (k A : Type*) [Field k] [Ring A] [Algebra k A] :
    IsGeometricallyReduced k A ↔ IsReduced (AlgebraicClosure k otimes[k] A) := by
  let e (p : Ideal k) [p.IsPrime] : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure p.ResidueField :=
    have := p.algEquivResidueFieldOfField.isAlgebraic
    IsAlgClosure.equiv k _ _
  refine ⟨fun ⟨h⟩ => ?_, fun h => ⟨fun p hp => ?_⟩⟩
  · exact isReduced_of_injective _ (Algebra.TensorProduct.congr (e ⊥) AlgEquiv.refl).injective
  · exact isReduced_of_injective _ (Algebra.TensorProduct.congr (e p).symm AlgEquiv.refl).injective

instance (k A K : Type*) [Field k] [Ring A] [Algebra k A] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] [IsGeometricallyReduced k A] : IsReduced (K otimes[k] A) := by
  have := (isGeometricallyReduced_field_iff k A).mp ‹_›
  exact isReduced_of_injective
    (Algebra.TensorProduct.map ((IsAlgClosed.lift : K ->ₐ[k] AlgebraicClosure k)) 1)
    (Module.Flat.rTensor_preserves_injective_linearMap _ (RingHom.injective _))

/--
lemma `IsGeometricallyReduced.of_injective` / 引理 `IsGeometricallyReduced.of_injective`

English:
lemma IsGeometricallyReduced.of_injective
  statement: {B : Type*} [Ring B] [Algebra k B] (f : A ->ₐ[k] B)
  proof: by
  rw [isGeometricallyReduced_field_iff]
  exact isReduced_of_injective (Algebra.TensorProduct.map 1 f)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)

中文:
引理 IsGeometricallyReduced.of_injective
  结论: {B : 类型} [Ring B] [Algebra k B] (f : A ->ₐ[k] B)
  证明: by
  rw [isGeometricallyReduced_field_iff]
  exact isReduced_of_injective (Algebra.TensorProduct.map 1 f)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)

Depends on / 依赖: Algebra, Algebra.TensorProduct.map, Module, Module.Flat.lTensor_preserves_injective_linearMap, TensorProduct, isGeometricallyReduced_field_iff, isReduced_of_injective, lTensor_preserves_injective_linearMap
-/
lemma IsGeometricallyReduced.of_injective {B : Type*} [Ring B] [Algebra k B] (f : A ->ₐ[k] B)
    (hf : Function.Injective f) [IsGeometricallyReduced k B] : IsGeometricallyReduced k A := by
  rw [isGeometricallyReduced_field_iff]
  exact isReduced_of_injective (Algebra.TensorProduct.map 1 f)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hf)

variable (k) in
/--
theorem `isReduced_of_isGeometricallyReduced` / 定理 `isReduced_of_isGeometricallyReduced`

English:
theorem isReduced_of_isGeometricallyReduced
  given: [IsGeometricallyReduced k A]
  statement: IsReduced A
  proof: isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A ->ₐ[k] (AlgebraicClosure k) otimes[k] A)
    (Algebra.TensorProduct.includeRight_injective (RingHom.injective _))

中文:
定理 isReduced_of_isGeometricallyReduced
  条件: [IsGeometricallyReduced k A]
  结论: IsReduced A
  证明: isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A ->ₐ[k] (AlgebraicClosure k) otimes[k] A)
    (Algebra.TensorProduct.includeRight_injective (RingHom.injective _))

Depends on / 依赖: Algebra, Algebra.TensorProduct.includeRight, Algebra.TensorProduct.includeRight_injective, AlgebraicClosure, RingHom, RingHom.injective, TensorProduct, includeRight, includeRight_injective, injective, isReduced_of_injective, otimes
-/
theorem isReduced_of_isGeometricallyReduced [IsGeometricallyReduced k A] : IsReduced A :=
  isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A ->ₐ[k] (AlgebraicClosure k) otimes[k] A)
    (Algebra.TensorProduct.includeRight_injective (RingHom.injective _))

/-- If all finitely generated subalgebras of `A` are geometrically reduced, then `A` is
  geometrically reduced. -/
@[stacks 030T]
/--
theorem `IsGeometricallyReduced.of_forall_fg` / 定理 `IsGeometricallyReduced.of_forall_fg`

English:
theorem IsGeometricallyReduced.of_forall_fg
  proof: by
  simp_rw [isGeometricallyReduced_field_iff] at h ⊢
  exact IsReduced.tensorProduct_of_flat_of_forall_fg h

中文:
定理 IsGeometricallyReduced.of_forall_fg
  证明: by
  simp_rw [isGeometricallyReduced_field_iff] at h ⊢
  exact IsReduced.tensorProduct_of_flat_of_forall_fg h

Depends on / 依赖: IsReduced, IsReduced.tensorProduct_of_flat_of_forall_fg, isGeometricallyReduced_field_iff, simp_rw, tensorProduct_of_flat_of_forall_fg
-/
theorem IsGeometricallyReduced.of_forall_fg
    (h : forall B : Subalgebra k A, B.FG -> IsGeometricallyReduced k B) :
    IsGeometricallyReduced k A := by
  simp_rw [isGeometricallyReduced_field_iff] at h ⊢
  exact IsReduced.tensorProduct_of_flat_of_forall_fg h

end Field

end Algebra
