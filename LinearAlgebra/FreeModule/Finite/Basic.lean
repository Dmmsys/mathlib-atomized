/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.StdBasis
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite and free modules

We provide some instances for finite and free modules.

## Main results

* `Module.Free.ChooseBasisIndex.fintype` : If a free module is finite, then any basis is finite.
* `Module.Finite.of_basis` : A free module with a basis indexed by a `Fintype` is finite.
-/

public section

universe u v w

/--
Instance `Module.Free.ChooseBasisIndex.fintype` / 实例 `Module.Free.ChooseBasisIndex.fintype`

English:
instance Module.Free.ChooseBasisIndex.fintype
  signature: (R : Type u) (M : Type v)
  body: by
  refine @Fintype.ofFinite _ ?_
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    rw [ChooseBasisIndex]
    infer_instance
  · exact Module.Finite.finite_basis (chooseBasis _ _)

中文:
实例 模.自由.ChooseBasisIndex.fintype
  签名: (R : 类型u) (M : 类型v)
  定义体: by
  refine @Fintype.ofFinite _ ?_
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    rw [ChooseBasisIndex]
    infer_instance
  · exact Module.Finite.finite_basis (chooseBasis _ _)

Depends on / 依赖: ChooseBasisIndex, Finite, Fintype, Fintype.ofFinite, Module, Module.Finite.finite_basis, Module.subsingleton, chooseBasis, finite_basis, infer_instance, ofFinite, subsingleton, subsingleton_or_nontrivial
-/
noncomputable instance Module.Free.ChooseBasisIndex.fintype (R : Type u) (M : Type v)
    [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M] :
    Fintype (Module.Free.ChooseBasisIndex R M) := by
  refine @Fintype.ofFinite _ ?_
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    rw [ChooseBasisIndex]
    infer_instance
  · exact Module.Finite.finite_basis (chooseBasis _ _)

/--
theorem `Module.Finite.of_basis` / 定理 `Module.Finite.of_basis`

English:
theorem Module.Finite.of_basis
  statement: {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
  proof: by
  cases nonempty_fintype ι
  classical
    refine ⟨⟨Finset.univ.image b, ?_⟩⟩
    simp only [Set.image_univ, Finset.coe_univ, Finset.coe_image, Basis.span_eq]

中文:
定理 模.有限.of_basis
  结论: {R M ι : 类型} [半环 R] [加法交换幺半群 M] [模 R M]
  证明: by
  cases nonempty_fintype ι
  classical
    refine ⟨⟨Finset.univ.image b, ?_⟩⟩
    simp only [Set.image_univ, Finset.coe_univ, Finset.coe_image, Basis.span_eq]

Depends on / 依赖: Basis.span_eq, Finset, Finset.coe_image, Finset.coe_univ, Finset.univ.image, Set.image_univ, classical, coe_image, coe_univ, image_univ, nonempty_fintype, span_eq
-/
theorem Module.Finite.of_basis {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [_root_.Finite ι] (b : Basis ι R M) : Module.Finite R M := by
  cases nonempty_fintype ι
  classical
    refine ⟨⟨Finset.univ.image b, ?_⟩⟩
    simp only [Set.image_univ, Finset.coe_univ, Finset.coe_image, Basis.span_eq]

/--
Instance `Module.Finite.matrix` / 实例 `Module.Finite.matrix`

English:
instance Module.Finite.matrix
  signature: {R ι₁ ι₂ M : Type*}
  body: by
  cases nonempty_fintype ι₁
  cases nonempty_fintype ι₂
exact Module.Finite.of_basis (Free.chooseBasis _ _).matrix _ _

example {ι₁ ι₂ R : Type*} [Semiring R] [Finite ι₁] [Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ R) := inferInstance

中文:
实例 模.有限.matrix
  签名: {R ι₁ ι₂ M : 类型}
  定义体: by
  cases nonempty_fintype ι₁
  cases nonempty_fintype ι₂
exact Module.Finite.of_basis (Free.chooseBasis _ _).matrix _ _

example {ι₁ ι₂ R : Type*} [Semiring R] [Finite ι₁] [Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ R) := inferInstance

Depends on / 依赖: Finite, Free.chooseBasis, Module, Module.Finite.of_basis, chooseBasis, matrix, nonempty_fintype, of_basis
-/
instance Module.Finite.matrix {R ι₁ ι₂ M : Type*}
    [Semiring R] [AddCommMonoid M] [Module R M] [Module.Free R M] [Module.Finite R M]
    [_root_.Finite ι₁] [_root_.Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ M) := by
  cases nonempty_fintype ι₁
  cases nonempty_fintype ι₂
exact Module.Finite.of_basis (Free.chooseBasis _ _).matrix _ _

example {ι₁ ι₂ R : Type*} [Semiring R] [Finite ι₁] [Finite ι₂] :
    Module.Finite R (Matrix ι₁ ι₂ R) := inferInstance
