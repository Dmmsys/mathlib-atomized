/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang, Andrew Yang
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.Algebra.DirectSum.Decomposition

/-!
# Decomposition of the identity of a semiring into orthogonal idempotents

In this file we show that if a semiring `R` can be decomposed into a direct sum
of (left) ideals `R = V₁ ⊕ V₂ ⊕ ⋯ ⊕ Vₙ` then in the corresponding decomposition
`1 = e₁ + e₂ + ⋯ + eₙ` with `eᵢ ∈ Vᵢ`, each `eᵢ` is an idempotent and the
`eᵢ`'s form a family of complete orthogonal idempotents.
-/

@[expose] public section

namespace DirectSum

section OrthogonalIdempotents

variable {R I : Type*} [Semiring R] [DecidableEq I] (V : I -> Ideal R) [Decomposition V]

/--
Definition of `idempotent` / `idempotent` 的定义

English:
definition idempotent
  signature: (i : I)
  body: decompose V 1 i

中文:
定义 idempotent
  签名: (i : I)
  定义体: decompose V 1 i

Depends on / 依赖: decompose
-/
def idempotent (i : I) : R :=
  decompose V 1 i

/--
lemma `decompose_eq_mul_idempotent` / 引理 `decompose_eq_mul_idempotent`

English:
lemma decompose_eq_mul_idempotent
  given: (x : R) (i : I)
  statement: decompose V x i = x * idempotent V i
  proof: by
  rw [← smul_eq_mul (a := x)]; rw [idempotent]; rw [← Submodule.coe_smul]; rw [← smul_apply]; rw [← decompose_smul]; rw [smul_eq_mul]; rw [mul_one]

中文:
引理 decompose_eq_mul_idempotent
  条件: (x : R) (i : I)
  结论: decompose V x i = x * idempotent V i
  证明: by
  rw [← smul_eq_mul (a := x)]; rw [idempotent]; rw [← Submodule.coe_smul]; rw [← smul_apply]; rw [← decompose_smul]; rw [smul_eq_mul]; rw [mul_one]

Depends on / 依赖: Submodule, Submodule.coe_smul, coe_smul, decompose_smul, idempotent, mul_one, smul_apply, smul_eq_mul
-/
lemma decompose_eq_mul_idempotent (x : R) (i : I) : decompose V x i = x * idempotent V i := by
  rw [← smul_eq_mul (a := x)]; rw [idempotent]; rw [← Submodule.coe_smul]; rw [← smul_apply]; rw [← decompose_smul]; rw [smul_eq_mul]; rw [mul_one]

/--
lemma `isIdempotentElem_idempotent` / 引理 `isIdempotentElem_idempotent`

English:
lemma isIdempotentElem_idempotent
  given: (i : I)
  statement: IsIdempotentElem (idempotent V i : R)
  proof: by
  rw [IsIdempotentElem]; rw [← decompose_eq_mul_idempotent]; rw [idempotent]; rw [decompose_coe]; rw [of_eq_same]

中文:
引理 isIdempotentElem_idempotent
  条件: (i : I)
  结论: IsIdempotentElem (idempotent V i : R)
  证明: by
  rw [IsIdempotentElem]; rw [← decompose_eq_mul_idempotent]; rw [idempotent]; rw [decompose_coe]; rw [of_eq_same]

Depends on / 依赖: IsIdempotentElem, decompose_coe, decompose_eq_mul_idempotent, idempotent, of_eq_same
-/
lemma isIdempotentElem_idempotent (i : I) : IsIdempotentElem (idempotent V i : R) := by
  rw [IsIdempotentElem]; rw [← decompose_eq_mul_idempotent]; rw [idempotent]; rw [decompose_coe]; rw [of_eq_same]

/--
theorem `completeOrthogonalIdempotents_idempotent` / 定理 `completeOrthogonalIdempotents_idempotent`

English:
theorem completeOrthogonalIdempotents_idempotent
  given: [Fintype I]
  proof: isIdempotentElem_idempotent V
  ortho i j hij := by
    simp only
    rw [← decompose_eq_mul_idempotent]; rw [idempotent]; rw [decompose_coe]; rw [of_eq_of_ne (h := hij.symm)]; rw [Submodule.coe_zero]
  complete := by
    apply (decompose V).injective
    refine DFunLike.ext _ _ fun i => ?_
    rw [decompose_sum]; rw [DFinsupp.finsetSum_apply]
    simp [idempotent, of_apply]

中文:
定理 completeOrthogonalIdempotents_idempotent
  条件: [有限类型 I]
  证明: isIdempotentElem_idempotent V
  ortho i j hij := by
    simp only
    rw [← decompose_eq_mul_idempotent]; rw [idempotent]; rw [decompose_coe]; rw [of_eq_of_ne (h := hij.symm)]; rw [Submodule.coe_zero]
  complete := by
    apply (decompose V).injective
    refine DFunLike.ext _ _ fun i => ?_
    rw [decompose_sum]; rw [DFinsupp.finsetSum_apply]
    simp [idempotent, of_apply]

Depends on / 依赖: isIdempotentElem_idempotent
-/
theorem completeOrthogonalIdempotents_idempotent [Fintype I] :
    CompleteOrthogonalIdempotents (idempotent V) where
  idem := isIdempotentElem_idempotent V
  ortho i j hij := by
    simp only
    rw [← decompose_eq_mul_idempotent]; rw [idempotent]; rw [decompose_coe]; rw [of_eq_of_ne (h := hij.symm)]; rw [Submodule.coe_zero]
  complete := by
    apply (decompose V).injective
    refine DFunLike.ext _ _ fun i => ?_
    rw [decompose_sum]; rw [DFinsupp.finsetSum_apply]
    simp [idempotent, of_apply]

end OrthogonalIdempotents

end DirectSum
