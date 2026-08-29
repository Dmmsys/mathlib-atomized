/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.SemiringInverse
public import Mathlib.LinearAlgebra.InvariantBasisNumber

/-!
# Invertible matrices over a ring with invariant basis number are square.
-/

public section

section

open Function Matrix LinearMap

variable {R : Type*} [Semiring R]

instance (priority := low) [OrzechProperty R] : IsStablyFiniteRing R :=
  isStablyFiniteRing_iff_injective_of_surjective.mpr fun _ =>
    OrzechProperty.injective_of_surjective_endomorphism

instance (priority := low) [IsStablyFiniteRing R] [Nontrivial R] : RankCondition R where
  le_of_fin_surjective {n m} f hf := by
    by_contra! lt
    let p : (Fin m -> R) ->ₗ[R] Fin n -> R := funLeft R R (Fin.castLE lt.le)
    have hp : Surjective p := funLeft_surjective_of_injective _ _ _ (Fin.castLE_injective lt.le)
    have : Injective p := .of_comp_right
      (Module.End.injective_of_surjective_fin (f := p ∘ₗ f) (hp.comp hf)) hf
    have ⟨⟨i, lt⟩, eq⟩ := injective_comp_right_iff_surjective.mp this ⟨n, lt⟩
    exact lt.ne congr($eq)

/--
theorem `rankCondition_iff_le_of_comp_eq_one` / 定理 `rankCondition_iff_le_of_comp_eq_one`

English:
theorem rankCondition_iff_le_of_comp_eq_one
  statement: RankCondition R ↔ forall n m
  proof: (rankCondition_iff R).trans ⟨fun h _ _ f _ eq => h f (surjective_of_comp_eq_id _ _ eq),
    fun h _ _ _ hf => have ⟨_, eq⟩ := Module.projective_lifting_property _ .id hf; h _ _ _ _ eq⟩

中文:
定理 rankCondition_iff_le_of_comp_eq_one
  结论: RankCondition R ↔ 对任意 n m
  证明: (rankCondition_iff R).trans ⟨fun h _ _ f _ eq => h f (surjective_of_comp_eq_id _ _ eq),
    fun h _ _ _ hf => have ⟨_, eq⟩ := Module.projective_lifting_property _ .id hf; h _ _ _ _ eq⟩

Depends on / 依赖: Module, Module.projective_lifting_property, projective_lifting_property, rankCondition_iff, surjective_of_comp_eq_id
-/
theorem rankCondition_iff_le_of_comp_eq_one : RankCondition R ↔ forall n m
    (f : (Fin n -> R) ->ₗ[R] Fin m -> R) (g : (Fin m -> R) ->ₗ[R] Fin n -> R), f ∘ₗ g = 1 -> m <= n :=
  (rankCondition_iff R).trans ⟨fun h _ _ f _ eq => h f (surjective_of_comp_eq_id _ _ eq),
    fun h _ _ _ hf => have ⟨_, eq⟩ := Module.projective_lifting_property _ .id hf; h _ _ _ _ eq⟩

/--
theorem `rankCondition_iff_matrix` / 定理 `rankCondition_iff_matrix`

English:
theorem rankCondition_iff_matrix
  statement: RankCondition R ↔ forall n m
  proof: by
  simp_rw [rankCondition_iff_le_of_comp_eq_one, ← toLinearMapRight'.toEquiv
.forall_congr_right, LinearEquiv.coe_toEquiv, ← toLinearMapRight'_mul,
    Module.End.one_eq_id, ← toLinearMapRight'_one, toLinearMapRight'.injective.eq_iff]

中文:
定理 rankCondition_iff_matrix
  结论: RankCondition R ↔ 对任意 n m
  证明: by
  simp_rw [rankCondition_iff_le_of_comp_eq_one, ← toLinearMapRight'.toEquiv
.forall_congr_right, LinearEquiv.coe_toEquiv, ← toLinearMapRight'_mul,
    Module.End.one_eq_id, ← toLinearMapRight'_one, toLinearMapRight'.injective.eq_iff]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_toEquiv, Module, Module.End.one_eq_id, _mul, _one, coe_toEquiv, eq_iff, forall_congr_right, injective, injective.eq_iff, one_eq_id, rankCondition_iff_le_of_comp_eq_one, simp_rw, toEquiv, toLinearMapRight
-/
theorem rankCondition_iff_matrix : RankCondition R ↔ forall n m
    (f : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin m) (Fin n) R), g * f = 1 -> m <= n := by
  simp_rw [rankCondition_iff_le_of_comp_eq_one, ← toLinearMapRight'.toEquiv
.forall_congr_right, LinearEquiv.coe_toEquiv, ← toLinearMapRight'_mul,
    Module.End.one_eq_id, ← toLinearMapRight'_one, toLinearMapRight'.injective.eq_iff]

/--
theorem `invariantBasisNumber_iff_matrix` / 定理 `invariantBasisNumber_iff_matrix`

English:
theorem invariantBasisNumber_iff_matrix
  statement: InvariantBasisNumber R ↔ forall n m
  proof: (invariantBasisNumber_iff R).trans .intro (fun h n m f g hfg hgf =>
      h (toLinearEquivRight'OfInv hfg hgf).symm) fun h n m e => h n m (toMatrixRight' e)
    (toMatrixRight' e.symm) (by simp [← toMatrixRight'_comp]) (by simp [← toMatrixRight'_comp])

中文:
定理 invariantBasisNumber_iff_matrix
  结论: 不变基数 R ↔ 对任意 n m
  证明: (invariantBasisNumber_iff R).trans .intro (fun h n m f g hfg hgf =>
      h (toLinearEquivRight'OfInv hfg hgf).symm) fun h n m e => h n m (toMatrixRight' e)
    (toMatrixRight' e.symm) (by simp [← toMatrixRight'_comp]) (by simp [← toMatrixRight'_comp])

Depends on / 依赖: _comp, e.symm, invariantBasisNumber_iff, toLinearEquivRight, toMatrixRight
-/
theorem invariantBasisNumber_iff_matrix : InvariantBasisNumber R ↔ forall n m
    (f : Matrix (Fin n) (Fin m) R) (g : Matrix (Fin m) (Fin n) R), f * g = 1 -> g * f = 1 -> n = m :=
(invariantBasisNumber_iff R).trans .intro (fun h n m f g hfg hgf =>
      h (toLinearEquivRight'OfInv hfg hgf).symm) fun h n m e => h n m (toMatrixRight' e)
    (toMatrixRight' e.symm) (by simp [← toMatrixRight'_comp]) (by simp [← toMatrixRight'_comp])

set_option backward.isDefEq.respectTransparency false in
/--
theorem `MulOpposite.rankCondition_iff` / 定理 `MulOpposite.rankCondition_iff`

English:
theorem MulOpposite.rankCondition_iff
  statement: RankCondition Rᵐᵒᵖ ↔ RankCondition R
  proof: by
  simp_rw [rankCondition_iff_matrix, ← opEquiv.mapMatrix.forall_congr_right,
    ← opEquiv.mapMatrix.symm.injective.eq_iff]
  congr! 2 with n m
refine forall_comm.trans .trans (forall_congr' ?_) (transposeAddEquiv ..).forall_congr_right
  refine fun f => .trans (forall_congr' fun g => ?_) (transp

中文:
定理 MulOpposite.rankCondition_iff
  结论: RankCondition Rᵐᵒᵖ ↔ RankCondition R
  证明: by
  simp_rw [rankCondition_iff_matrix, ← opEquiv.mapMatrix.forall_congr_right,
    ← opEquiv.mapMatrix.symm.injective.eq_iff]
  congr! 2 with n m
refine forall_comm.trans .trans (forall_congr' ?_) (transposeAddEquiv ..).forall_congr_right
  refine fun f => .trans (forall_congr' fun g => ?_) (transp
-/
protected theorem MulOpposite.rankCondition_iff : RankCondition Rᵐᵒᵖ ↔ RankCondition R := by
  simp_rw [rankCondition_iff_matrix, ← opEquiv.mapMatrix.forall_congr_right,
    ← opEquiv.mapMatrix.symm.injective.eq_iff]
  congr! 2 with n m
refine forall_comm.trans .trans (forall_congr' ?_) (transposeAddEquiv ..).forall_congr_right
  refine fun f => .trans (forall_congr' fun g => ?_) (transposeAddEquiv ..).forall_congr_right
  rw [← (transposeAddEquiv ..).injective.eq_iff]
  congrm (?_ = ?_ -> _)
  · ext; simp [map, mul_apply]
  · simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `MulOpposite.invariantBasisNumber_iff` / 定理 `MulOpposite.invariantBasisNumber_iff`

English:
theorem MulOpposite.invariantBasisNumber_iff
  proof: by
  simp_rw [invariantBasisNumber_iff_matrix, ← opEquiv.mapMatrix.forall_congr_right,
    ← opEquiv.mapMatrix.symm.injective.eq_iff]
  congr! 2 with n m
refine forall_comm.trans .trans (forall_congr' ?_) (transposeAddEquiv ..).forall_congr_right
  refine fun f => .trans (forall_congr' fun g => ?_) 

中文:
定理 MulOpposite.invariantBasisNumber_iff
  证明: by
  simp_rw [invariantBasisNumber_iff_matrix, ← opEquiv.mapMatrix.forall_congr_right,
    ← opEquiv.mapMatrix.symm.injective.eq_iff]
  congr! 2 with n m
refine forall_comm.trans .trans (forall_congr' ?_) (transposeAddEquiv ..).forall_congr_right
  refine fun f => .trans (forall_congr' fun g => ?_) 
-/
protected theorem MulOpposite.invariantBasisNumber_iff :
    InvariantBasisNumber Rᵐᵒᵖ ↔ InvariantBasisNumber R := by
  simp_rw [invariantBasisNumber_iff_matrix, ← opEquiv.mapMatrix.forall_congr_right,
    ← opEquiv.mapMatrix.symm.injective.eq_iff]
  congr! 2 with n m
refine forall_comm.trans .trans (forall_congr' ?_) (transposeAddEquiv ..).forall_congr_right
  refine fun f => .trans (forall_congr' fun g => ?_) (transposeAddEquiv ..).forall_congr_right
  rw [← (transposeAddEquiv ..).injective.eq_iff]; rw [← (transposeAddEquiv (Fin m) ..).injective.eq_iff]
  congrm (?_ = ?_ -> ?_ = ?_ -> _)
  iterate 2 ext; simp [map, mul_apply]; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [RankCondition
  signature: R] : RankCondition Rᵐᵒᵖ
  body: MulOpposite.rankCondition_iff.mpr ‹_›

中文:
实例 [RankCondition
  签名: R] : RankCondition Rᵐᵒᵖ
  定义体: MulOpposite.rankCondition_iff.mpr ‹_›

Depends on / 依赖: MulOpposite, MulOpposite.rankCondition_iff.mpr, rankCondition_iff
-/
instance [RankCondition R] : RankCondition Rᵐᵒᵖ := MulOpposite.rankCondition_iff.mpr ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [InvariantBasisNumber
  signature: R] : InvariantBasisNumber Rᵐᵒᵖ
  body: MulOpposite.invariantBasisNumber_iff.mpr ‹_›

中文:
实例 [不变基数
  签名: R] : 不变基数 Rᵐᵒᵖ
  定义体: MulOpposite.invariantBasisNumber_iff.mpr ‹_›

Depends on / 依赖: MulOpposite, MulOpposite.invariantBasisNumber_iff.mpr, invariantBasisNumber_iff
-/
instance [InvariantBasisNumber R] : InvariantBasisNumber Rᵐᵒᵖ :=
  MulOpposite.invariantBasisNumber_iff.mpr ‹_›

end

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
variable {R : Type*} [Semiring R] [InvariantBasisNumber R]

/--
theorem `Matrix.square_of_invertible` / 定理 `Matrix.square_of_invertible`

English:
theorem Matrix.square_of_invertible
  statement: (M : Matrix n m R) (N : Matrix m n R) (h : M * N = 1)
  proof: card_eq_of_linearEquiv R (Matrix.toLinearEquivRight'OfInv h' h)

中文:
定理 矩阵.square_of_invertible
  结论: (M : 矩阵 n m R) (N : 矩阵 m n R) (h : M * N = 1)
  证明: card_eq_of_linearEquiv R (Matrix.toLinearEquivRight'OfInv h' h)

Depends on / 依赖: Matrix, Matrix.toLinearEquivRight, card_eq_of_linearEquiv, toLinearEquivRight
-/
theorem Matrix.square_of_invertible (M : Matrix n m R) (N : Matrix m n R) (h : M * N = 1)
    (h' : N * M = 1) : Fintype.card n = Fintype.card m :=
  card_eq_of_linearEquiv R (Matrix.toLinearEquivRight'OfInv h' h)

open Function in
/-- Nontrivial commutative semirings `R` satisfy the rank condition.

If `R` is moreover a ring, then it satisfies the strong rank condition, see
`commRing_strongRankCondition`. It is unclear whether this generalizes to semirings. -/
instance (priority := 100) rankCondition_of_nontrivial_of_commSemiring {R : Type*}
    [CommSemiring R] [Nontrivial R] : RankCondition R := inferInstance
