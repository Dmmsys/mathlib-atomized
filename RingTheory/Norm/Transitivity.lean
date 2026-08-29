/-
Copyright (c) 2024 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.FieldTheory.Galois.Basic

/-!
# Transitivity of algebra norm

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## References

* [silvester2000] Silvester, *Determinants of Block Matrices*, The Mathematical Gazette (2000).

-/

@[expose] public section

variable {R S A n m : Type*} [CommRing R] [CommRing S]
variable (M : Matrix m m S) [DecidableEq m] [DecidableEq n] (k : m)
open Matrix Polynomial

namespace Algebra.Norm.Transitivity

/--
Definition of `auxMat` / `auxMat` 的定义

English:
definition auxMat
  signature: : Matrix m m S
  body: of fun i j =>
    if j = k then
      if i = k then 1 else 0
    else if i = k then -M k j
    else if i = j then M k k
    else 0

中文:
定义 auxMat
  签名: : 矩阵 m m S
  定义体: of fun i j =>
    if j = k then
      if i = k then 1 else 0
    else if i = k then -M k j
    else if i = j then M k k
    else 0
-/
def auxMat : Matrix m m S :=
  of fun i j =>
    if j = k then
      if i = k then 1 else 0
    else if i = k then -M k j
    else if i = j then M k k
    else 0

/--
lemma `auxMat_blockTriangular` / 引理 `auxMat_blockTriangular`

English:
lemma auxMat_blockTriangular
  statement: (auxMat M k).BlockTriangular (· != k)
  proof: fun i j lt => by
    simp_rw [lt_iff_not_ge, le_Prop_eq, Classical.not_imp, not_not] at lt
    rw [auxMat]; rw [of_apply]; rw [if_pos lt.2]; rw [if_neg lt.1]

中文:
引理 auxMat_blockTriangular
  结论: (auxMat M k).BlockTriangular (· != k)
  证明: fun i j lt => by
    simp_rw [lt_iff_not_ge, le_Prop_eq, Classical.not_imp, not_not] at lt
    rw [auxMat]; rw [of_apply]; rw [if_pos lt.2]; rw [if_neg lt.1]

Depends on / 依赖: Classical, Classical.not_imp, auxMat, if_neg, if_pos, le_Prop_eq, lt_iff_not_ge, not_imp, not_not, of_apply, simp_rw
-/
lemma auxMat_blockTriangular : (auxMat M k).BlockTriangular (· != k) :=
  fun i j lt => by
    simp_rw [lt_iff_not_ge, le_Prop_eq, Classical.not_imp, not_not] at lt
    rw [auxMat]; rw [of_apply]; rw [if_pos lt.2]; rw [if_neg lt.1]

/--
lemma `auxMat_toSquareBlock_ne` / 引理 `auxMat_toSquareBlock_ne`

English:
lemma auxMat_toSquareBlock_ne
  statement: (auxMat M k).toSquareBlock (· != k) True = M k k • 1
  proof: by
  ext i j
  simp [auxMat, toSquareBlock_def, if_neg (of_eq_true i.2), if_neg (of_eq_true j.2),
    Matrix.one_apply, Subtype.ext_iff]

中文:
引理 auxMat_toSquareBlock_ne
  结论: (auxMat M k).toSquareBlock (· != k) 真 = M k k • 1
  证明: by
  ext i j
  simp [auxMat, toSquareBlock_def, if_neg (of_eq_true i.2), if_neg (of_eq_true j.2),
    Matrix.one_apply, Subtype.ext_iff]

Depends on / 依赖: Matrix, Matrix.one_apply, Subtype, Subtype.ext_iff, auxMat, ext_iff, if_neg, of_eq_true, one_apply, toSquareBlock_def
-/
lemma auxMat_toSquareBlock_ne : (auxMat M k).toSquareBlock (· != k) True = M k k • 1 := by
  ext i j
  simp [auxMat, toSquareBlock_def, if_neg (of_eq_true i.2), if_neg (of_eq_true j.2),
    Matrix.one_apply, Subtype.ext_iff]

/--
lemma `auxMat_toSquareBlock_eq` / 引理 `auxMat_toSquareBlock_eq`

English:
lemma auxMat_toSquareBlock_eq
  statement: (auxMat M k).toSquareBlock (· != k) False = 1
  proof: by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [eq_iff_iff]; rw [iff_false]; rw [not_not] at hi hj
  simp [auxMat, toSquareBlock_def, if_pos hi, if_pos hj, Matrix.one_apply, if_pos (hj ▸ hi)]

中文:
引理 auxMat_toSquareBlock_eq
  结论: (auxMat M k).toSquareBlock (· != k) 假 = 1
  证明: by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [eq_iff_iff]; rw [iff_false]; rw [not_not] at hi hj
  simp [auxMat, toSquareBlock_def, if_pos hi, if_pos hj, Matrix.one_apply, if_pos (hj ▸ hi)]

Depends on / 依赖: Matrix, Matrix.one_apply, auxMat, eq_iff_iff, if_pos, iff_false, not_not, one_apply, toSquareBlock_def
-/
lemma auxMat_toSquareBlock_eq : (auxMat M k).toSquareBlock (· != k) False = 1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [eq_iff_iff]; rw [iff_false]; rw [not_not] at hi hj
  simp [auxMat, toSquareBlock_def, if_pos hi, if_pos hj, Matrix.one_apply, if_pos (hj ▸ hi)]

variable [Fintype m]

/--
lemma `mul_auxMat_blockTriangular` / 引理 `mul_auxMat_blockTriangular`

English:
lemma mul_auxMat_blockTriangular
  statement: (M * auxMat M k).BlockTriangular (· = k)
  proof: fun i j lt => by
    simp_rw [lt_iff_not_ge, le_Prop_eq, Classical.not_imp] at lt
    simp_rw [Matrix.mul_apply, auxMat, of_apply, if_neg lt.2, mul_ite, mul_neg, mul_zero]
    rw [Finset.sum_ite]; rw [Finset.filter_eq']; rw [if_pos (Finset.mem_univ _)]; rw [Finset.sum_singleton]; rw [Finset.sum_ite_

中文:
引理 mul_auxMat_blockTriangular
  结论: (M * auxMat M k).BlockTriangular (· = k)
  证明: fun i j lt => by
    simp_rw [lt_iff_not_ge, le_Prop_eq, Classical.not_imp] at lt
    simp_rw [Matrix.mul_apply, auxMat, of_apply, if_neg lt.2, mul_ite, mul_neg, mul_zero]
    rw [Finset.sum_ite]; rw [Finset.filter_eq']; rw [if_pos (Finset.mem_univ _)]; rw [Finset.sum_singleton]; rw [Finset.sum_ite_

Depends on / 依赖: Classical, Classical.not_imp, Finset, Finset.filter_eq, Finset.mem_filter.mpr, Finset.mem_univ, Finset.sum_ite, Finset.sum_ite_eq, Finset.sum_singleton, Matrix, Matrix.mul_apply, auxMat, filter_eq, if_neg, if_pos, le_Prop_eq, lt_iff_not_ge, mem_filter, mem_univ, mul_apply
-/
lemma mul_auxMat_blockTriangular : (M * auxMat M k).BlockTriangular (· = k) :=
  fun i j lt => by
    simp_rw [lt_iff_not_ge, le_Prop_eq, Classical.not_imp] at lt
    simp_rw [Matrix.mul_apply, auxMat, of_apply, if_neg lt.2, mul_ite, mul_neg, mul_zero]
    rw [Finset.sum_ite]; rw [Finset.filter_eq']; rw [if_pos (Finset.mem_univ _)]; rw [Finset.sum_singleton]; rw [Finset.sum_ite_eq']; rw [if_pos]; rw [lt.1]; rw [mul_comm]; rw [neg_add_cancel]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt.2⟩

/--
lemma `mul_auxMat_corner` / 引理 `mul_auxMat_corner`

English:
lemma mul_auxMat_corner
  statement: (M * auxMat M k) k k = M k k
  proof: by simp [Matrix.mul_apply, auxMat]

中文:
引理 mul_auxMat_corner
  结论: (M * auxMat M k) k k = M k k
  证明: by simp [Matrix.mul_apply, auxMat]

Depends on / 依赖: Matrix, Matrix.mul_apply, auxMat, mul_apply
-/
lemma mul_auxMat_corner : (M * auxMat M k) k k = M k k := by simp [Matrix.mul_apply, auxMat]

/--
lemma `mul_auxMat_toSquareBlock_eq` / 引理 `mul_auxMat_toSquareBlock_eq`

English:
lemma mul_auxMat_toSquareBlock_eq
  proof: by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [eq_iff_iff]; rw [iff_true] at hi hj
  simp [toSquareBlock_def, hi, hj, mul_auxMat_corner]

中文:
引理 mul_auxMat_toSquareBlock_eq
  证明: by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [eq_iff_iff]; rw [iff_true] at hi hj
  simp [toSquareBlock_def, hi, hj, mul_auxMat_corner]

Depends on / 依赖: eq_iff_iff, iff_true, mul_auxMat_corner, toSquareBlock_def
-/
lemma mul_auxMat_toSquareBlock_eq :
    (M * auxMat M k).toSquareBlock (· = k) True = M k k • 1 := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  rw [eq_iff_iff]; rw [iff_true] at hi hj
  simp [toSquareBlock_def, hi, hj, mul_auxMat_corner]

set_option quotPrecheck false in
/-- The upper-left block of `M * aux M k`. -/
scoped notation "mulAuxMatBlock" => (M * auxMat M k).toSquareBlock (· = k) False

/--
lemma `det_mul_corner_pow` / 引理 `det_mul_corner_pow`

English:
lemma det_mul_corner_pow
  proof: by
  trans (M * auxMat M k).det
  · simp [det_mul, (auxMat_blockTriangular M k).det_fintype,
      auxMat_toSquareBlock_ne, auxMat_toSquareBlock_eq]
  rw [(mul_auxMat_blockTriangular M k).det_fintype]; rw [Fintype.prod_Prop]; rw [mul_auxMat_toSquareBlock_eq]
  simp_rw [det_smul_of_tower, eq_iff_iff,

中文:
引理 det_mul_corner_pow
  证明: by
  trans (M * auxMat M k).det
  · simp [det_mul, (auxMat_blockTriangular M k).det_fintype,
      auxMat_toSquareBlock_ne, auxMat_toSquareBlock_eq]
  rw [(mul_auxMat_blockTriangular M k).det_fintype]; rw [Fintype.prod_Prop]; rw [mul_auxMat_toSquareBlock_eq]
  simp_rw [det_smul_of_tower, eq_iff_iff,

Depends on / 依赖: Fintype, Fintype.card_unique, Fintype.prod_Prop, auxMat, auxMat_blockTriangular, auxMat_toSquareBlock_eq, auxMat_toSquareBlock_ne, card_unique, det_fintype, det_mul, det_one, det_smul_of_tower, eq_iff_iff, iff_true, mul_auxMat_blockTriangular, mul_auxMat_toSquareBlock_eq, mul_one, pow_one, prod_Prop, simp_rw
-/
lemma det_mul_corner_pow :
    M.det * M k k ^ (Fintype.card m - 1) = M k k * (mulAuxMatBlock).det := by
  trans (M * auxMat M k).det
  · simp [det_mul, (auxMat_blockTriangular M k).det_fintype,
      auxMat_toSquareBlock_ne, auxMat_toSquareBlock_eq]
  rw [(mul_auxMat_blockTriangular M k).det_fintype]; rw [Fintype.prod_Prop]; rw [mul_auxMat_toSquareBlock_eq]
  simp_rw [det_smul_of_tower, eq_iff_iff, iff_true, Fintype.card_unique,
    pow_one, det_one, smul_eq_mul, mul_one]
  -- `Decidable (P = Q)` diamond induced by `Prop.linearOrder`, which is classical, when `P` and `Q`
  -- are themselves decidable.
  convert! rfl

/--
Definition of `cornerAddX` / `cornerAddX` 的定义

English:
definition cornerAddX
  signature: : Matrix m m S[X]
  body: (diagonal fun i => if i = k then X else 0) + M.map C

中文:
定义 cornerAddX
  签名: : 矩阵 m m S[X]
  定义体: (diagonal fun i => if i = k then X else 0) + M.map C

Depends on / 依赖: M.map, diagonal
-/
noncomputable def cornerAddX : Matrix m m S[X] :=
  (diagonal fun i => if i = k then X else 0) + M.map C

variable [Fintype n] (f : S ->+* Matrix n n R)

omit [Fintype m] in
/--
lemma `polyToMatrix_cornerAddX` / 引理 `polyToMatrix_cornerAddX`

English:
lemma polyToMatrix_cornerAddX
  proof: by
  simp [cornerAddX, Matrix.add_apply, charmatrix,
    RingHom.polyToMatrix, -AlgEquiv.symm_toRingEquiv, map_neg]

中文:
引理 polyToMatrix_cornerAddX
  证明: by
  simp [cornerAddX, Matrix.add_apply, charmatrix,
    RingHom.polyToMatrix, -AlgEquiv.symm_toRingEquiv, map_neg]

Depends on / 依赖: AlgEquiv, AlgEquiv.symm_toRingEquiv, Matrix, Matrix.add_apply, RingHom, RingHom.polyToMatrix, add_apply, charmatrix, cornerAddX, map_neg, polyToMatrix, symm_toRingEquiv
-/
lemma polyToMatrix_cornerAddX :
    f.polyToMatrix (cornerAddX M k k k) = (-f (M k k)).charmatrix := by
  simp [cornerAddX, Matrix.add_apply, charmatrix,
    RingHom.polyToMatrix, -AlgEquiv.symm_toRingEquiv, map_neg]

/--
lemma `eval_zero_det_det` / 引理 `eval_zero_det_det`

English:
lemma eval_zero_det_det
  statement: eval 0 (f.polyToMatrix (cornerAddX M k).det).det = (f M.det).det
  proof: by
  rw [← coe_evalRingHom]; rw [RingHom.map_det]; rw [← RingHom.comp_apply]; rw [evalRingHom_mapMatrix_comp_polyToMatrix]; rw [f.comp_apply]; rw [RingHom.map_det]
  congr; ext; simp [cornerAddX, diagonal, apply_ite]

中文:
引理 eval_zero_det_det
  结论: eval 0 (f.polyToMatrix (cornerAddX M k).det).det = (f M.det).det
  证明: by
  rw [← coe_evalRingHom]; rw [RingHom.map_det]; rw [← RingHom.comp_apply]; rw [evalRingHom_mapMatrix_comp_polyToMatrix]; rw [f.comp_apply]; rw [RingHom.map_det]
  congr; ext; simp [cornerAddX, diagonal, apply_ite]

Depends on / 依赖: RingHom, RingHom.comp_apply, RingHom.map_det, apply_ite, coe_evalRingHom, comp_apply, cornerAddX, diagonal, evalRingHom_mapMatrix_comp_polyToMatrix, f.comp_apply, map_det
-/
lemma eval_zero_det_det : eval 0 (f.polyToMatrix (cornerAddX M k).det).det = (f M.det).det := by
  rw [← coe_evalRingHom]; rw [RingHom.map_det]; rw [← RingHom.comp_apply]; rw [evalRingHom_mapMatrix_comp_polyToMatrix]; rw [f.comp_apply]; rw [RingHom.map_det]
  congr; ext; simp [cornerAddX, diagonal, apply_ite]

/--
lemma `eval_zero_comp_det` / 引理 `eval_zero_comp_det`

English:
lemma eval_zero_comp_det
  proof: by
  simp_rw [← coe_evalRingHom, RingHom.map_det, ← compRingEquiv_apply, ← RingEquiv.coe_toRingHom,
    ← RingHom.mapMatrix_apply, ← RingHom.comp_apply, ← RingHom.comp_assoc,
    evalRingHom_mapMatrix_comp_compRingEquiv, RingHom.comp_assoc, RingHom.mapMatrix_comp,
    evalRingHom_mapMatrix_comp_poly

中文:
引理 eval_zero_comp_det
  证明: by
  simp_rw [← coe_evalRingHom, RingHom.map_det, ← compRingEquiv_apply, ← RingEquiv.coe_toRingHom,
    ← RingHom.mapMatrix_apply, ← RingHom.comp_apply, ← RingHom.comp_assoc,
    evalRingHom_mapMatrix_comp_compRingEquiv, RingHom.comp_assoc, RingHom.mapMatrix_comp,
    evalRingHom_mapMatrix_comp_poly

Depends on / 依赖: RingEquiv, RingEquiv.coe_toRingHom, RingHom, RingHom.comp_apply, RingHom.comp_assoc, RingHom.mapMatrix_apply, RingHom.mapMatrix_comp, RingHom.map_det, apply_ite, coe_evalRingHom, coe_toRingHom, compRingEquiv_apply, comp_apply, comp_assoc, cornerAddX, diagonal, evalRingHom_mapMatrix_comp_compRingEquiv, evalRingHom_mapMatrix_comp_polyToMatrix, mapMatrix_apply, mapMatrix_comp
-/
lemma eval_zero_comp_det :
    eval 0 (comp m m n n R[X] <| (cornerAddX M k).map f.polyToMatrix).det =
      (comp m m n n R <| M.map f).det := by
  simp_rw [← coe_evalRingHom, RingHom.map_det, ← compRingEquiv_apply, ← RingEquiv.coe_toRingHom,
    ← RingHom.mapMatrix_apply, ← RingHom.comp_apply, ← RingHom.comp_assoc,
    evalRingHom_mapMatrix_comp_compRingEquiv, RingHom.comp_assoc, RingHom.mapMatrix_comp,
    evalRingHom_mapMatrix_comp_polyToMatrix, ← RingHom.mapMatrix_comp, RingHom.comp_apply]
  congr with i j
  simp [cornerAddX, diagonal, apply_ite]

/--
theorem `comp_det_mul_pow` / 定理 `comp_det_mul_pow`

English:
theorem comp_det_mul_pow
  proof: by
  trans (((M * auxMat M k).map f).comp m m n n R).det
  · simp_rw [← f.mapMatrix_apply, ← compRingEquiv_apply, map_mul, det_mul, f.mapMatrix_apply,
      compRingEquiv_apply, ((auxMat_blockTriangular M k).map f).comp.det_fintype, Fintype.prod_Prop,
      comp_toSquareBlock (b := (· != k)), det_re

中文:
定理 comp_det_mul_pow
  证明: by
  trans (((M * auxMat M k).map f).comp m m n n R).det
  · simp_rw [← f.mapMatrix_apply, ← compRingEquiv_apply, map_mul, det_mul, f.mapMatrix_apply,
      compRingEquiv_apply, ((auxMat_blockTriangular M k).map f).comp.det_fintype, Fintype.prod_Prop,
      comp_toSquareBlock (b := (· != k)), det_re

Depends on / 依赖: Fintype, Fintype.prod_Prop, auxMat, auxMat_blockTriangular, auxMat_toSquareBlock_eq, auxMat_toSquareBlock_ne, comp.det_fintype, compRingEquiv_apply, comp_diagonal, comp_toSquareBlock, det_fintype, det_mul, det_reindex_self, diagonal_map, diagonal_one, f.mapMatrix_apply, mapMatrix_apply, map_mul, map_toSquareBlock, map_zero
-/
theorem comp_det_mul_pow :
    ((M.map f).comp m m n n R).det * (f (M k k)).det ^ (Fintype.card m - 1) =
      (f (M k k)).det * (((mulAuxMatBlock).map f).comp _ _ n n R).det := by
  trans (((M * auxMat M k).map f).comp m m n n R).det
  · simp_rw [← f.mapMatrix_apply, ← compRingEquiv_apply, map_mul, det_mul, f.mapMatrix_apply,
      compRingEquiv_apply, ((auxMat_blockTriangular M k).map f).comp.det_fintype, Fintype.prod_Prop,
      comp_toSquareBlock (b := (· != k)), det_reindex_self, map_toSquareBlock,
      auxMat_toSquareBlock_eq, auxMat_toSquareBlock_ne, smul_one_eq_diagonal, ← diagonal_one,
      diagonal_map (map_zero _), comp_diagonal, det_reindex_self]
    simp
  · simp_rw [((mul_auxMat_blockTriangular M k).map f).comp.det_fintype, Fintype.prod_Prop,
      comp_toSquareBlock (b := (· = k)), det_reindex_self, map_toSquareBlock,
      mul_auxMat_toSquareBlock_eq, smul_one_eq_diagonal,
      diagonal_map (map_zero _), comp_diagonal, det_reindex_self]
    simp

variable {M f} in
/--
lemma `det_det_aux` / 引理 `det_det_aux`

English:
lemma det_det_aux
  proof: by
  rw [sub_mul]; rw [comp_det_mul_pow]; rw [← det_pow]; rw [← map_pow]; rw [← det_mul]; rw [← map_mul]; rw [det_mul_corner_pow]; rw [map_mul]; rw [det_mul]; rw [ih]; rw [sub_self]

中文:
引理 det_det_aux
  证明: by
  rw [sub_mul]; rw [comp_det_mul_pow]; rw [← det_pow]; rw [← map_pow]; rw [← det_mul]; rw [← map_mul]; rw [det_mul_corner_pow]; rw [map_mul]; rw [det_mul]; rw [ih]; rw [sub_self]

Depends on / 依赖: comp_det_mul_pow, det_mul, det_mul_corner_pow, det_pow, map_mul, map_pow, sub_mul, sub_self
-/
lemma det_det_aux
    (ih : forall M, (f (det M)).det = ((M.map f).comp {a // (a = k) = False} _ n n R).det) :
    ((f M.det).det - ((M.map f).comp m m n n R).det) *
      (f (M k k)).det ^ (Fintype.card m - 1) = 0 := by
  rw [sub_mul]; rw [comp_det_mul_pow]; rw [← det_pow]; rw [← map_pow]; rw [← det_mul]; rw [← map_mul]; rw [det_mul_corner_pow]; rw [map_mul]; rw [det_mul]; rw [ih]; rw [sub_self]

end Algebra.Norm.Transitivity

open Algebra.Norm.Transitivity

/--
theorem `Matrix.det_det` / 定理 `Matrix.det_det`

English:
theorem Matrix.det_det
  given: [Fintype m] [Fintype n] (f : S ->+* Matrix n n R)
  proof: by
  induction l : Fintype.card m generalizing R S m with
  | zero =>
    rw [Fintype.card_eq_zero_iff] at l
    simp_rw [Matrix.det_isEmpty, map_one, det_one]
  | succ l ih =>
    have ⟨k⟩ := Fintype.card_pos_iff.mp (Nat.lt_of_sub_eq_succ l)
    let f' := f.polyToMatrix
    let M' := cornerAddX M k

中文:
定理 矩阵.det_det
  条件: [有限类型 m] [有限类型 n] (f : S ->+* 矩阵 n n R)
  证明: by
  induction l : Fintype.card m generalizing R S m with
  | zero =>
    rw [Fintype.card_eq_zero_iff] at l
    simp_rw [Matrix.det_isEmpty, map_one, det_one]
  | succ l ih =>
    have ⟨k⟩ := Fintype.card_pos_iff.mp (Nat.lt_of_sub_eq_succ l)
    let f' := f.polyToMatrix
    let M' := cornerAddX M k

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_eq_zero_iff, Fintype.card_pos_iff.mp, Fintype.card_subtype_compl, Fintype.card_u, Matrix, Matrix.det_isEmpty, Nat.lt_of_sub_eq_succ, card_eq_zero_iff, card_pos_iff, card_subtype_compl, card_u, cornerAddX, det_det_aux, det_isEmpty, det_one, f.polyToMatrix, generalizing, lt_of_sub_eq_succ
-/
theorem Matrix.det_det [Fintype m] [Fintype n] (f : S ->+* Matrix n n R) :
    (f M.det).det = ((M.map f).comp m m n n R).det := by
  induction l : Fintype.card m generalizing R S m with
  | zero =>
    rw [Fintype.card_eq_zero_iff] at l
    simp_rw [Matrix.det_isEmpty, map_one, det_one]
  | succ l ih =>
    have ⟨k⟩ := Fintype.card_pos_iff.mp (Nat.lt_of_sub_eq_succ l)
    let f' := f.polyToMatrix
    let M' := cornerAddX M k
    have : (f' M'.det).det = ((M'.map f').comp m m n n R[X]).det := by
refine sub_eq_zero.mp mem_nonZeroDivisors_iff_right.mp
        (pow_mem ?_ _) _ (det_det_aux k fun M => ih _ _ <| by
          grind [Fintype.card_subtype_compl, Fintype.card_unique])
      rw [polyToMatrix_cornerAddX]; rw [← charpoly]
      exact (Matrix.charpoly_monic _).mem_nonZeroDivisors
    rw [← eval_zero_det_det]; rw [congr_arg (eval 0) this]; rw [eval_zero_comp_det]

variable [Algebra R S] [Module.Free R S]

/--
theorem `LinearMap.det_restrictScalars` / 定理 `LinearMap.det_restrictScalars`

English:
theorem LinearMap.det_restrictScalars
  statement: [AddCommGroup A] [Module R A] [Module S A]
  proof: by
  classical
  nontriviality R
  nontriviality A
  have := Module.nontrivial S A
  let ⟨ιS, bS⟩ := Module.Free.exists_basis (R := R) (M := S)
  let ⟨ιA, bA⟩ := Module.Free.exists_basis (R := S) (M := A)
  have := bS.index_nonempty
  have := bA.index_nonempty
  cases fintypeOrInfinite ιS; swap
  · 

中文:
定理 线性映射.det_restrictScalars
  结论: [加法交换群 A] [模 R A] [模 S A]
  证明: by
  classical
  nontriviality R
  nontriviality A
  have := Module.nontrivial S A
  let ⟨ιS, bS⟩ := Module.Free.exists_basis (R := R) (M := S)
  let ⟨ιA, bA⟩ := Module.Free.exists_basis (R := S) (M := A)
  have := bS.index_nonempty
  have := bA.index_nonempty
  cases fintypeOrInfinite ιS; swap
  · 

Depends on / 依赖: Algebra, Algebra.norm_eq_one_of_not_module_finite, Module, Module.Free.exists_basis, Module.nontrivial, Module.not_finite_of_infinite_basis, bA.index_nonempty, bS.index_nonempty, bS.smulTower, classical, det_e, det_eq_one_of_not_module_finite, exists_basis, fintypeOrInfinite, index_nonempty, nontrivial, nontriviality, norm_eq_one_of_not_module_finite, not_finite_of_infinite_basis, smulTower
-/
theorem LinearMap.det_restrictScalars [AddCommGroup A] [Module R A] [Module S A]
    [IsScalarTower R S A] [Module.Free S A] {f : A ->ₗ[S] A} :
    (f.restrictScalars R).det = Algebra.norm R f.det := by
  classical
  nontriviality R
  nontriviality A
  have := Module.nontrivial S A
  let ⟨ιS, bS⟩ := Module.Free.exists_basis (R := R) (M := S)
  let ⟨ιA, bA⟩ := Module.Free.exists_basis (R := S) (M := A)
  have := bS.index_nonempty
  have := bA.index_nonempty
  cases fintypeOrInfinite ιS; swap
  · rw [Algebra.norm_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis bS),
      det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis (bS.smulTower bA))]
  cases fintypeOrInfinite ιA; swap
  · rw [det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis bA), map_one,
      det_eq_one_of_not_module_finite (Module.not_finite_of_infinite_basis (bS.smulTower bA))]
  rw [Algebra.norm_eq_matrix_det bS]; rw [← AlgHom.coe_toRingHom]; rw [← det_toMatrix bA]; rw [det_det]; rw [← det_toMatrix (bS.smulTower' bA)]; rw [restrictScalars_toMatrix]; rw [RingHom.coe_coe]

/--
theorem `Algebra.norm_norm` / 定理 `Algebra.norm_norm`

English:
theorem Algebra.norm_norm
  statement: {A} [Ring A] [Algebra R A] [Algebra S A]
  proof: by
  rw [norm_apply S]; rw [norm_apply R a]; rw [← LinearMap.det_restrictScalars]; rfl

中文:
定理 代数.norm_norm
  结论: {A} [环 A] [代数 R A] [代数 S A]
  证明: by
  rw [norm_apply S]; rw [norm_apply R a]; rw [← LinearMap.det_restrictScalars]; rfl

Depends on / 依赖: LinearMap, LinearMap.det_restrictScalars, det_restrictScalars, norm_apply
-/
theorem Algebra.norm_norm {A} [Ring A] [Algebra R A] [Algebra S A]
    [IsScalarTower R S A] [Module.Free S A] {a : A} :
    norm R (norm S a) = norm R a := by
  rw [norm_apply S]; rw [norm_apply R a]; rw [← LinearMap.det_restrictScalars]; rfl

variable {L : Type*} (K : Type*) [Field K] [Field L] [Algebra K L]

open Module IntermediateField AdjoinSimple

namespace Algebra

/--
theorem `isIntegral_norm` / 定理 `isIntegral_norm`

English:
theorem isIntegral_norm
  statement: [Algebra R L] [Algebra R K] [IsScalarTower R K L] {x : L}
  proof: by
  by_cases h : FiniteDimensional K L
  swap
  · simpa [norm_eq_one_of_not_module_finite h] using isIntegral_one
  let F := K⟮x⟯
  rw [← norm_norm (S := F)]; rw [← coe_gen K x]; rw [← IntermediateField.algebraMap_apply]; rw [norm_algebraMap_of_basis (Module.Free.chooseBasis F L) (gen K x)]; rw [ma

中文:
定理 is整数egral_norm
  结论: [代数 R L] [代数 R K] [标量塔 R K L] {x : L}
  证明: by
  by_cases h : FiniteDimensional K L
  swap
  · simpa [norm_eq_one_of_not_module_finite h] using isIntegral_one
  let F := K⟮x⟯
  rw [← norm_norm (S := F)]; rw [← coe_gen K x]; rw [← IntermediateField.algebraMap_apply]; rw [norm_algebraMap_of_basis (Module.Free.chooseBasis F L) (gen K x)]; rw [ma

Depends on / 依赖: AlgebraicClosure, FiniteDimensional, IntermediateField, IntermediateField.algebraMap_apply, IsAlgClosed, IsAlgClosed.splits, IsIntegral, IsIntegral.multiset_prod, IsIntegral.pow, Module, Module.Free.chooseBasis, algebraMap, algebraMap_apply, chooseBasis, coe_gen, injective, isIntegral_algebraMap_iff, isIntegral_one, map_pow, multiset_prod
-/
theorem isIntegral_norm [Algebra R L] [Algebra R K] [IsScalarTower R K L] {x : L}
    (hx : IsIntegral R x) : IsIntegral R (norm K x) := by
  by_cases h : FiniteDimensional K L
  swap
  · simpa [norm_eq_one_of_not_module_finite h] using isIntegral_one
  let F := K⟮x⟯
  rw [← norm_norm (S := F)]; rw [← coe_gen K x]; rw [← IntermediateField.algebraMap_apply]; rw [norm_algebraMap_of_basis (Module.Free.chooseBasis F L) (gen K x)]; rw [map_pow]
  apply IsIntegral.pow
  rw [← isIntegral_algebraMap_iff (algebraMap K (AlgebraicClosure F)).injective]; rw [norm_gen_eq_prod_roots _ (IsAlgClosed.splits _)]
  refine IsIntegral.multiset_prod (fun y hy => ⟨minpoly R x, minpoly.monic hx, ?_⟩)
  suffices (aeval y) ((minpoly R x).map (algebraMap R K)) = 0 by simpa
  obtain ⟨P, hP⟩ := minpoly.dvd K x (show aeval x ((minpoly R x).map (algebraMap R K)) = 0 by simp)
  simp [hP, aeval_mul, (mem_aroots'.mp hy).2]

/--
theorem `norm_eq_norm_adjoin` / 定理 `norm_eq_norm_adjoin`

English:
theorem norm_eq_norm_adjoin
  given: (x : L)
  proof: by
  by_cases h : FiniteDimensional K L
  swap
  · rw [norm_eq_one_of_not_module_finite h]
    by_cases hx : IsIntegral K x
· have h₁ : ¬ FiniteDimensional K⟮x⟯ L := fun H => h by
        have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx
        exact Finite.trans K⟮x⟯ L
      simp [fin

中文:
定理 norm_eq_norm_adjoin
  条件: (x : L)
  证明: by
  by_cases h : FiniteDimensional K L
  swap
  · rw [norm_eq_one_of_not_module_finite h]
    by_cases hx : IsIntegral K x
· have h₁ : ¬ FiniteDimensional K⟮x⟯ L := fun H => h by
        have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx
        exact Finite.trans K⟮x⟯ L
      simp [fin

Depends on / 依赖: Finite, Finite.trans, FiniteDimensional, Interm, IsIntegral, IsIntegral.isIntegral, adjoin, adjoin.finiteDimensional, coe_gen, finiteDimensional, finrank_of_not_finite, isIntegral, isIntegral_gen, norm_eq_one_of_not_module_finite, norm_norm, nth_rw
-/
theorem norm_eq_norm_adjoin (x : L) :
    norm K x = norm K (AdjoinSimple.gen K x) ^ finrank K⟮x⟯ L := by
  by_cases h : FiniteDimensional K L
  swap
  · rw [norm_eq_one_of_not_module_finite h]
    by_cases hx : IsIntegral K x
· have h₁ : ¬ FiniteDimensional K⟮x⟯ L := fun H => h by
        have : FiniteDimensional K K⟮x⟯ := adjoin.finiteDimensional hx
        exact Finite.trans K⟮x⟯ L
      simp [finrank_of_not_finite h₁]
    · rw [norm_eq_one_of_not_module_finite]
      · simp
      · refine fun H => hx ?_
        rw [← isIntegral_gen]
        exact IsIntegral.isIntegral (gen K x)
  let F := K⟮x⟯
  nth_rw 1 [← coe_gen K x]
  rw [← norm_norm (S := F)]; rw [← IntermediateField.algebraMap_apply]; rw [norm_algebraMap_of_basis (Module.Free.chooseBasis F L) (gen K x)]; rw [map_pow]; rw [finrank_eq_card_chooseBasisIndex]

variable (F E : Type*) [Field F] [Algebra K F] [Field E] [Algebra K E]

variable {K} in
/--
theorem `norm_eq_prod_roots` / 定理 `norm_eq_prod_roots`

English:
theorem norm_eq_prod_roots
  given: {x : L} (hF : ((minpoly K x).map (algebraMap K F)).Splits)
  proof: by
  rw [norm_eq_norm_adjoin K x]; rw [map_pow]; rw [IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots _ hF]

中文:
定理 norm_eq_prod_roots
  条件: {x : L} (hF : ((minpoly K x).map (algebraMap K F)).Splits)
  证明: by
  rw [norm_eq_norm_adjoin K x]; rw [map_pow]; rw [IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots _ hF]

Depends on / 依赖: AdjoinSimple, IntermediateField, IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots, map_pow, norm_eq_norm_adjoin, norm_gen_eq_prod_roots
-/
theorem norm_eq_prod_roots {x : L} (hF : ((minpoly K x).map (algebraMap K F)).Splits) :
    algebraMap K F (norm K x) =
      ((minpoly K x).aroots F).prod ^ finrank K⟮x⟯ L := by
  rw [norm_eq_norm_adjoin K x]; rw [map_pow]; rw [IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots _ hF]

variable [FiniteDimensional K L]

/--
theorem `norm_eq_prod_embeddings` / 定理 `norm_eq_prod_embeddings`

English:
theorem norm_eq_prod_embeddings
  statement: [Algebra.IsSeparable K L] [IsAlgClosed E]
  proof: by
  have hx := Algebra.IsSeparable.isIntegral K x
  rw [norm_eq_norm_adjoin K x]; rw [map_pow]; rw [← adjoin.powerBasis_gen hx]; rw [norm_eq_prod_embeddings_gen E (adjoin.powerBasis hx) (IsAlgClosed.splits _)]
  · exact (prod_embeddings_eq_finrank_pow L (L := K⟮x⟯) E (adjoin.powerBasis hx)).symm
  

中文:
定理 norm_eq_prod_embeddings
  结论: [代数.是可分 K L] [是代数闭 E]
  证明: by
  have hx := Algebra.IsSeparable.isIntegral K x
  rw [norm_eq_norm_adjoin K x]; rw [map_pow]; rw [← adjoin.powerBasis_gen hx]; rw [norm_eq_prod_embeddings_gen E (adjoin.powerBasis hx) (IsAlgClosed.splits _)]
  · exact (prod_embeddings_eq_finrank_pow L (L := K⟮x⟯) E (adjoin.powerBasis hx)).symm
  

Depends on / 依赖: Algebra, Algebra.IsSeparable.isIntegral, Algebra.IsSeparable.isSeparable, Algebra.isSeparable_tower_bot_of_isSeparable, IsAlgClosed, IsAlgClosed.splits, IsSeparable, adjoin, adjoin.powerBasis, adjoin.powerBasis_gen, isIntegral, isSeparable, isSeparable_tower_bot_of_isSeparable, map_pow, norm_eq_norm_adjoin, norm_eq_prod_embeddings_gen, powerBasis, powerBasis_gen, prod_embeddings_eq_finrank_pow, splits
-/
theorem norm_eq_prod_embeddings [Algebra.IsSeparable K L] [IsAlgClosed E]
    (x : L) : algebraMap K E (norm K x) = ∏ σ : L ->ₐ[K] E, σ x := by
  have hx := Algebra.IsSeparable.isIntegral K x
  rw [norm_eq_norm_adjoin K x]; rw [map_pow]; rw [← adjoin.powerBasis_gen hx]; rw [norm_eq_prod_embeddings_gen E (adjoin.powerBasis hx) (IsAlgClosed.splits _)]
  · exact (prod_embeddings_eq_finrank_pow L (L := K⟮x⟯) E (adjoin.powerBasis hx)).symm
  · have := Algebra.isSeparable_tower_bot_of_isSeparable K K⟮x⟯ L
    exact Algebra.IsSeparable.isSeparable K _

/--
theorem `norm_eq_prod_automorphisms` / 定理 `norm_eq_prod_automorphisms`

English:
theorem norm_eq_prod_automorphisms
  given: [IsGalois K L] (x : L)
  proof: by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [map_prod (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.prod_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← norm_eq_prod_embeddings _ _ x, ← IsScalarTower.algebraMap_apply]
  · intro σ
    simp only [N

中文:
定理 norm_eq_prod_automorphisms
  条件: [是Galois K L] (x : L)
  证明: by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [map_prod (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.prod_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← norm_eq_prod_embeddings _ _ x, ← IsScalarTower.algebraMap_apply]
  · intro σ
    simp only [N

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_ofBijective, AlgHom, AlgHom.restrictNormal, AlgHom.restrictNormal_commutes, AlgebraicClosure, Equiv.coe_fn_mk, FaithfulSMul, FaithfulSMul.algebraMap_injective, Fintype, Fintype.prod_equiv, IsScalarTower, IsScalarTower.algebraMap_apply, Normal, Normal.algHomEquivAut, RingHom, RingHom.id_apply, algHomEquivAut, algebraMap, algebraMap_apply
-/
theorem norm_eq_prod_automorphisms [IsGalois K L] (x : L) :
    algebraMap K L (norm K x) = ∏ σ : Gal(L/K), σ x := by
  apply FaithfulSMul.algebraMap_injective L (AlgebraicClosure L)
  rw [map_prod (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.prod_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← norm_eq_prod_embeddings _ _ x, ← IsScalarTower.algebraMap_apply]
  · intro σ
    simp only [Normal.algHomEquivAut, AlgHom.restrictNormal', Equiv.coe_fn_mk,
      AlgEquiv.coe_ofBijective, AlgHom.restrictNormal_commutes, algebraMap_self, RingHom.id_apply]

end Algebra
