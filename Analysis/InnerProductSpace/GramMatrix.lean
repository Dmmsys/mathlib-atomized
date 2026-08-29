/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order

/-! # Gram Matrices

This file defines Gram matrices and proves their positive semidefiniteness.
Results require `RCLike 𝕜`.

## Main definition

* `Matrix.gram` : the `Matrix n n 𝕜` with `⟪v i, v j⟫` at `i j : n`, where `v : n → E` for an
  `Inner 𝕜 E`.

## Main results

* `Matrix.posSemidef_gram`: Gram matrices are positive semidefinite.
* `Matrix.posDef_gram_iff_linearIndependent`: Linear independence of `v` is
  equivalent to positive definiteness of `gram 𝕜 v`.
-/

@[expose] public section

open RCLike Real Matrix

open scoped InnerProductSpace ComplexOrder ComplexConjugate

variable {E n α 𝕜 : Type*}
namespace Matrix

/--
Definition of `gram` / `gram` 的定义

English:
definition gram
  signature: (𝕜 : Type*) [Inner 𝕜 E] (v : n -> E)
  body: of fun i j => ⟪v i, v j⟫_𝕜

@[simp]

中文:
定义 gram
  签名: (𝕜 : 类型) [Inner 𝕜 E] (v : n -> E)
  定义体: of fun i j => ⟪v i, v j⟫_𝕜

@[simp]
-/
def gram (𝕜 : Type*) [Inner 𝕜 E] (v : n -> E) : Matrix n n 𝕜 := of fun i j => ⟪v i, v j⟫_𝕜

@[simp]
/--
lemma `gram_apply` / 引理 `gram_apply`

English:
lemma gram_apply
  given: [Inner 𝕜 E] (v : n -> E) (i j : n)
  proof: rfl

中文:
引理 gram_apply
  条件: [Inner 𝕜 E] (v : n -> E) (i j : n)
  证明: rfl
-/
lemma gram_apply [Inner 𝕜 E] (v : n -> E) (i j : n) :
    (gram 𝕜 v) i j = ⟪v i, v j⟫_𝕜 := rfl

variable [RCLike 𝕜]

section SemiInnerProductSpace
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

@[simp]
/--
lemma `gram_zero` / 引理 `gram_zero`

English:
lemma gram_zero
  statement: gram 𝕜 (0 : n -> E) = 0
  proof: Matrix.ext fun _ _ => inner_zero_left _

@[simp]

中文:
引理 gram_zero
  结论: gram 𝕜 (0 : n -> E) = 0
  证明: Matrix.ext fun _ _ => inner_zero_left _

@[simp]

Depends on / 依赖: Matrix, Matrix.ext, inner_zero_left
-/
lemma gram_zero : gram 𝕜 (0 : n -> E) = 0 := Matrix.ext fun _ _ => inner_zero_left _

@[simp]
/--
lemma `gram_single` / 引理 `gram_single`

English:
lemma gram_single
  given: [DecidableEq n] (i : n) (x : E)
  proof: by
  ext j k
  obtain hij | rfl := ne_or_eq i j
  · simp [hij]
  obtain hik | rfl := ne_or_eq i k
  · simp [hik]
  simp

中文:
引理 gram_single
  条件: [DecidableEq n] (i : n) (x : E)
  证明: by
  ext j k
  obtain hij | rfl := ne_or_eq i j
  · simp [hij]
  obtain hik | rfl := ne_or_eq i k
  · simp [hik]
  simp

Depends on / 依赖: ne_or_eq
-/
lemma gram_single [DecidableEq n] (i : n) (x : E) :
    gram 𝕜 (Pi.single i x) = Matrix.single i i ⟪x, x⟫_𝕜 := by
  ext j k
  obtain hij | rfl := ne_or_eq i j
  · simp [hij]
  obtain hik | rfl := ne_or_eq i k
  · simp [hik]
  simp

/--
lemma `submatrix_gram` / 引理 `submatrix_gram`

English:
lemma submatrix_gram
  given: (v : n -> E) {m : Set n} (f : m -> n)
  proof: rfl

中文:
引理 submatrix_gram
  条件: (v : n -> E) {m : Set n} (f : m -> n)
  证明: rfl
-/
lemma submatrix_gram (v : n -> E) {m : Set n} (f : m -> n) :
    (gram 𝕜 v).submatrix f f = gram 𝕜 (v ∘ f) := rfl

variable (𝕜) in
/--
lemma `isHermitian_gram` / 引理 `isHermitian_gram`

English:
lemma isHermitian_gram
  given: (v : n -> E)
  statement: (gram 𝕜 v).IsHermitian
  proof: Matrix.ext fun _ _ => inner_conj_symm _ _

中文:
引理 isHermitian_gram
  条件: (v : n -> E)
  结论: (gram 𝕜 v).IsHermitian
  证明: Matrix.ext fun _ _ => inner_conj_symm _ _

Depends on / 依赖: Matrix, Matrix.ext, inner_conj_symm
-/
lemma isHermitian_gram (v : n -> E) : (gram 𝕜 v).IsHermitian :=
  Matrix.ext fun _ _ => inner_conj_symm _ _

/--
theorem `star_dotProduct_gram_mulVec` / 定理 `star_dotProduct_gram_mulVec`

English:
theorem star_dotProduct_gram_mulVec
  given: [Fintype n] (v : n -> E) (x y : n -> 𝕜)
  proof: by
  trans ∑ i, ∑ j, conj (x i) * y j * ⟪v i, v j⟫_𝕜
  · simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm, ← star_def,
      gram_apply, Pi.star_apply]
  · simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]

中文:
定理 star_dotProduct_gram_mulVec
  条件: [Fintype n] (v : n -> E) (x y : n -> 𝕜)
  证明: by
  trans ∑ i, ∑ j, conj (x i) * y j * ⟪v i, v j⟫_𝕜
  · simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm, ← star_def,
      gram_apply, Pi.star_apply]
  · simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]

Depends on / 依赖: Finset, Finset.mul_sum, Pi.star_apply, dotProduct, gram_apply, inner_smul_left, inner_smul_right, inner_sum, mulVec, mul_assoc, mul_comm, mul_sum, simp_rw, star_apply, star_def, sum_inner
-/
theorem star_dotProduct_gram_mulVec [Fintype n] (v : n -> E) (x y : n -> 𝕜) :
    star x ⬝ᵥ (gram 𝕜 v) *ᵥ y = ⟪∑ i, x i • v i, ∑ i, y i • v i⟫_𝕜 := by
  trans ∑ i, ∑ j, conj (x i) * y j * ⟪v i, v j⟫_𝕜
  · simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm, ← star_def,
      gram_apply, Pi.star_apply]
  · simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]

variable [Finite n]

variable (𝕜) in
/--
theorem `posSemidef_gram` / 定理 `posSemidef_gram`

English:
theorem posSemidef_gram
  given: (v : n -> E)
  proof: by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_gram _ _) fun x => ?_
  rw [star_dotProduct_gram_mulVec]; rw [le_iff_re_im]
  simp

中文:
定理 posSemidef_gram
  条件: (v : n -> E)
  证明: by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_gram _ _) fun x => ?_
  rw [star_dotProduct_gram_mulVec]; rw [le_iff_re_im]
  simp

Depends on / 依赖: Fintype, Fintype.ofFinite, isHermitian_gram, le_iff_re_im, ofFinite, of_dotProduct_mulVec_nonneg, star_dotProduct_gram_mulVec
-/
theorem posSemidef_gram (v : n -> E) :
    PosSemidef (gram 𝕜 v) := by
  have := Fintype.ofFinite n
  refine .of_dotProduct_mulVec_nonneg (isHermitian_gram _ _) fun x => ?_
  rw [star_dotProduct_gram_mulVec]; rw [le_iff_re_im]
  simp

/--
theorem `linearIndependent_of_posDef_gram` / 定理 `linearIndependent_of_posDef_gram`

English:
theorem linearIndependent_of_posDef_gram
  given: {v : n -> E} (h_gram : PosDef (gram 𝕜 v))
  proof: by
  have := Fintype.ofFinite n
  rw [Fintype.linearIndependent_iff]
  intro y hy
  have := h_gram.dotProduct_mulVec_pos (x := y)
  simp_all [star_dotProduct_gram_mulVec]

omit [Finite n] in

中文:
定理 linearIndependent_of_posDef_gram
  条件: {v : n -> E} (h_gram : PosDef (gram 𝕜 v))
  证明: by
  have := Fintype.ofFinite n
  rw [Fintype.linearIndependent_iff]
  intro y hy
  have := h_gram.dotProduct_mulVec_pos (x := y)
  simp_all [star_dotProduct_gram_mulVec]

omit [Finite n] in

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff, Fintype.ofFinite, dotProduct_mulVec_pos, h_gram, h_gram.dotProduct_mulVec_pos, linearIndependent_iff, ofFinite, star_dotProduct_gram_mulVec
-/
theorem linearIndependent_of_posDef_gram {v : n -> E} (h_gram : PosDef (gram 𝕜 v)) :
    LinearIndependent 𝕜 v := by
  have := Fintype.ofFinite n
  rw [Fintype.linearIndependent_iff]
  intro y hy
  have := h_gram.dotProduct_mulVec_pos (x := y)
  simp_all [star_dotProduct_gram_mulVec]

omit [Finite n] in
/--
theorem `linearIndependent_of_det_gram_ne_zero` / 定理 `linearIndependent_of_det_gram_ne_zero`

English:
theorem linearIndependent_of_det_gram_ne_zero
  statement: [Fintype n] [DecidableEq n] {v : n -> E}
  proof: linearIndependent_of_posDef_gram (posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero.mpr h

中文:
定理 linearIndependent_of_det_gram_ne_zero
  结论: [Fintype n] [DecidableEq n] {v : n -> E}
  证明: linearIndependent_of_posDef_gram (posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero.mpr h

Depends on / 依赖: linearIndependent_of_posDef_gram, posDef_iff_det_ne_zero, posDef_iff_det_ne_zero.mpr, posSemidef_gram
-/
theorem linearIndependent_of_det_gram_ne_zero [Fintype n] [DecidableEq n] {v : n -> E}
    (h : (gram 𝕜 v).det != 0) : LinearIndependent 𝕜 v :=
linearIndependent_of_posDef_gram (posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero.mpr h

end SemiInnerProductSpace

section NormedInnerProductSpace
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Finite n]

/--
theorem `posDef_gram_of_linearIndependent` / 定理 `posDef_gram_of_linearIndependent`

English:
theorem posDef_gram_of_linearIndependent
  proof: by
  have := Fintype.ofFinite n
  rw [Fintype.linearIndependent_iff] at h_li
  refine .of_dotProduct_mulVec_pos (isHermitian_gram _ _) fun x hx =>
    ((posSemidef_gram ..).dotProduct_mulVec_nonneg _).lt_of_ne' ?_
  rw [star_dotProduct_gram_mulVec]; rw [inner_self_eq_zero.ne]
  exact mt (h_li x) (mt

中文:
定理 posDef_gram_of_linearIndependent
  证明: by
  have := Fintype.ofFinite n
  rw [Fintype.linearIndependent_iff] at h_li
  refine .of_dotProduct_mulVec_pos (isHermitian_gram _ _) fun x hx =>
    ((posSemidef_gram ..).dotProduct_mulVec_nonneg _).lt_of_ne' ?_
  rw [star_dotProduct_gram_mulVec]; rw [inner_self_eq_zero.ne]
  exact mt (h_li x) (mt

Depends on / 依赖: Fintype, Fintype.linearIndependent_iff, Fintype.ofFinite, dotProduct_mulVec_nonneg, h_li, inner_self_eq_zero, inner_self_eq_zero.ne, isHermitian_gram, linearIndependent_iff, lt_of_ne, ofFinite, of_dotProduct_mulVec_pos, posSemidef_gram, star_dotProduct_gram_mulVec
-/
theorem posDef_gram_of_linearIndependent
    {v : n -> E} (h_li : LinearIndependent 𝕜 v) : PosDef (gram 𝕜 v) := by
  have := Fintype.ofFinite n
  rw [Fintype.linearIndependent_iff] at h_li
  refine .of_dotProduct_mulVec_pos (isHermitian_gram _ _) fun x hx =>
    ((posSemidef_gram ..).dotProduct_mulVec_nonneg _).lt_of_ne' ?_
  rw [star_dotProduct_gram_mulVec]; rw [inner_self_eq_zero.ne]
  exact mt (h_li x) (mt funext hx)

/--
theorem `posDef_gram_iff_linearIndependent` / 定理 `posDef_gram_iff_linearIndependent`

English:
theorem posDef_gram_iff_linearIndependent
  given: {v : n -> E}
  proof: ⟨linearIndependent_of_posDef_gram, posDef_gram_of_linearIndependent⟩

omit [Finite n] in

中文:
定理 posDef_gram_iff_linearIndependent
  条件: {v : n -> E}
  证明: ⟨linearIndependent_of_posDef_gram, posDef_gram_of_linearIndependent⟩

omit [Finite n] in

Depends on / 依赖: linearIndependent_of_posDef_gram, posDef_gram_of_linearIndependent
-/
theorem posDef_gram_iff_linearIndependent {v : n -> E} :
    PosDef (gram 𝕜 v) ↔ LinearIndependent 𝕜 v :=
  ⟨linearIndependent_of_posDef_gram, posDef_gram_of_linearIndependent⟩

omit [Finite n] in
/--
theorem `det_gram_ne_zero_iff_linearIndependent` / 定理 `det_gram_ne_zero_iff_linearIndependent`

English:
theorem det_gram_ne_zero_iff_linearIndependent
  given: [Fintype n] [DecidableEq n] {v : n -> E}
  proof: by
  rw [← posDef_gram_iff_linearIndependent]; rw [(posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero]

omit [Finite n] in

中文:
定理 det_gram_ne_zero_iff_linearIndependent
  条件: [Fintype n] [DecidableEq n] {v : n -> E}
  证明: by
  rw [← posDef_gram_iff_linearIndependent]; rw [(posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero]

omit [Finite n] in

Depends on / 依赖: posDef_gram_iff_linearIndependent, posDef_iff_det_ne_zero, posSemidef_gram
-/
theorem det_gram_ne_zero_iff_linearIndependent [Fintype n] [DecidableEq n] {v : n -> E} :
    (gram 𝕜 v).det != 0 ↔ LinearIndependent 𝕜 v := by
  rw [← posDef_gram_iff_linearIndependent]; rw [(posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero]

omit [Finite n] in
/--
theorem `gram_eq_conjTranspose_mul` / 定理 `gram_eq_conjTranspose_mul`

English:
theorem gram_eq_conjTranspose_mul
  given: {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (v : n -> E)
  proof: of fun i j => b.repr (v j) i
    gram 𝕜 v = mᴴ * m := by
  ext i j
  simp [mul_apply, b.repr_apply_apply, b.sum_inner_mul_inner]

omit [Finite n] in
@[simp]

中文:
定理 gram_eq_conjTranspose_mul
  条件: {ι : 类型} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (v : n -> E)
  证明: of fun i j => b.repr (v j) i
    gram 𝕜 v = mᴴ * m := by
  ext i j
  simp [mul_apply, b.repr_apply_apply, b.sum_inner_mul_inner]

omit [Finite n] in
@[simp]

Depends on / 依赖: b.repr
-/
theorem gram_eq_conjTranspose_mul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (v : n -> E) :
    letI m := of fun i j => b.repr (v j) i
    gram 𝕜 v = mᴴ * m := by
  ext i j
  simp [mul_apply, b.repr_apply_apply, b.sum_inner_mul_inner]

omit [Finite n] in
@[simp]
/--
lemma `gram_eq_one_iff_orthonormal` / 引理 `gram_eq_one_iff_orthonormal`

English:
lemma gram_eq_one_iff_orthonormal
  given: [DecidableEq n] {v : n -> E}
  statement: gram 𝕜 v = 1 ↔ Orthonormal 𝕜 v
  proof: by
  simp [← Matrix.ext_iff, orthonormal_iff_ite, Matrix.one_apply]

omit [Finite n] in

中文:
引理 gram_eq_one_iff_orthonormal
  条件: [DecidableEq n] {v : n -> E}
  结论: gram 𝕜 v = 1 ↔ Orthonormal 𝕜 v
  证明: by
  simp [← Matrix.ext_iff, orthonormal_iff_ite, Matrix.one_apply]

omit [Finite n] in

Depends on / 依赖: Matrix, Matrix.ext_iff, Matrix.one_apply, ext_iff, one_apply, orthonormal_iff_ite
-/
lemma gram_eq_one_iff_orthonormal [DecidableEq n] {v : n -> E} : gram 𝕜 v = 1 ↔ Orthonormal 𝕜 v := by
  simp [← Matrix.ext_iff, orthonormal_iff_ite, Matrix.one_apply]

omit [Finite n] in
/--
theorem `posSemidef_opNorm_smul_gram_sub_gram` / 定理 `posSemidef_opNorm_smul_gram_sub_gram`

English:
theorem posSemidef_opNorm_smul_gram_sub_gram
  statement: {F} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  proof: by
  refine ⟨(isHermitian_gram 𝕜 v).smul (((Pi.isSelfAdjoint.mpr (congrFun rfl)).apply f).pow 2)
.sub (isHermitian_gram 𝕜 (f ∘ v)), fun c => ?_⟩
  simp_rw [Finsupp.sum, Matrix.sub_apply, Matrix.smul_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib, sub_nonneg]
  calc
    ∑ x in c.support, ∑ y in 

中文:
定理 posSemidef_opNorm_smul_gram_sub_gram
  结论: {F} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  证明: by
  refine ⟨(isHermitian_gram 𝕜 v).smul (((Pi.isSelfAdjoint.mpr (congrFun rfl)).apply f).pow 2)
.sub (isHermitian_gram 𝕜 (f ∘ v)), fun c => ?_⟩
  simp_rw [Finsupp.sum, Matrix.sub_apply, Matrix.smul_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib, sub_nonneg]
  calc
    ∑ x in c.support, ∑ y in 

Depends on / 依赖: Finset, Finset.sum_sub_distrib, Finsupp, Finsupp.sum, Matrix, Matrix.smul_apply, Matrix.sub_apply, Pi.isSelfAdjoint.mpr, c.support, f.le_opNorm, isHermitian_gram, isSelfAdjoint, le_opNorm, mul_, mul_sub, simp_rw, smul_apply, smul_eq_mul, sub_apply, sub_mul
-/
theorem posSemidef_opNorm_smul_gram_sub_gram {F} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (v : n -> E) (f : E ->L[𝕜] F) : (‖f‖ ^ 2 • gram 𝕜 v - gram 𝕜 (f ∘ v)).PosSemidef := by
  refine ⟨(isHermitian_gram 𝕜 v).smul (((Pi.isSelfAdjoint.mpr (congrFun rfl)).apply f).pow 2)
.sub (isHermitian_gram 𝕜 (f ∘ v)), fun c => ?_⟩
  simp_rw [Finsupp.sum, Matrix.sub_apply, Matrix.smul_apply, mul_sub, sub_mul,
    Finset.sum_sub_distrib, sub_nonneg]
  calc
    ∑ x in c.support, ∑ y in c.support, star (c x) * gram 𝕜 (f ∘ v) x y * c y
    _ = (‖f (∑ x in c.support, c x • v x)‖ : 𝕜) ^ 2 := ?h1
    _ <= ‖f‖ ^ 2 • (‖∑ i in c.support, c i • v i‖ : 𝕜) ^ 2 := by
      norm_cast
      grw [f.le_opNorm _, smul_eq_mul, ← mul_pow]
    _ = ∑ x in c.support, ∑ y in c.support, star (c x) * ‖f‖ ^ 2 • gram 𝕜 v x y * c y := ?h2
  all_goals
    rw [Finset.sum_comm]
    simp [← inner_self_eq_norm_sq_to_K, inner_sum, sum_inner, inner_smul_left, inner_smul_right,
      Finset.mul_sum, Finset.smul_sum, RCLike.real_smul_eq_coe_mul]
    grind

end NormedInnerProductSpace

end Matrix
