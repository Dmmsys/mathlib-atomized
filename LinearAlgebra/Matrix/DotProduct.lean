/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Pi
public import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# Dot product of two vectors

This file contains some results on the map `dotProduct`, which maps two
vectors `v w : n → R` to the sum of the entrywise products `v i * w i`.

## Main results

* `dotProduct_stdBasis_one`: the dot product of `v` with the `i`th
  standard basis vector is `v i`
* `dotProduct_eq_zero_iff`: if `v`'s dot product with all `w` is zero,
  then `v` is zero

## Tags

matrix

-/

public section


variable {m n p R : Type*}

section Semiring

variable [Semiring R] [Fintype n]

/--
theorem `dotProduct_eq` / 定理 `dotProduct_eq`

English:
theorem dotProduct_eq
  given: (v w : n -> R) (h : forall u, v ⬝ᵥ u = w ⬝ᵥ u)
  statement: v = w
  proof: by
  funext x
  classical rw [← dotProduct_single_one v x, ← dotProduct_single_one w x, h]

中文:
定理 dotProduct_eq
  条件: (v w : n -> R) (h : 对任意 u, v ⬝ᵥ u = w ⬝ᵥ u)
  结论: v = w
  证明: by
  funext x
  classical rw [← dotProduct_single_one v x, ← dotProduct_single_one w x, h]

Depends on / 依赖: classical, dotProduct_single_one
-/
theorem dotProduct_eq (v w : n -> R) (h : forall u, v ⬝ᵥ u = w ⬝ᵥ u) : v = w := by
  funext x
  classical rw [← dotProduct_single_one v x, ← dotProduct_single_one w x, h]

/--
theorem `dotProduct_eq_iff` / 定理 `dotProduct_eq_iff`

English:
theorem dotProduct_eq_iff
  given: {v w : n -> R}
  statement: (forall u, v ⬝ᵥ u = w ⬝ᵥ u) ↔ v = w
  proof: ⟨fun h => dotProduct_eq v w h, fun h _ => h ▸ rfl⟩

中文:
定理 dotProduct_eq_iff
  条件: {v w : n -> R}
  结论: (对任意 u, v ⬝ᵥ u = w ⬝ᵥ u) ↔ v = w
  证明: ⟨fun h => dotProduct_eq v w h, fun h _ => h ▸ rfl⟩

Depends on / 依赖: dotProduct_eq
-/
theorem dotProduct_eq_iff {v w : n -> R} : (forall u, v ⬝ᵥ u = w ⬝ᵥ u) ↔ v = w :=
  ⟨fun h => dotProduct_eq v w h, fun h _ => h ▸ rfl⟩

/--
theorem `dotProduct_eq_zero` / 定理 `dotProduct_eq_zero`

English:
theorem dotProduct_eq_zero
  given: (v : n -> R) (h : forall w, v ⬝ᵥ w = 0)
  statement: v = 0
  proof: dotProduct_eq _ _ fun u => (h u).symm ▸ (zero_dotProduct u).symm

中文:
定理 dotProduct_eq_zero
  条件: (v : n -> R) (h : 对任意 w, v ⬝ᵥ w = 0)
  结论: v = 0
  证明: dotProduct_eq _ _ fun u => (h u).symm ▸ (zero_dotProduct u).symm

Depends on / 依赖: dotProduct_eq, zero_dotProduct
-/
theorem dotProduct_eq_zero (v : n -> R) (h : forall w, v ⬝ᵥ w = 0) : v = 0 :=
  dotProduct_eq _ _ fun u => (h u).symm ▸ (zero_dotProduct u).symm

/--
theorem `dotProduct_eq_zero_iff` / 定理 `dotProduct_eq_zero_iff`

English:
theorem dotProduct_eq_zero_iff
  given: {v : n -> R}
  statement: (forall w, v ⬝ᵥ w = 0) ↔ v = 0
  proof: ⟨fun h => dotProduct_eq_zero v h, fun h w => h.symm ▸ zero_dotProduct w⟩

中文:
定理 dotProduct_eq_zero_iff
  条件: {v : n -> R}
  结论: (对任意 w, v ⬝ᵥ w = 0) ↔ v = 0
  证明: ⟨fun h => dotProduct_eq_zero v h, fun h w => h.symm ▸ zero_dotProduct w⟩

Depends on / 依赖: dotProduct_eq_zero, h.symm, zero_dotProduct
-/
theorem dotProduct_eq_zero_iff {v : n -> R} : (forall w, v ⬝ᵥ w = 0) ↔ v = 0 :=
  ⟨fun h => dotProduct_eq_zero v h, fun h w => h.symm ▸ zero_dotProduct w⟩

end Semiring

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Fintype n]

/--
lemma `dotProduct_nonneg_of_nonneg` / 引理 `dotProduct_nonneg_of_nonneg`

English:
lemma dotProduct_nonneg_of_nonneg
  given: {v w : n -> R} (hv : 0 <= v) (hw : 0 <= w)
  statement: 0 <= v ⬝ᵥ w
  proof: Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hw i))

中文:
引理 dotProduct_nonneg_of_nonneg
  条件: {v w : n -> R} (hv : 0 <= v) (hw : 0 <= w)
  结论: 0 <= v ⬝ᵥ w
  证明: Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hw i))

Depends on / 依赖: Finset, Finset.sum_nonneg, mul_nonneg, sum_nonneg
-/
lemma dotProduct_nonneg_of_nonneg {v w : n -> R} (hv : 0 <= v) (hw : 0 <= w) : 0 <= v ⬝ᵥ w :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hv i) (hw i))

/--
lemma `dotProduct_le_dotProduct_of_nonneg_right` / 引理 `dotProduct_le_dotProduct_of_nonneg_right`

English:
lemma dotProduct_le_dotProduct_of_nonneg_right
  given: {u v w : n -> R} (huv : u <= v) (hw : 0 <= w)
  proof: by
  unfold dotProduct; gcongr <;> apply_rules

中文:
引理 dotProduct_le_dotProduct_of_nonneg_right
  条件: {u v w : n -> R} (huv : u <= v) (hw : 0 <= w)
  证明: by
  unfold dotProduct; gcongr <;> apply_rules

Depends on / 依赖: apply_rules, dotProduct
-/
lemma dotProduct_le_dotProduct_of_nonneg_right {u v w : n -> R} (huv : u <= v) (hw : 0 <= w) :
    u ⬝ᵥ w <= v ⬝ᵥ w := by
  unfold dotProduct; gcongr <;> apply_rules

/--
lemma `dotProduct_le_dotProduct_of_nonneg_left` / 引理 `dotProduct_le_dotProduct_of_nonneg_left`

English:
lemma dotProduct_le_dotProduct_of_nonneg_left
  given: {u v w : n -> R} (huv : u <= v) (hw : 0 <= w)
  proof: by
  unfold dotProduct; gcongr <;> apply_rules

中文:
引理 dotProduct_le_dotProduct_of_nonneg_left
  条件: {u v w : n -> R} (huv : u <= v) (hw : 0 <= w)
  证明: by
  unfold dotProduct; gcongr <;> apply_rules

Depends on / 依赖: apply_rules, dotProduct
-/
lemma dotProduct_le_dotProduct_of_nonneg_left {u v w : n -> R} (huv : u <= v) (hw : 0 <= w) :
    w ⬝ᵥ u <= w ⬝ᵥ v := by
  unfold dotProduct; gcongr <;> apply_rules

end OrderedSemiring

section Self

variable [Fintype m] [Fintype n] [Fintype p]

@[simp]
/--
theorem `dotProduct_self_eq_zero` / 定理 `dotProduct_self_eq_zero`

English:
theorem dotProduct_self_eq_zero
  given: [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {v : n -> R}
  proof: (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).trans by
    simp [funext_iff]

中文:
定理 dotProduct_self_eq_zero
  条件: [环 R] [线性序 R] [是StrictOrdered环 R] {v : n -> R}
  证明: (Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).trans by
    simp [funext_iff]

Depends on / 依赖: Finset, Finset.sum_eq_zero_iff_of_nonneg, funext_iff, mul_self_nonneg, sum_eq_zero_iff_of_nonneg
-/
theorem dotProduct_self_eq_zero [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {v : n -> R} :
    v ⬝ᵥ v = 0 ↔ v = 0 :=
(Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (v i)).trans by
    simp [funext_iff]

section StarOrderedRing

variable [PartialOrder R] [NonUnitalRing R] [StarRing R] [StarOrderedRing R]

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/--
theorem `dotProduct_star_self_nonneg` / 定理 `dotProduct_star_self_nonneg`

English:
theorem dotProduct_star_self_nonneg
  given: (v : n -> R)
  statement: 0 <= star v ⬝ᵥ v
  proof: Fintype.sum_nonneg fun _ => star_mul_self_nonneg _

中文:
定理 dotProduct_star_self_nonneg
  条件: (v : n -> R)
  结论: 0 <= star v ⬝ᵥ v
  证明: Fintype.sum_nonneg fun _ => star_mul_self_nonneg _

Depends on / 依赖: Fintype, Fintype.sum_nonneg, star_mul_self_nonneg, sum_nonneg
-/
theorem dotProduct_star_self_nonneg (v : n -> R) : 0 <= star v ⬝ᵥ v :=
  Fintype.sum_nonneg fun _ => star_mul_self_nonneg _

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/--
theorem `dotProduct_self_star_nonneg` / 定理 `dotProduct_self_star_nonneg`

English:
theorem dotProduct_self_star_nonneg
  given: (v : n -> R)
  statement: 0 <= v ⬝ᵥ star v
  proof: Fintype.sum_nonneg fun _ => mul_star_self_nonneg _

中文:
定理 dotProduct_self_star_nonneg
  条件: (v : n -> R)
  结论: 0 <= v ⬝ᵥ star v
  证明: Fintype.sum_nonneg fun _ => mul_star_self_nonneg _

Depends on / 依赖: Fintype, Fintype.sum_nonneg, mul_star_self_nonneg, sum_nonneg
-/
theorem dotProduct_self_star_nonneg (v : n -> R) : 0 <= v ⬝ᵥ star v :=
  Fintype.sum_nonneg fun _ => mul_star_self_nonneg _

variable [NoZeroDivisors R]

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/--
theorem `dotProduct_star_self_eq_zero` / 定理 `dotProduct_star_self_eq_zero`

English:
theorem dotProduct_star_self_eq_zero
  given: {v : n -> R}
  statement: star v ⬝ᵥ v = 0 ↔ v = 0
  proof: (Fintype.sum_eq_zero_iff_of_nonneg fun _ => star_mul_self_nonneg _).trans
    by simp [funext_iff, mul_eq_zero]

中文:
定理 dotProduct_star_self_eq_zero
  条件: {v : n -> R}
  结论: star v ⬝ᵥ v = 0 ↔ v = 0
  证明: (Fintype.sum_eq_zero_iff_of_nonneg fun _ => star_mul_self_nonneg _).trans
    by simp [funext_iff, mul_eq_zero]

Depends on / 依赖: Fintype, Fintype.sum_eq_zero_iff_of_nonneg, funext_iff, mul_eq_zero, star_mul_self_nonneg, sum_eq_zero_iff_of_nonneg
-/
theorem dotProduct_star_self_eq_zero {v : n -> R} : star v ⬝ᵥ v = 0 ↔ v = 0 :=
(Fintype.sum_eq_zero_iff_of_nonneg fun _ => star_mul_self_nonneg _).trans
    by simp [funext_iff, mul_eq_zero]

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/--
theorem `dotProduct_self_star_eq_zero` / 定理 `dotProduct_self_star_eq_zero`

English:
theorem dotProduct_self_star_eq_zero
  given: {v : n -> R}
  statement: v ⬝ᵥ star v = 0 ↔ v = 0
  proof: (Fintype.sum_eq_zero_iff_of_nonneg fun _ => mul_star_self_nonneg _).trans
    by simp [funext_iff, mul_eq_zero]

中文:
定理 dotProduct_self_star_eq_zero
  条件: {v : n -> R}
  结论: v ⬝ᵥ star v = 0 ↔ v = 0
  证明: (Fintype.sum_eq_zero_iff_of_nonneg fun _ => mul_star_self_nonneg _).trans
    by simp [funext_iff, mul_eq_zero]

Depends on / 依赖: Fintype, Fintype.sum_eq_zero_iff_of_nonneg, funext_iff, mul_eq_zero, mul_star_self_nonneg, sum_eq_zero_iff_of_nonneg
-/
theorem dotProduct_self_star_eq_zero {v : n -> R} : v ⬝ᵥ star v = 0 ↔ v = 0 :=
(Fintype.sum_eq_zero_iff_of_nonneg fun _ => mul_star_self_nonneg _).trans
    by simp [funext_iff, mul_eq_zero]

namespace Matrix

@[simp]
/--
lemma `conjTranspose_mul_self_eq_zero` / 引理 `conjTranspose_mul_self_eq_zero`

English:
lemma conjTranspose_mul_self_eq_zero
  given: {n} {A : Matrix m n R}
  statement: Aᴴ * A = 0 ↔ A = 0
  proof: ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_star_self_eq_zero.1 <| Matrix.ext_iff.2 h j j) i,
  fun h => h ▸ Matrix.mul_zero _⟩

@[simp]

中文:
引理 conjTranspose_mul_self_eq_zero
  条件: {n} {A : 矩阵 m n R}
  结论: Aᴴ * A = 0 ↔ A = 0
  证明: ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_star_self_eq_zero.1 <| Matrix.ext_iff.2 h j j) i,
  fun h => h ▸ Matrix.mul_zero _⟩

@[simp]

Depends on / 依赖: Matrix, Matrix.ext, Matrix.ext_iff, Matrix.mul_zero, congr_fun, dotProduct_star_self_eq_zero, ext_iff, mul_zero
-/
lemma conjTranspose_mul_self_eq_zero {n} {A : Matrix m n R} : Aᴴ * A = 0 ↔ A = 0 :=
  ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_star_self_eq_zero.1 <| Matrix.ext_iff.2 h j j) i,
  fun h => h ▸ Matrix.mul_zero _⟩

@[simp]
/--
lemma `self_mul_conjTranspose_eq_zero` / 引理 `self_mul_conjTranspose_eq_zero`

English:
lemma self_mul_conjTranspose_eq_zero
  given: {m} {A : Matrix m n R}
  statement: A * Aᴴ = 0 ↔ A = 0
  proof: ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_self_star_eq_zero.1 <| Matrix.ext_iff.2 h i i) j,
  fun h => h ▸ Matrix.zero_mul _⟩

中文:
引理 self_mul_conjTranspose_eq_zero
  条件: {m} {A : 矩阵 m n R}
  结论: A * Aᴴ = 0 ↔ A = 0
  证明: ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_self_star_eq_zero.1 <| Matrix.ext_iff.2 h i i) j,
  fun h => h ▸ Matrix.zero_mul _⟩

Depends on / 依赖: Matrix, Matrix.ext, Matrix.ext_iff, Matrix.zero_mul, congr_fun, dotProduct_self_star_eq_zero, ext_iff, zero_mul
-/
lemma self_mul_conjTranspose_eq_zero {m} {A : Matrix m n R} : A * Aᴴ = 0 ↔ A = 0 :=
  ⟨fun h => Matrix.ext fun i j =>
    (congr_fun <| dotProduct_self_star_eq_zero.1 <| Matrix.ext_iff.2 h i i) j,
  fun h => h ▸ Matrix.zero_mul _⟩

/--
lemma `conjTranspose_mul_self_mul_eq_zero` / 引理 `conjTranspose_mul_self_mul_eq_zero`

English:
lemma conjTranspose_mul_self_mul_eq_zero
  given: {p} (A : Matrix m n R) (B : Matrix n p R)
  proof: by
  refine ⟨fun h => ?_, fun h => by simp only [Matrix.mul_assoc, h, Matrix.mul_zero]⟩
  apply_fun (Bᴴ * ·) at h
  rwa [Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
    conjTranspose_mul_self_eq_zero] at h

中文:
引理 conjTranspose_mul_self_mul_eq_zero
  条件: {p} (A : 矩阵 m n R) (B : 矩阵 n p R)
  证明: by
  refine ⟨fun h => ?_, fun h => by simp only [Matrix.mul_assoc, h, Matrix.mul_zero]⟩
  apply_fun (Bᴴ * ·) at h
  rwa [Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
    conjTranspose_mul_self_eq_zero] at h

Depends on / 依赖: Matrix, Matrix.mul_assoc, Matrix.mul_zero, apply_fun, conjTranspose_mul, conjTranspose_mul_self_eq_zero, mul_assoc, mul_zero
-/
lemma conjTranspose_mul_self_mul_eq_zero {p} (A : Matrix m n R) (B : Matrix n p R) :
    (Aᴴ * A) * B = 0 ↔ A * B = 0 := by
  refine ⟨fun h => ?_, fun h => by simp only [Matrix.mul_assoc, h, Matrix.mul_zero]⟩
  apply_fun (Bᴴ * ·) at h
  rwa [Matrix.mul_zero, Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul,
    conjTranspose_mul_self_eq_zero] at h

/--
lemma `self_mul_conjTranspose_mul_eq_zero` / 引理 `self_mul_conjTranspose_mul_eq_zero`

English:
lemma self_mul_conjTranspose_mul_eq_zero
  given: {p} (A : Matrix m n R) (B : Matrix m p R)
  proof: by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mul_eq_zero Aᴴ _

中文:
引理 self_mul_conjTranspose_mul_eq_zero
  条件: {p} (A : 矩阵 m n R) (B : 矩阵 m p R)
  证明: by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mul_eq_zero Aᴴ _

Depends on / 依赖: conjTranspose_conjTranspose, conjTranspose_mul_self_mul_eq_zero
-/
lemma self_mul_conjTranspose_mul_eq_zero {p} (A : Matrix m n R) (B : Matrix m p R) :
    (A * Aᴴ) * B = 0 ↔ Aᴴ * B = 0 := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mul_eq_zero Aᴴ _

/--
lemma `mul_self_mul_conjTranspose_eq_zero` / 引理 `mul_self_mul_conjTranspose_eq_zero`

English:
lemma mul_self_mul_conjTranspose_eq_zero
  given: {p} (A : Matrix m n R) (B : Matrix p m R)
  proof: by
  rw [← conjTranspose_eq_zero]; rw [conjTranspose_mul]; rw [conjTranspose_mul]; rw [conjTranspose_conjTranspose]; rw [self_mul_conjTranspose_mul_eq_zero]; rw [← conjTranspose_mul]; rw [conjTranspose_eq_zero]

中文:
引理 mul_self_mul_conjTranspose_eq_zero
  条件: {p} (A : 矩阵 m n R) (B : 矩阵 p m R)
  证明: by
  rw [← conjTranspose_eq_zero]; rw [conjTranspose_mul]; rw [conjTranspose_mul]; rw [conjTranspose_conjTranspose]; rw [self_mul_conjTranspose_mul_eq_zero]; rw [← conjTranspose_mul]; rw [conjTranspose_eq_zero]

Depends on / 依赖: conjTranspose_conjTranspose, conjTranspose_eq_zero, conjTranspose_mul, self_mul_conjTranspose_mul_eq_zero
-/
lemma mul_self_mul_conjTranspose_eq_zero {p} (A : Matrix m n R) (B : Matrix p m R) :
    B * (A * Aᴴ) = 0 ↔ B * A = 0 := by
  rw [← conjTranspose_eq_zero]; rw [conjTranspose_mul]; rw [conjTranspose_mul]; rw [conjTranspose_conjTranspose]; rw [self_mul_conjTranspose_mul_eq_zero]; rw [← conjTranspose_mul]; rw [conjTranspose_eq_zero]

/--
lemma `mul_conjTranspose_mul_self_eq_zero` / 引理 `mul_conjTranspose_mul_self_eq_zero`

English:
lemma mul_conjTranspose_mul_self_eq_zero
  given: {p} (A : Matrix m n R) (B : Matrix p n R)
  proof: by
  simpa only [conjTranspose_conjTranspose] using mul_self_mul_conjTranspose_eq_zero Aᴴ _

中文:
引理 mul_conjTranspose_mul_self_eq_zero
  条件: {p} (A : 矩阵 m n R) (B : 矩阵 p n R)
  证明: by
  simpa only [conjTranspose_conjTranspose] using mul_self_mul_conjTranspose_eq_zero Aᴴ _

Depends on / 依赖: conjTranspose_conjTranspose, mul_self_mul_conjTranspose_eq_zero
-/
lemma mul_conjTranspose_mul_self_eq_zero {p} (A : Matrix m n R) (B : Matrix p n R) :
    B * (Aᴴ * A) = 0 ↔ B * Aᴴ = 0 := by
  simpa only [conjTranspose_conjTranspose] using mul_self_mul_conjTranspose_eq_zero Aᴴ _

/--
lemma `conjTranspose_mul_self_mulVec_eq_zero` / 引理 `conjTranspose_mul_self_mulVec_eq_zero`

English:
lemma conjTranspose_mul_self_mulVec_eq_zero
  given: (A : Matrix m n R) (v : n -> R)
  proof: by
  simpa only [← Matrix.replicateCol_mulVec, replicateCol_eq_zero] using
    conjTranspose_mul_self_mul_eq_zero A (replicateCol (Fin 1) v)

中文:
引理 conjTranspose_mul_self_mulVec_eq_zero
  条件: (A : 矩阵 m n R) (v : n -> R)
  证明: by
  simpa only [← Matrix.replicateCol_mulVec, replicateCol_eq_zero] using
    conjTranspose_mul_self_mul_eq_zero A (replicateCol (Fin 1) v)

Depends on / 依赖: Matrix, Matrix.replicateCol_mulVec, conjTranspose_mul_self_mul_eq_zero, replicateCol, replicateCol_eq_zero, replicateCol_mulVec
-/
lemma conjTranspose_mul_self_mulVec_eq_zero (A : Matrix m n R) (v : n -> R) :
    (Aᴴ * A) *ᵥ v = 0 ↔ A *ᵥ v = 0 := by
  simpa only [← Matrix.replicateCol_mulVec, replicateCol_eq_zero] using
    conjTranspose_mul_self_mul_eq_zero A (replicateCol (Fin 1) v)

/--
lemma `self_mul_conjTranspose_mulVec_eq_zero` / 引理 `self_mul_conjTranspose_mulVec_eq_zero`

English:
lemma self_mul_conjTranspose_mulVec_eq_zero
  given: (A : Matrix m n R) (v : m -> R)
  proof: by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mulVec_eq_zero Aᴴ _

中文:
引理 self_mul_conjTranspose_mulVec_eq_zero
  条件: (A : 矩阵 m n R) (v : m -> R)
  证明: by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mulVec_eq_zero Aᴴ _

Depends on / 依赖: conjTranspose_conjTranspose, conjTranspose_mul_self_mulVec_eq_zero
-/
lemma self_mul_conjTranspose_mulVec_eq_zero (A : Matrix m n R) (v : m -> R) :
    (A * Aᴴ) *ᵥ v = 0 ↔ Aᴴ *ᵥ v = 0 := by
  simpa only [conjTranspose_conjTranspose] using conjTranspose_mul_self_mulVec_eq_zero Aᴴ _

/--
lemma `vecMul_conjTranspose_mul_self_eq_zero` / 引理 `vecMul_conjTranspose_mul_self_eq_zero`

English:
lemma vecMul_conjTranspose_mul_self_eq_zero
  given: (A : Matrix m n R) (v : n -> R)
  proof: by
  simpa only [← Matrix.replicateRow_vecMul, replicateRow_eq_zero] using
    mul_conjTranspose_mul_self_eq_zero A (replicateRow (Fin 1) v)

中文:
引理 vecMul_conjTranspose_mul_self_eq_zero
  条件: (A : 矩阵 m n R) (v : n -> R)
  证明: by
  simpa only [← Matrix.replicateRow_vecMul, replicateRow_eq_zero] using
    mul_conjTranspose_mul_self_eq_zero A (replicateRow (Fin 1) v)

Depends on / 依赖: Matrix, Matrix.replicateRow_vecMul, mul_conjTranspose_mul_self_eq_zero, replicateRow, replicateRow_eq_zero, replicateRow_vecMul
-/
lemma vecMul_conjTranspose_mul_self_eq_zero (A : Matrix m n R) (v : n -> R) :
    v ᵥ* (Aᴴ * A) = 0 ↔ v ᵥ* Aᴴ = 0 := by
  simpa only [← Matrix.replicateRow_vecMul, replicateRow_eq_zero] using
    mul_conjTranspose_mul_self_eq_zero A (replicateRow (Fin 1) v)

/--
lemma `vecMul_self_mul_conjTranspose_eq_zero` / 引理 `vecMul_self_mul_conjTranspose_eq_zero`

English:
lemma vecMul_self_mul_conjTranspose_eq_zero
  given: (A : Matrix m n R) (v : m -> R)
  proof: by
  simpa only [conjTranspose_conjTranspose] using vecMul_conjTranspose_mul_self_eq_zero Aᴴ _

中文:
引理 vecMul_self_mul_conjTranspose_eq_zero
  条件: (A : 矩阵 m n R) (v : m -> R)
  证明: by
  simpa only [conjTranspose_conjTranspose] using vecMul_conjTranspose_mul_self_eq_zero Aᴴ _

Depends on / 依赖: conjTranspose_conjTranspose, vecMul_conjTranspose_mul_self_eq_zero
-/
lemma vecMul_self_mul_conjTranspose_eq_zero (A : Matrix m n R) (v : m -> R) :
    v ᵥ* (A * Aᴴ) = 0 ↔ v ᵥ* A = 0 := by
  simpa only [conjTranspose_conjTranspose] using vecMul_conjTranspose_mul_self_eq_zero Aᴴ _

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/--
theorem `dotProduct_star_self_pos_iff` / 定理 `dotProduct_star_self_pos_iff`

English:
theorem dotProduct_star_self_pos_iff
  given: {v : n -> R}
  proof: by
  nontriviality R
  refine (Fintype.sum_pos_iff_of_nonneg fun i => star_mul_self_nonneg _).trans ?_
  simp_rw [Pi.lt_def, Function.ne_iff, Pi.zero_apply]
refine (and_iff_right fun i => star_mul_self_nonneg (v i)).trans exists_congr fun i => ?_
  constructor
  · rintro h hv
    simp [hv] at h
  · exact (star_mul_self_pos <| .of_ne_zero ·)

中文:
定理 dotProduct_star_self_pos_iff
  条件: {v : n -> R}
  证明: by
  nontriviality R
  refine (Fintype.sum_pos_iff_of_nonneg fun i => star_mul_self_nonneg _).trans ?_
  simp_rw [Pi.lt_def, Function.ne_iff, Pi.zero_apply]
refine (and_iff_right fun i => star_mul_self_nonneg (v i)).trans exists_congr fun i => ?_
  constructor
  · rintro h hv
    simp [hv] at h
  · exact (star_mul_self_pos <| .of_ne_zero ·)

Depends on / 依赖: Fintype, Fintype.sum_pos_iff_of_nonneg, Function, Function.ne_iff, Pi.lt_def, Pi.zero_apply, and_iff_right, exists_congr, lt_def, ne_iff, nontriviality, of_ne_zero, simp_rw, star_mul_self_nonneg, star_mul_self_pos, sum_pos_iff_of_nonneg, zero_apply
-/
theorem dotProduct_star_self_pos_iff {v : n -> R} :
    0 < star v ⬝ᵥ v ↔ v != 0 := by
  nontriviality R
  refine (Fintype.sum_pos_iff_of_nonneg fun i => star_mul_self_nonneg _).trans ?_
  simp_rw [Pi.lt_def, Function.ne_iff, Pi.zero_apply]
refine (and_iff_right fun i => star_mul_self_nonneg (v i)).trans exists_congr fun i => ?_
  constructor
  · rintro h hv
    simp [hv] at h
  · exact (star_mul_self_pos <| .of_ne_zero ·)

/-- Note that this applies to `ℂ` via `RCLike.toStarOrderedRing`. -/
@[simp]
/--
theorem `dotProduct_self_star_pos_iff` / 定理 `dotProduct_self_star_pos_iff`

English:
theorem dotProduct_self_star_pos_iff
  given: {v : n -> R}
  statement: 0 < dotProduct v (star v) ↔ v != 0
  proof: by
  simpa using dotProduct_star_self_pos_iff (v := star v)

中文:
定理 dotProduct_self_star_pos_iff
  条件: {v : n -> R}
  结论: 0 < dotProduct v (star v) ↔ v != 0
  证明: by
  simpa using dotProduct_star_self_pos_iff (v := star v)

Depends on / 依赖: dotProduct_star_self_pos_iff
-/
theorem dotProduct_self_star_pos_iff {v : n -> R} : 0 < dotProduct v (star v) ↔ v != 0 := by
  simpa using dotProduct_star_self_pos_iff (v := star v)

end Matrix

end StarOrderedRing

end Self
