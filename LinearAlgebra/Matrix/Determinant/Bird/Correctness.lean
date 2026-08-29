/-
Copyright (c) 2026 Paul Cadman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Cadman
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Data.Fintype.Order
import Mathlib.Order.Preorder.Finite

/-!
# Correctness of Bird's determinant algorithm

This file contains a proof that Bird's division-free algorithm computes
`Matrix.det`, in both its matrix form `BirdDet.Spec.birdDet`
(`birdDetSpec_eq_det`) and its flat-array form `BirdDet.birdDet`
(`det_eq_birdDet`), formalizing the combinatorial argument of
[Richard S. Bird, *A simple division-free algorithm for computing determinants*][bird2011].

## Correspondence with the paper

* A word of length `p` is a tuple `Fin p → Fin n`, using the indexing convention
  above (NB: Indices in Bird's paper start at 1).
* `f[α, β]`, the minor on rows `α` and columns `β`, is `(A.submatrix α β).det`.
* `f[iα, jα]`, a bordered minor, is `bminor A i j α`, with the word `iα` spelled
  `Fin.cons i α`.
* `f[α, α]`, a principal minor, is `pminor A α`.
* If `i : Fin n` represents Bird's symbol `r = i.val + 1`, then Bird's
  `βᵣ = [r + 1, ..., n]` is represented by `Finset.Ioi i`.
* Bird's `Sₚ(βᵣ)`, the length `p` subsequences of `βᵣ`, is represented by `S p i`.

The theorem names `paper_eq1`, ..., `paper_eq5` follow Bird's numbering.

## Main results

- `BirdDet.birdDetSpec_eq_det`: `Matrix.det` computes the same determinant as `BirdDet.Spec.birdDet`
- `BirdDet.det_eq_birdDet`: `Matrix.det` computes the same determinant as `BirdDet.birdDet`
-/

namespace BirdDet

open Function
variable {R : Type*} [CommRing R] {m n : Nat}

/--
theorem `sumFrom_eq_sum_Ico` / 定理 `sumFrom_eq_sum_Ico`

English:
theorem sumFrom_eq_sum_Ico
  given: {lo : Nat} (f : Nat -> R)
  proof: by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

中文:
定理 sumFrom_eq_sum_Ico
  条件: {lo : 自然数} (f : 自然数 -> R)
  证明: by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

Depends on / 依赖: BirdDet, BirdDet.sumFrom_induct, Finset, Finset.Ico_eq_empty, Finset.sum_empty, Finset.sum_eq_sum_Ico_succ_bot, Ico_eq_empty, sumFrom_induct, sumFrom_step, sumFrom_stop, sum_empty, sum_eq_sum_Ico_succ_bot
-/
theorem sumFrom_eq_sum_Ico {lo : Nat} (f : Nat -> R) :
    BirdDet.sumFrom n lo f = ∑ k in Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

/--
theorem `sumFrom_fin_tail` / 定理 `sumFrom_fin_tail`

English:
theorem sumFrom_fin_tail
  given: (i : Fin n) (f : Nat -> R)
  proof: calc
  _ = ∑ k in Finset.Ico (i.val + 1) n, f k := by rw [sumFrom_eq_sum_Ico]
  _ = ∑ k in (Finset.range n).filter (i.val < ·), f k := by congr; ext; aesop
  _ = ∑ k in Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
  _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 :

中文:
定理 sumFrom_fin_tail
  条件: (i : Fin n) (f : 自然数 -> R)
  证明: calc
  _ = ∑ k in Finset.Ico (i.val + 1) n, f k := by rw [sumFrom_eq_sum_Ico]
  _ = ∑ k in (Finset.range n).filter (i.val < ·), f k := by congr; ext; aesop
  _ = ∑ k in Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
  _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 :
-/
theorem sumFrom_fin_tail (i : Fin n) (f : Nat -> R) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k in Finset.Ioi i, f k.val := calc
  _ = ∑ k in Finset.Ico (i.val + 1) n, f k := by rw [sumFrom_eq_sum_Ico]
  _ = ∑ k in (Finset.range n).filter (i.val < ·), f k := by congr; ext; aesop
  _ = ∑ k in Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
  _ = ∑ k : Fin n, if i.val < k.val then f k.val else 0 := by rw [← Fin.sum_univ_eq_sum_range]
  _ = ∑ k in Finset.Ioi i, f k.val := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

/--
theorem `iterate_stepEntry_get_eq_spec` / 定理 `iterate_stepEntry_get_eq_spec`

English:
theorem iterate_stepEntry_get_eq_spec
  given: (A : Array R) (hA : A.size = n * n) (t : Nat) (i j : Fin n)
  proof: by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [get_eq]
  | succ t ih =>
    simp_rw [iterate_succ_apply', stepEntry_eq, Spec.stepEntry_eq, sumFrom_fin_tail, ih,
      Matrix.of_apply, get_eq]

中文:
定理 iterate_stepEntry_get_eq_spec
  条件: (A : Array R) (hA : A.size = n * n) (t : 自然数) (i j : Fin n)
  证明: by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [get_eq]
  | succ t ih =>
    simp_rw [iterate_succ_apply', stepEntry_eq, Spec.stepEntry_eq, sumFrom_fin_tail, ih,
      Matrix.of_apply, get_eq]

Depends on / 依赖: Matrix, Matrix.ofArray_eq_of_getD, Matrix.of_apply, Spec.stepEntry_eq, generalizing, get_eq, iterate_succ_apply, ofArray_eq_of_getD, of_apply, simp_rw, stepEntry_eq, sumFrom_fin_tail
-/
theorem iterate_stepEntry_get_eq_spec (A : Array R) (hA : A.size = n * n) (t : Nat) (i j : Fin n) :
    ((stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [get_eq]
  | succ t ih =>
    simp_rw [iterate_succ_apply', stepEntry_eq, Spec.stepEntry_eq, sumFrom_fin_tail, ih,
      Matrix.of_apply, get_eq]

/--
theorem `birdDet_eq_birdDetSpec` / 定理 `birdDet_eq_birdDetSpec`

English:
theorem birdDet_eq_birdDetSpec
  given: (A : Array R) (hA : A.size = n * n)
  proof: by
  cases n with
  | zero => rw [birdDet_zero, Spec.birdDetSpec_zero]
  | succ k => simp [birdDet_succ, Spec.birdDetSpec_succ, ← iterate_stepEntry_get_eq_spec A hA k]

中文:
定理 birdDet_eq_birdDetSpec
  条件: (A : Array R) (hA : A.size = n * n)
  证明: by
  cases n with
  | zero => rw [birdDet_zero, Spec.birdDetSpec_zero]
  | succ k => simp [birdDet_succ, Spec.birdDetSpec_succ, ← iterate_stepEntry_get_eq_spec A hA k]

Depends on / 依赖: Spec.birdDetSpec_succ, Spec.birdDetSpec_zero, birdDetSpec_succ, birdDetSpec_zero, birdDet_succ, birdDet_zero, iterate_stepEntry_get_eq_spec
-/
theorem birdDet_eq_birdDetSpec (A : Array R) (hA : A.size = n * n) :
    birdDet n A = Spec.birdDet (.ofArray A hA) := by
  cases n with
  | zero => rw [birdDet_zero, Spec.birdDetSpec_zero]
  | succ k => simp [birdDet_succ, Spec.birdDetSpec_succ, ← iterate_stepEntry_get_eq_spec A hA k]

variable (A : Matrix (Fin n) (Fin n) R) {p : Nat}

/--
Definition of `bminor` / `bminor` 的定义

English:
abbreviation bminor
  signature: (i j : Fin n) (α : Fin p -> Fin n)
  body: (A.submatrix (Fin.cons i α) (Fin.cons j α)).det

中文:
缩写 bminor
  签名: (i j : Fin n) (α : Fin p -> Fin n)
  定义体: (A.submatrix (Fin.cons i α) (Fin.cons j α)).det

Depends on / 依赖: A.submatrix, Fin.cons, submatrix
-/
abbrev bminor (i j : Fin n) (α : Fin p -> Fin n) : R :=
  (A.submatrix (Fin.cons i α) (Fin.cons j α)).det

/--
Definition of `pminor` / `pminor` 的定义

English:
abbreviation pminor
  signature: (α : Fin p -> Fin n)
  body: (A.submatrix α α).det

中文:
缩写 pminor
  签名: (α : Fin p -> Fin n)
  定义体: (A.submatrix α α).det

Depends on / 依赖: A.submatrix, submatrix
-/
abbrev pminor (α : Fin p -> Fin n) : R :=
  (A.submatrix α α).det

/--
lemma `det_submatrix_removeNth_eq_sign_mul_bminor` / 引理 `det_submatrix_removeNth_eq_sign_mul_bminor`

English:
lemma det_submatrix_removeNth_eq_sign_mul_bminor
  proof: calc
    _ = (-1 : R) ^ s.val * ((A.submatrix (Fin.cons i (s.removeNth α)) α)
.submatrix id (Fin.cycleRange s).symm).det := by
      rw [Matrix.det_permute']
      simp [← mul_assoc, ← pow_add]
    _ = (-1 : R) ^ s.val * bminor A i (α s) (s.removeNth α) := by
      congrm _ * Matrix.det ?_
      sim

中文:
引理 det_submatrix_removeNth_eq_sign_mul_bminor
  证明: calc
    _ = (-1 : R) ^ s.val * ((A.submatrix (Fin.cons i (s.removeNth α)) α)
.submatrix id (Fin.cycleRange s).symm).det := by
      rw [Matrix.det_permute']
      simp [← mul_assoc, ← pow_add]
    _ = (-1 : R) ^ s.val * bminor A i (α s) (s.removeNth α) := by
      congrm _ * Matrix.det ?_
      sim

Depends on / 依赖: A.submatrix, Fin.cons, Fin.cons_removeNth_eq_comp_cycleRange_symm, Fin.cycleRange, Matrix, Matrix.det, Matrix.det_permute, bminor, congrm, cons_removeNth_eq_comp_cycleRange_symm, cycleRange, det_permute, mul_assoc, pow_add, removeNth, s.removeNth, s.val, submatrix
-/
lemma det_submatrix_removeNth_eq_sign_mul_bminor
  (α : Fin (p + 1) -> Fin n) (i : Fin n) (s : Fin (p + 1)) :
    (A.submatrix (Fin.cons i (s.removeNth α)) α).det =
      (-1 : R) ^ s.val * bminor A i (α s) (s.removeNth α) :=
  calc
    _ = (-1 : R) ^ s.val * ((A.submatrix (Fin.cons i (s.removeNth α)) α)
.submatrix id (Fin.cycleRange s).symm).det := by
      rw [Matrix.det_permute']
      simp [← mul_assoc, ← pow_add]
    _ = (-1 : R) ^ s.val * bminor A i (α s) (s.removeNth α) := by
      congrm _ * Matrix.det ?_
      simp [Fin.cons_removeNth_eq_comp_cycleRange_symm]

/--
theorem `det_bordered_expand` / 定理 `det_bordered_expand`

English:
theorem det_bordered_expand
  given: (α : Fin (p + 1) -> Fin n) (i j : Fin n)
  proof: calc
  _ = A i j * pminor A α +
        ∑ s : Fin (p + 1), (-1 : R) ^ (s.val + 1) * A (α s) j *
          (A.submatrix (Fin.cons i (s.removeNth α)) α).det := by
      rw [bminor]; rw [Matrix.det_succ_column_zero]; rw [Fin.sum_univ_succ]; simp
  _ = pminor A α * A i j +
        ∑ s : Fin (p + 1),
   

中文:
定理 det_bordered_expand
  条件: (α : Fin (p + 1) -> Fin n) (i j : Fin n)
  证明: calc
  _ = A i j * pminor A α +
        ∑ s : Fin (p + 1), (-1 : R) ^ (s.val + 1) * A (α s) j *
          (A.submatrix (Fin.cons i (s.removeNth α)) α).det := by
      rw [bminor]; rw [Matrix.det_succ_column_zero]; rw [Fin.sum_univ_succ]; simp
  _ = pminor A α * A i j +
        ∑ s : Fin (p + 1),
   
-/
theorem det_bordered_expand (α : Fin (p + 1) -> Fin n) (i j : Fin n) :
    bminor A i j α =
      pminor A α * A i j - ∑ s : Fin (p + 1), bminor A i (α s) (s.removeNth α) * A (α s) j := calc
  _ = A i j * pminor A α +
        ∑ s : Fin (p + 1), (-1 : R) ^ (s.val + 1) * A (α s) j *
          (A.submatrix (Fin.cons i (s.removeNth α)) α).det := by
      rw [bminor]; rw [Matrix.det_succ_column_zero]; rw [Fin.sum_univ_succ]; simp
  _ = pminor A α * A i j +
        ∑ s : Fin (p + 1),
          ((-1 : R) ^ (s.val + 1) *
            (A.submatrix (Fin.cons i (s.removeNth α)) α).det) * A (α s) j := by
    simp only [mul_comm (A i j), mul_right_comm]
  _ = pminor A α * A i j +
      ∑ s : Fin (p + 1), -(bminor A i (α s) (s.removeNth α) * A (α s) j) := by
    simp only [det_submatrix_removeNth_eq_sign_mul_bminor, ← mul_assoc, ← pow_add]; aesop
  _ = pminor A α * A i j -
      ∑ s : Fin (p + 1), bminor A i (α s) (s.removeNth α) * A (α s) j := by
    simp only [Finset.sum_neg_distrib, sub_eq_add_neg]

/--
theorem `bminor_eq_zero_of_mem_range` / 定理 `bminor_eq_zero_of_mem_range`

English:
theorem bminor_eq_zero_of_mem_range
  proof: by
  obtain ⟨q, rfl⟩ := hk
  -- The repeated columns in the submatrix used in bminor are `0` and `q + 1`.
exact Matrix.det_zero_of_column_eq q.succ_ne_zero by simp

中文:
定理 bminor_eq_zero_of_mem_range
  证明: by
  obtain ⟨q, rfl⟩ := hk
  -- The repeated columns in the submatrix used in bminor are `0` and `q + 1`.
exact Matrix.det_zero_of_column_eq q.succ_ne_zero by simp
-/
theorem bminor_eq_zero_of_mem_range
    {k : Fin n} (α : Fin p -> Fin n) (i : Fin n) (hk : k in Set.range α) :
    bminor A i k α = 0 := by
  obtain ⟨q, rfl⟩ := hk
  -- The repeated columns in the submatrix used in bminor are `0` and `q + 1`.
exact Matrix.det_zero_of_column_eq q.succ_ne_zero by simp

/--
Definition of `S` / `S` 的定义

English:
definition S
  signature: (p : Nat) (i : Fin n)
  body: {α : Fin p -> Fin n | StrictMono (Fin.cons i α)}

中文:
定义 S
  签名: (p : 自然数) (i : Fin n)
  定义体: {α : Fin p -> Fin n | StrictMono (Fin.cons i α)}

Depends on / 依赖: Fin.cons, StrictMono
-/
def S (p : Nat) (i : Fin n) : Finset (Fin p -> Fin n) :=
  {α : Fin p -> Fin n | StrictMono (Fin.cons i α)}

/--
theorem `mem_S_iff` / 定理 `mem_S_iff`

English:
theorem mem_S_iff
  given: {p : Nat} {i : Fin n} {α : Fin p -> Fin n}
  proof: Finset.mem_filter_univ α

中文:
定理 mem_S_iff
  条件: {p : 自然数} {i : Fin n} {α : Fin p -> Fin n}
  证明: Finset.mem_filter_univ α

Depends on / 依赖: Finset, Finset.mem_filter_univ, mem_filter_univ
-/
theorem mem_S_iff {p : Nat} {i : Fin n} {α : Fin p -> Fin n} :
    α in S p i ↔ StrictMono (Fin.cons i α) :=
  Finset.mem_filter_univ α

/--
theorem `S_zero` / 定理 `S_zero`

English:
theorem S_zero
  given: (i : Fin n)
  statement: S 0 i = {![]}
  proof: by
  ext; simp [mem_S_iff, Fin.strictMono_iff_lt_succ, eq_iff_true_of_subsingleton]

中文:
定理 S_zero
  条件: (i : Fin n)
  结论: S 0 i = {![]}
  证明: by
  ext; simp [mem_S_iff, Fin.strictMono_iff_lt_succ, eq_iff_true_of_subsingleton]

Depends on / 依赖: Fin.strictMono_iff_lt_succ, eq_iff_true_of_subsingleton, mem_S_iff, strictMono_iff_lt_succ
-/
theorem S_zero (i : Fin n) : S 0 i = {![]} := by
  ext; simp [mem_S_iff, Fin.strictMono_iff_lt_succ, eq_iff_true_of_subsingleton]

/--
lemma `S_zero_eq_singleton` / 引理 `S_zero_eq_singleton`

English:
lemma S_zero_eq_singleton
  given: {p : Nat}
  statement: S p 0 = {Fin.succ}
  proof: by
  ext; simp [mem_S_iff]

中文:
引理 S_zero_eq_singleton
  条件: {p : 自然数}
  结论: S p 0 = {Fin.succ}
  证明: by
  ext; simp [mem_S_iff]
-/
@[simp] lemma S_zero_eq_singleton {p : Nat} : S p 0 = {Fin.succ} := by
  ext; simp [mem_S_iff]

/-! ## Decomposition `S_{p+1}(βᵢ) = { kα | k ∈ βᵢ, α ∈ S_p(β_k) }` -/

/--
theorem `S_succ_eq_biUnion` / 定理 `S_succ_eq_biUnion`

English:
theorem S_succ_eq_biUnion
  given: {p : Nat} (i : Fin n)
  proof: by
  ext α
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ioi, mem_S_iff]
  refine ⟨fun hα => ⟨α 0, (Fin.strictMono_cons.mp hα).1 0, Fin.tail α, ?_, Fin.cons_self_tail α⟩, ?_⟩
  · simp only [Fin.cons_self_tail]
    exact hα.comp Fin.strictMono_succ
  · rintro ⟨k, hk, u, hu, rfl⟩
    e

中文:
定理 S_succ_eq_biUnion
  条件: {p : 自然数} (i : Fin n)
  证明: by
  ext α
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ioi, mem_S_iff]
  refine ⟨fun hα => ⟨α 0, (Fin.strictMono_cons.mp hα).1 0, Fin.tail α, ?_, Fin.cons_self_tail α⟩, ?_⟩
  · simp only [Fin.cons_self_tail]
    exact hα.comp Fin.strictMono_succ
  · rintro ⟨k, hk, u, hu, rfl⟩
    e

Depends on / 依赖: Fin.cons_self_tail, Fin.strictMono_cons.mp, Fin.strictMono_succ, Fin.tail, Finset, Finset.mem_Ioi, Finset.mem_biUnion, Finset.mem_image, StrictMono, StrictMono.vecCons, cons_self_tail, mem_Ioi, mem_S_iff, mem_biUnion, mem_image, strictMono_cons, strictMono_succ, vecCons
-/
theorem S_succ_eq_biUnion {p : Nat} (i : Fin n) :
    S (p + 1) i = (Finset.Ioi i).biUnion fun k => (S p k).image (Fin.cons k) := by
  ext α
  simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_Ioi, mem_S_iff]
  refine ⟨fun hα => ⟨α 0, (Fin.strictMono_cons.mp hα).1 0, Fin.tail α, ?_, Fin.cons_self_tail α⟩, ?_⟩
  · simp only [Fin.cons_self_tail]
    exact hα.comp Fin.strictMono_succ
  · rintro ⟨k, hk, u, hu, rfl⟩
    exact StrictMono.vecCons hu hk

/--
lemma `exists_insertNth_mem_S` / 引理 `exists_insertNth_mem_S`

English:
lemma exists_insertNth_mem_S
  statement: {p : Nat} {i : Fin n} {α : Fin p -> Fin n} {k : Fin n}
  proof: by
  set t := ⨅ j in {j | k < α j}, j.castSucc with t_eq
  use t
  simp only [mem_S_iff, Fin.strictMono_cons] at ⊢ hα
  refine ⟨fun j => Fin.succAboveCases t ?_ ?_ j, ?_⟩
  · simp only [t_eq, Set.mem_ofPred_eq, Fin.strictMono_insertNth_iff, hα.2, lt_iInf_iff,
      le_iInf_iff, forall_exists_index, 

中文:
引理 exists_insertNth_mem_S
  结论: {p : 自然数} {i : Fin n} {α : Fin p -> Fin n} {k : Fin n}
  证明: by
  set t := ⨅ j in {j | k < α j}, j.castSucc with t_eq
  use t
  simp only [mem_S_iff, Fin.strictMono_cons] at ⊢ hα
  refine ⟨fun j => Fin.succAboveCases t ?_ ?_ j, ?_⟩
  · simp only [t_eq, Set.mem_ofPred_eq, Fin.strictMono_insertNth_iff, hα.2, lt_iInf_iff,
      le_iInf_iff, forall_exists_index, 

Depends on / 依赖: Fin.strictMono_cons, Fin.strictMono_insertNth_iff, Fin.succAboveCases, Set.mem_ofPred_eq, and_imp, castSucc, contrapose, exists_prop, forall_exists_index, h.lt_of_ne, hj.symm, iInf_le_iff_forall_lt, iInf_lt_iff, j.castSucc, k_ne, le_iInf_iff, lt_iInf_iff, lt_of_ne, mem_S_iff, mem_ofPred_eq
-/
lemma exists_insertNth_mem_S {p : Nat} {i : Fin n} {α : Fin p -> Fin n} {k : Fin n}
    (hα : α in S p i) (hik : i < k) (hk : k ∉ Set.range α) :
    exists t : Fin (p + 1), t.insertNth k α in S (p + 1) i := by
  set t := ⨅ j in {j | k < α j}, j.castSucc with t_eq
  use t
  simp only [mem_S_iff, Fin.strictMono_cons] at ⊢ hα
  refine ⟨fun j => Fin.succAboveCases t ?_ ?_ j, ?_⟩
  · simp only [t_eq, Set.mem_ofPred_eq, Fin.strictMono_insertNth_iff, hα.2, lt_iInf_iff,
      le_iInf_iff, forall_exists_index, and_imp, iInf_le_iff_forall_lt, iInf_lt_iff,
      exists_prop, true_and]
    refine ⟨fun j x hjx h => ?_, fun j h => ?_⟩
    · contrapose! h
      have k_ne (j : Fin p) : k != α j := fun hj => hk ⟨j, hj.symm⟩
      exact ⟨j, h.lt_of_ne (k_ne _), hjx⟩
    · obtain ⟨q, hkq, hqj⟩ := h j.succ j.castSucc_lt_succ
exact hkq.trans_le hα.2.monotone Fin.castSucc_lt_succ_iff.mp hqj
  · simpa
  · simpa using hα.1

variable (p) in
/--
Definition of `Eq1` / `Eq1` 的定义

English:
abbreviation Eq1
  signature: : Prop
  body: (Spec.stepEntry A)^[p] A = .of fun i j => (-1) ^ p * ∑ α in S p i, bminor A i j α

中文:
缩写 Eq1
  签名: : 命题
  定义体: (Spec.stepEntry A)^[p] A = .of fun i j => (-1) ^ p * ∑ α in S p i, bminor A i j α

Depends on / 依赖: Spec.stepEntry, bminor, stepEntry
-/
abbrev Eq1 : Prop :=
  (Spec.stepEntry A)^[p] A = .of fun i j => (-1) ^ p * ∑ α in S p i, bminor A i j α

/-! ## Equations (2) and (3): substituting the induction hypothesis -/

/--
theorem `paper_eq2` / 定理 `paper_eq2`

English:
theorem paper_eq2
  given: (i : Fin n) (hEq1 : Eq1 A p)
  proof: by
  calc
    (-∑ k in Finset.Ioi i, (Spec.stepEntry A)^[p] A k k) =
        (-1) ^ (p + 1) * ∑ k in Finset.Ioi i, ∑ α in S p k, bminor A k k α := by
      simp only [hEq1, Matrix.of_apply, ← Finset.mul_sum]
      ring
    _ = (-1) ^ (p + 1) * ∑ α in S (p + 1) i, pminor A α := by
      rw [S_succ_eq

中文:
定理 paper_eq2
  条件: (i : Fin n) (hEq1 : Eq1 A p)
  证明: by
  calc
    (-∑ k in Finset.Ioi i, (Spec.stepEntry A)^[p] A k k) =
        (-1) ^ (p + 1) * ∑ k in Finset.Ioi i, ∑ α in S p k, bminor A k k α := by
      simp only [hEq1, Matrix.of_apply, ← Finset.mul_sum]
      ring
    _ = (-1) ^ (p + 1) * ∑ α in S (p + 1) i, pminor A α := by
      rw [S_succ_eq

Depends on / 依赖: Fin.cons_, Fin.cons_inj.mp, Finset, Finset.Ioi, Finset.disjoint_left, Finset.mul_sum, Finset.sum_biUnion, Finset.sum_image, Matrix, Matrix.of_apply, Pairwise, PairwiseDisjoint, S_succ_eq_biUnion, Set.Pairwise, Set.PairwiseDisjoint, Spec.stepEntry, bminor, congrm, cons_, cons_inj
-/
theorem paper_eq2 (i : Fin n) (hEq1 : Eq1 A p) :
    (-∑ k in Finset.Ioi i, (Spec.stepEntry A)^[p] A k k) =
      (-1) ^ (p + 1) * ∑ α in S (p + 1) i, pminor A α := by
  calc
    (-∑ k in Finset.Ioi i, (Spec.stepEntry A)^[p] A k k) =
        (-1) ^ (p + 1) * ∑ k in Finset.Ioi i, ∑ α in S p k, bminor A k k α := by
      simp only [hEq1, Matrix.of_apply, ← Finset.mul_sum]
      ring
    _ = (-1) ^ (p + 1) * ∑ α in S (p + 1) i, pminor A α := by
      rw [S_succ_eq_biUnion]; rw [Finset.sum_biUnion]
      · congrm (((-1) ^ (p + 1) * ∑ k in Finset.Ioi i, ?_))
        symm
        exact Finset.sum_image fun _ _ _ _ hαβ => (Fin.cons_inj.mp hαβ).2
      · grind [Set.PairwiseDisjoint, Set.Pairwise, Finset.disjoint_left, Fin.cons_inj]

/--
theorem `paper_eq3` / 定理 `paper_eq3`

English:
theorem paper_eq3
  given: (i j : Fin n) (hEq1 : Eq1 A p)
  proof: by
  simp_rw [iterate_succ_apply', Spec.stepEntry_eq, Matrix.of_apply, paper_eq2 _ _ hEq1, hEq1,
    Matrix.of_apply, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  ring

中文:
定理 paper_eq3
  条件: (i j : Fin n) (hEq1 : Eq1 A p)
  证明: by
  simp_rw [iterate_succ_apply', Spec.stepEntry_eq, Matrix.of_apply, paper_eq2 _ _ hEq1, hEq1,
    Matrix.of_apply, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  ring

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_mul, Matrix, Matrix.of_apply, Spec.stepEntry_eq, iterate_succ_apply, mul_assoc, mul_sum, of_apply, paper_eq2, simp_rw, stepEntry_eq, sum_mul
-/
theorem paper_eq3 (i j : Fin n) (hEq1 : Eq1 A p) :
    ((Spec.stepEntry A)^[p + 1] A) i j =
      (-1) ^ (p + 1) * (∑ α in S (p + 1) i, pminor A α * A i j -
        ∑ k in Finset.Ioi i, ∑ α in S p i, bminor A i k α * A k j) := by
  simp_rw [iterate_succ_apply', Spec.stepEntry_eq, Matrix.of_apply, paper_eq2 _ _ hEq1, hEq1,
    Matrix.of_apply, mul_assoc, Finset.sum_mul, ← Finset.mul_sum]
  ring

/-! ## Equation (5): first-column Laplace expansion -/

/--
theorem `paper_eq5` / 定理 `paper_eq5`

English:
theorem paper_eq5
  given: (i j : Fin n)
  proof: calc
  _ = ∑ α in S (p + 1) i, (pminor A α * A i j -
        ∑ t : Fin (p + 1), bminor A i (α t) (t.removeNth α) * A (α t) j) := by
exact Finset.sum_congr rfl by simp [det_bordered_expand]
  _ = ∑ α in S (p + 1) i, pminor A α * A i j -
        ∑ α in S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α t) 

中文:
定理 paper_eq5
  条件: (i j : Fin n)
  证明: calc
  _ = ∑ α in S (p + 1) i, (pminor A α * A i j -
        ∑ t : Fin (p + 1), bminor A i (α t) (t.removeNth α) * A (α t) j) := by
exact Finset.sum_congr rfl by simp [det_bordered_expand]
  _ = ∑ α in S (p + 1) i, pminor A α * A i j -
        ∑ α in S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α t) 
-/
theorem paper_eq5 (i j : Fin n) :
    ∑ α in S (p + 1) i, bminor A i j α =
      ∑ α in S (p + 1) i, pminor A α * A i j -
      ∑ α in S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α t) (t.removeNth α) * A (α t) j := calc
  _ = ∑ α in S (p + 1) i, (pminor A α * A i j -
        ∑ t : Fin (p + 1), bminor A i (α t) (t.removeNth α) * A (α t) j) := by
exact Finset.sum_congr rfl by simp [det_bordered_expand]
  _ = ∑ α in S (p + 1) i, pminor A α * A i j -
        ∑ α in S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α t) (t.removeNth α) * A (α t) j := by
    rw [Finset.sum_sub_distrib]

/-! ## Comparing equations (3) and (5): reindex by sorted insert/delete -/

/--
theorem `paper_eq3_eq5_off_diag` / 定理 `paper_eq3_eq5_off_diag`

English:
theorem paper_eq3_eq5_off_diag
  given: (i j : Fin n)
  proof: by
  rw [Finset.sum_comm]; rw [← Finset.sum_product']; rw [← Finset.sum_product']
  -- The right-hand summand is the left-hand summand composed with the deletion map
  --
  -- d (α, t) := (t.removeNth α, α t).
  --
  -- This map is injective, and every left-hand summand outside its image is zero,
  

中文:
定理 paper_eq3_eq5_off_diag
  条件: (i j : Fin n)
  证明: by
  rw [Finset.sum_comm]; rw [← Finset.sum_product']; rw [← Finset.sum_product']
  -- The right-hand summand is the left-hand summand composed with the deletion map
  --
  -- d (α, t) := (t.removeNth α, α t).
  --
  -- This map is injective, and every left-hand summand outside its image is zero,
  

Depends on / 依赖: Finset, Finset.sum_comm, Finset.sum_product, sum_comm, sum_product
-/
theorem paper_eq3_eq5_off_diag (i j : Fin n) :
    ∑ k in Finset.Ioi i, ∑ α in S p i, bminor A i k α * A k j =
      ∑ α' in S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α' t) (t.removeNth α') * A (α' t) j := by
  rw [Finset.sum_comm]; rw [← Finset.sum_product']; rw [← Finset.sum_product']
  -- The right-hand summand is the left-hand summand composed with the deletion map
  --
  -- d (α, t) := (t.removeNth α, α t).
  --
  -- This map is injective, and every left-hand summand outside its image is zero,
  -- so `sum_of_injOn` applies.
  symm
  refine Finset.sum_of_injOn (fun ⟨α, k⟩ => ⟨k.removeNth α, α k⟩) ?_ ?_ ?_ ?_
  · simp only [Set.InjOn, Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ,
      and_true, Finset.mem_coe, Prod.mk.injEq, and_imp, Prod.forall, mem_S_iff, Fin.strictMono_cons]
    intros α k hi hiα α' k' hj hiα' hremove hvalue
    suffices hrange : Set.range α = Set.range α' by
      rw [hiα.range_inj hiα'] at hrange
      subst α'
      exact ⟨rfl, hiα.injective hvalue⟩
    calc
      _ = Set.insert (α k) (Set.range (k.removeNth α)) := by
        rw [← Fin.range_insertNth]; rw [Fin.insertNth_self_removeNth]
      _ = Set.insert (α' k') (Set.range (k'.removeNth α')) := by
        rw [hvalue]; rw [hremove]
      _ = Set.range α' := by
        rw [← Fin.range_insertNth]; rw [Fin.insertNth_self_removeNth]
  · rintro ⟨α, t⟩ hα
    simp only [Finset.coe_product, Finset.coe_univ, Set.mem_prod, Set.mem_univ, and_true,
      Finset.mem_coe, Finset.coe_Ioi, Set.mem_Ioi, mem_S_iff, Fin.strictMono_cons] at hα ⊢
    obtain ⟨hbound, hmono⟩ := hα
    exact ⟨⟨fun q => hbound (t.succAbove q), hmono.removeNth t⟩, hbound t⟩
  · rintro ⟨α, k⟩ htarget hnotmem
    simp only [Finset.mem_product, Finset.mem_Ioi] at htarget
    obtain ⟨hα, hk⟩ := htarget
    by_cases hoccurs : k in Set.range α
    · -- The border column `k` is repeated among the columns indexed by `α` and
      -- so the bordered minor is 0.
      rw [bminor_eq_zero_of_mem_range A α i hoccurs]; rw [zero_mul]
    · contrapose hnotmem
      obtain ⟨t, ht⟩ := exists_insertNth_mem_S hα hk hoccurs
      exact ⟨(t.insertNth k α, t), by simpa, by simp⟩
  · simp

/--
theorem `paper_eq1` / 定理 `paper_eq1`

English:
theorem paper_eq1
  statement: Eq1 A p
  proof: by
  induction p with
  | zero =>
    ext i j
    simp [iterate_zero_apply, S_zero, bminor]
  | succ p ih =>
    ext i j
    rw [Matrix.of_apply]; rw [paper_eq3 A i j ih]; rw [paper_eq5 A]; rw [paper_eq3_eq5_off_diag A]

中文:
定理 paper_eq1
  结论: Eq1 A p
  证明: by
  induction p with
  | zero =>
    ext i j
    simp [iterate_zero_apply, S_zero, bminor]
  | succ p ih =>
    ext i j
    rw [Matrix.of_apply]; rw [paper_eq3 A i j ih]; rw [paper_eq5 A]; rw [paper_eq3_eq5_off_diag A]

Depends on / 依赖: Matrix, Matrix.of_apply, S_zero, bminor, iterate_zero_apply, of_apply, paper_eq3, paper_eq3_eq5_off_diag, paper_eq5
-/
theorem paper_eq1 : Eq1 A p := by
  induction p with
  | zero =>
    ext i j
    simp [iterate_zero_apply, S_zero, bminor]
  | succ p ih =>
    ext i j
    rw [Matrix.of_apply]; rw [paper_eq3 A i j ih]; rw [paper_eq5 A]; rw [paper_eq3_eq5_off_diag A]

/-! ## instantiating equation (1) to prove Theorem 1 -/

/--
theorem `birdDetSpec_eq_det` / 定理 `birdDetSpec_eq_det`

English:
theorem birdDetSpec_eq_det
  given: (A : Matrix (Fin n) (Fin n) R)
  proof: by
  cases n with
  | zero => simp
  | succ k =>
    have : ∑ α in S k 0, bminor A 0 0 α = A.det := by simp [bminor]
    rw [Spec.birdDetSpec_succ]; rw [paper_eq1]; rw [Matrix.of_apply]; rw [← mul_assoc]; rw [← pow_add]; aesop

中文:
定理 birdDetSpec_eq_det
  条件: (A : Matrix (Fin n) (Fin n) R)
  证明: by
  cases n with
  | zero => simp
  | succ k =>
    have : ∑ α in S k 0, bminor A 0 0 α = A.det := by simp [bminor]
    rw [Spec.birdDetSpec_succ]; rw [paper_eq1]; rw [Matrix.of_apply]; rw [← mul_assoc]; rw [← pow_add]; aesop

Depends on / 依赖: A.det, Matrix, Matrix.of_apply, Spec.birdDetSpec_succ, birdDetSpec_succ, bminor, mul_assoc, of_apply, paper_eq1, pow_add
-/
theorem birdDetSpec_eq_det (A : Matrix (Fin n) (Fin n) R) :
    Matrix.det A = Spec.birdDet A := by
  cases n with
  | zero => simp
  | succ k =>
    have : ∑ α in S k 0, bminor A 0 0 α = A.det := by simp [bminor]
    rw [Spec.birdDetSpec_succ]; rw [paper_eq1]; rw [Matrix.of_apply]; rw [← mul_assoc]; rw [← pow_add]; aesop

/-- `BirdDet.birdDet n A` computes the determinant of the `n × n` matrix whose
  entries are stored in row-major order in `A`. -/
public theorem det_eq_birdDet (A : Array R) (hA : A.size = n * n) :
    Matrix.det (.ofArray A hA) = birdDet n A := by
  rw [birdDet_eq_birdDetSpec]; rw [birdDetSpec_eq_det]

end BirdDet
