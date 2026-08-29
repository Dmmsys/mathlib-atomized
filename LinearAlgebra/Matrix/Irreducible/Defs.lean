/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Data.Matrix.Mul

/-!
# Irreducibility and primitivity of nonnegative matrices

This file develops a graph-theoretic interface for studying the properties of nonnegative square
matrices.

We associate a directed graph (quiver) with a matrix `A`, where an edge `i ⟶ j` exists if and only
if the entry `A i j` is strictly positive. This allows translating algebraic properties of the
matrix (like powers) into graph-theoretic properties of its quiver (like the existence of paths).

## Main definitions

* `Matrix.toQuiver A`: The quiver associated with a matrix `A`, where an edge `i ⟶ j` exists if
  `0 < A i j`.
* `Matrix.IsIrreducible A`: A matrix `A` is defined as irreducible if it is entrywise nonnegative
  and its associated quiver `toQuiver A` is strongly connected. The theorem
  `Matrix.isIrreducible_iff_exists_pow_pos` proves this graph-theoretic definition is equivalent
  to the algebraic one in seneta2006 (Def 1.6, p.18): for every pair of indices `(i, j)`, there
  exists a positive integer `k` such that `(A ^ k) i j > 0`.
* `Matrix.IsPrimitive A`: A matrix `A` is primitive if it is nonnegative and some power `A ^ k`
  is strictly positive (all entries are `> 0`), (seneta2006, Definition 1.1, p.14).

## Main results

* `Matrix.pow_apply_pos_iff_nonempty_path`: Establishes the link between matrix powers and graph
  theory:
  `(A ^ k) i j > 0` if and only if there is a path of length `k` from `i` to `j` in `toQuiver A`.
* `Matrix.isIrreducible_iff_exists_pow_pos`: Shows the equivalence between the graph-theoretic
  definition of irreducibility (strong connectivity) and the algebraic one (existence of a
  positive entry in some power).
* `Matrix.IsPrimitive.to_IsIrreducible`: Proves that a primitive matrix is also irreducible
  (Seneta, p.14).
* `Matrix.IsIrreducible.transpose`: Shows that the irreducibility property is preserved under
  transposition.

## Implementation notes

Throughout we work over a linearly ordered ring `R`. Some results require stronger assumptions,
like `PosMulStrictMono R` or `Nontrivial R`. Some statements expand matrix powers and thus require
`[DecidableEq n]` to reason about finite sums.

## TODO

Refactor to use digraphs instead of quivers. A prerequisite for this refactor
is paths in digraphs.

## References

* [E. Seneta, *Non-negative Matrices and Markov Chains*][seneta2006]

## Tags

matrix, nonnegative, positive, power, quiver, graph, irreducible, primitive, perron-frobenius
-/

@[expose] public section
namespace Matrix

open Quiver Quiver.Path

variable {n R : Type*} [Ring R] [LinearOrder R]

/-- The directed graph (quiver) associated with a matrix `A`,
with an edge `i ⟶ j` iff `0 < A i j`. -/
@[instance_reducible]
/--
Definition of `toQuiver` / `toQuiver` 的定义

English:
definition toQuiver
  signature: (A : Matrix n n R)
  body: ⟨fun i j => PLift (0 < A i j)⟩

中文:
定义 toQuiver
  签名: (A : Matrix n n R)
  定义体: ⟨fun i j => PLift (0 < A i j)⟩
-/
def toQuiver (A : Matrix n n R) : Quiver n :=
  ⟨fun i j => PLift (0 < A i j)⟩

/--
Definition of `IsIrreducible` / `IsIrreducible` 的定义

English:
structure IsIrreducible
  parameters: (A : Matrix n n R)
  axioms and operations (2):
    - nonneg((i j : n)) : 0 <= A i j
    - connected : @IsSStronglyConnected n (toQuiver A)

中文:
结构 IsIrreducible
  参数: (A : Matrix n n R)
  公理与运算 (2 个):
    - nonneg((i j : n)) : 0 <= A i j
    - connected : @IsSStronglyConnected n (toQuiver A)
-/
@[mk_iff] structure IsIrreducible (A : Matrix n n R) : Prop where
  nonneg (i j : n) : 0 <= A i j
  connected : @IsSStronglyConnected n (toQuiver A)

/--
Definition of `IsPrimitive` / `IsPrimitive` 的定义

English:
structure IsPrimitive
  parameters: [Fintype n] [DecidableEq n] (A : Matrix n n R)
  axioms and operations (2):
    - nonneg((i j : n)) : 0 <= A i j
    - exists_pos_pow : exists k > 0, forall i j, 0 < (A ^ k) i j

中文:
结构 IsPrimitive
  参数: [Fintype n] [DecidableEq n] (A : Matrix n n R)
  公理与运算 (2 个):
    - nonneg((i j : n)) : 0 <= A i j
    - exists_pos_pow : 存在 k > 0, 对任意 i j, 0 < (A ^ k) i j
-/
@[mk_iff] structure IsPrimitive [Fintype n] [DecidableEq n] (A : Matrix n n R) : Prop where
  nonneg (i j : n) : 0 <= A i j
  exists_pos_pow : exists k > 0, forall i j, 0 < (A ^ k) i j

variable {A : Matrix n n R}

/--
lemma `IsIrreducible.exists_pos` / 引理 `IsIrreducible.exists_pos`

English:
lemma IsIrreducible.exists_pos
  statement: [Nontrivial n]
  proof: by
  let : Quiver n := toQuiver A
  by_contra h_row
  have no_out : forall j : n, IsEmpty (i ⟶ j) :=
    fun j => ⟨fun e => h_row ⟨j, e.down⟩⟩
  obtain ⟨j, hij⟩ := exists_pair_ne n
  obtain ⟨p, hp_pos⟩ := h_irr.connected i j
  have h_le : 1 <= p.length := Nat.succ_le_of_lt hp_pos
  have ⟨v, p₁, p₂, 

中文:
引理 IsIrreducible.exists_pos
  结论: [Nontrivial n]
  证明: by
  let : Quiver n := toQuiver A
  by_contra h_row
  have no_out : forall j : n, IsEmpty (i ⟶ j) :=
    fun j => ⟨fun e => h_row ⟨j, e.down⟩⟩
  obtain ⟨j, hij⟩ := exists_pair_ne n
  obtain ⟨p, hp_pos⟩ := h_irr.connected i j
  have h_le : 1 <= p.length := Nat.succ_le_of_lt hp_pos
  have ⟨v, p₁, p₂, 

Depends on / 依赖: IsEmpty, Nat.succ_le_of_lt, Quiver, Quiver.Path.length_ne_zero_iff_eq_cons, _hp_eq, connected, e.down, exists_eq_comp_of_le_length, exists_pair_ne, h_irr, h_irr.connected, h_le, h_row, hlen_ne, hp_pos, length, length_ne_zero_iff_eq_cons, no_out, p.exists_eq_comp_of_le_length, p.length
-/
lemma IsIrreducible.exists_pos [Nontrivial n]
    (h_irr : IsIrreducible A) (i : n) :
    exists j, 0 < A i j := by
  let : Quiver n := toQuiver A
  by_contra h_row
  have no_out : forall j : n, IsEmpty (i ⟶ j) :=
    fun j => ⟨fun e => h_row ⟨j, e.down⟩⟩
  obtain ⟨j, hij⟩ := exists_pair_ne n
  obtain ⟨p, hp_pos⟩ := h_irr.connected i j
  have h_le : 1 <= p.length := Nat.succ_le_of_lt hp_pos
  have ⟨v, p₁, p₂, _hp_eq, hp₁_len⟩ := p.exists_eq_comp_of_le_length (n := 1) h_le
  have hlen_ne : p₁.length != 0 := by simp [hp₁_len]
  obtain ⟨c, p', e, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons (p := p₁)).1 (by lia)
  obtain ⟨rfl⟩ : i = c := Quiver.Path.eq_of_length_zero p' (by simp_all)
  exact (no_out _).false e

/--
theorem `pow_apply_pos_iff_nonempty_path` / 定理 `pow_apply_pos_iff_nonempty_path`

English:
theorem pow_apply_pos_iff_nonempty_path
  proof: toQuiver A
    0 < (A ^ k) i j ↔ Nonempty {p : Path i j // p.length = k} := by
  let := toQuiver A
  induction k generalizing i j with
  | zero =>
    refine ⟨fun h_pos => ?_, fun ⟨p, hp⟩ => ?_⟩
    · rcases eq_or_ne i j with rfl | h_eq
      · exact ⟨⟨Quiver.Path.nil, rfl⟩⟩
      · simp_all
    · s

中文:
定理 pow_apply_pos_iff_nonempty_path
  证明: toQuiver A
    0 < (A ^ k) i j ↔ Nonempty {p : Path i j // p.length = k} := by
  let := toQuiver A
  induction k generalizing i j with
  | zero =>
    refine ⟨fun h_pos => ?_, fun ⟨p, hp⟩ => ?_⟩
    · rcases eq_or_ne i j with rfl | h_eq
      · exact ⟨⟨Quiver.Path.nil, rfl⟩⟩
      · simp_all
    · s

Depends on / 依赖: toQuiver
-/
theorem pow_apply_pos_iff_nonempty_path
    [Fintype n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (hA : forall i j, 0 <= A i j) (k : Nat) (i j : n) :
    letI := toQuiver A
    0 < (A ^ k) i j ↔ Nonempty {p : Path i j // p.length = k} := by
  let := toQuiver A
  induction k generalizing i j with
  | zero =>
    refine ⟨fun h_pos => ?_, fun ⟨p, hp⟩ => ?_⟩
    · rcases eq_or_ne i j with rfl | h_eq
      · exact ⟨⟨Quiver.Path.nil, rfl⟩⟩
      · simp_all
    · simp [Quiver.Path.eq_of_length_zero p hp]
  | succ m ih =>
    rw [pow_succ]; rw [mul_apply]
    constructor
    · intro h_pos
      obtain ⟨l, hl_mem, hl_pos⟩ :
          exists l in (Finset.univ : Finset n), 0 < (A ^ m) i l * A l j := by
        simpa [Finset.sum_pos_iff_of_nonneg
                 (fun x _ => mul_nonneg (pow_apply_nonneg hA m i x) (hA x j))]
          using h_pos
      have hAm_nonneg : 0 <= (A ^ m) i l := pow_apply_nonneg hA m i l
      have hA_nonneg' : 0 <= A l j := hA l j
      have h_Am : 0 < (A ^ m) i l := by by_contra! h; simp [le_antisymm h hAm_nonneg] at hl_pos
      have h_A : 0 < A l j := by by_contra! h; simp [le_antisymm h hA_nonneg'] at hl_pos
      obtain ⟨⟨p, rfl⟩⟩ := (ih i l).mp h_Am
      exact ⟨p.cons (PLift.up h_A), by simp⟩
    · rintro ⟨p, hp_len⟩
      cases p with
      | nil => simp [Quiver.Path.length] at hp_len
      | @cons b _ q e =>
        simp only [Quiver.Path.length_cons, Nat.succ.injEq] at hp_len
        have h_Am_pos : 0 < (A ^ m) i b := (ih i b).mpr ⟨q, hp_len⟩
        let h_A_pos := e
        have h_prod : 0 < (A ^ m) i b * A b j := mul_pos h_Am_pos h_A_pos.down
        exact
          (Finset.sum_pos_iff_of_nonneg
            (fun x _ => mul_nonneg (pow_apply_nonneg hA m i x) (hA x j))).2
            ⟨b, Finset.mem_univ b, h_prod⟩

/--
theorem `isIrreducible_iff_exists_pow_pos` / 定理 `isIrreducible_iff_exists_pow_pos`

English:
theorem isIrreducible_iff_exists_pow_pos
  proof: by
  let : Quiver n := toQuiver A
  constructor
  · intro h_irr i j
    obtain ⟨p, hp_len⟩ := h_irr.2 i j
    refine ⟨p.length, hp_len, ?_⟩
    have : Nonempty {q : Path i j // q.length = p.length} := ⟨⟨p, rfl⟩⟩
    have hpos :=
      (pow_apply_pos_iff_nonempty_path (A := A) hA p.length i j).2 this

中文:
定理 isIrreducible_iff_exists_pow_pos
  证明: by
  let : Quiver n := toQuiver A
  constructor
  · intro h_irr i j
    obtain ⟨p, hp_len⟩ := h_irr.2 i j
    refine ⟨p.length, hp_len, ?_⟩
    have : Nonempty {q : Path i j // q.length = p.length} := ⟨⟨p, rfl⟩⟩
    have hpos :=
      (pow_apply_pos_iff_nonempty_path (A := A) hA p.length i j).2 this

Depends on / 依赖: Nonempty, Quiver, h_exists, h_irr, hk_entry, hk_pos, hp_len, length, p.length, pow_apply_pos_iff_nonempty_path, q.length, toQuiver
-/
theorem isIrreducible_iff_exists_pow_pos
    [Fintype n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (hA : forall i j, 0 <= A i j) :
    IsIrreducible A ↔ forall i j, exists k > 0, 0 < (A ^ k) i j := by
  let : Quiver n := toQuiver A
  constructor
  · intro h_irr i j
    obtain ⟨p, hp_len⟩ := h_irr.2 i j
    refine ⟨p.length, hp_len, ?_⟩
    have : Nonempty {q : Path i j // q.length = p.length} := ⟨⟨p, rfl⟩⟩
    have hpos :=
      (pow_apply_pos_iff_nonempty_path (A := A) hA p.length i j).2 this
    simpa using hpos
  · intro h_exists
    constructor
    · exact hA
    · intro i j
      obtain ⟨k, hk_pos, hk_entry⟩ := h_exists i j
      obtain ⟨⟨p, rfl⟩⟩ :=
        (pow_apply_pos_iff_nonempty_path (A := A) hA k i j).mp hk_entry
      exact ⟨p, hk_pos⟩

/--
theorem `IsPrimitive.isIrreducible` / 定理 `IsPrimitive.isIrreducible`

English:
theorem IsPrimitive.isIrreducible
  proof: by
  obtain ⟨h_nonneg, k, hk_pos, hk_all⟩ := h_prim
  rw [isIrreducible_iff_exists_pow_pos h_nonneg]
  aesop

中文:
定理 IsPrimitive.isIrreducible
  证明: by
  obtain ⟨h_nonneg, k, hk_pos, hk_all⟩ := h_prim
  rw [isIrreducible_iff_exists_pow_pos h_nonneg]
  aesop

Depends on / 依赖: h_nonneg, h_prim, hk_all, hk_pos, isIrreducible_iff_exists_pow_pos
-/
theorem IsPrimitive.isIrreducible
    [Fintype n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (h_prim : IsPrimitive A) : IsIrreducible A := by
  obtain ⟨h_nonneg, k, hk_pos, hk_all⟩ := h_prim
  rw [isIrreducible_iff_exists_pow_pos h_nonneg]
  aesop

/-! ## Transposition -/

/--
Definition of `transposePath` / `transposePath` 的定义

English:
definition transposePath
  signature: {i j : n} (p : @Quiver.Path n A.toQuiver i j)
  body: by
  letI : Quiver n := toQuiver A
  induction p with
  | nil =>
    exact (@Quiver.Path.nil _ (toQuiver Aᵀ) _)
  | @cons b c q e ih =>
    have eT : 0 < (Aᵀ) c b := by
      simpa [Matrix.transpose_apply] using e.down
    exact (@Quiver.Path.comp n (toQuiver Aᵀ) c b i (@Quiver.Hom.toPath n (toQuive

中文:
定义 transposePath
  签名: {i j : n} (p : @Quiver.Path n A.toQuiver i j)
  定义体: by
  letI : Quiver n := toQuiver A
  induction p with
  | nil =>
    exact (@Quiver.Path.nil _ (toQuiver Aᵀ) _)
  | @cons b c q e ih =>
    have eT : 0 < (Aᵀ) c b := by
      simpa [Matrix.transpose_apply] using e.down
    exact (@Quiver.Path.comp n (toQuiver Aᵀ) c b i (@Quiver.Hom.toPath n (toQuive

Depends on / 依赖: Matrix, Matrix.transpose_apply, PLift.up, Quiver, Quiver.Hom.toPath, Quiver.Path.comp, Quiver.Path.nil, e.down, toPath, toQuiver, transpose_apply
-/
def transposePath {i j : n} (p : @Quiver.Path n A.toQuiver i j) :
    @Quiver.Path n Aᵀ.toQuiver j i := by
  letI : Quiver n := toQuiver A
  induction p with
  | nil =>
    exact (@Quiver.Path.nil _ (toQuiver Aᵀ) _)
  | @cons b c q e ih =>
    have eT : 0 < (Aᵀ) c b := by
      simpa [Matrix.transpose_apply] using e.down
    exact (@Quiver.Path.comp n (toQuiver Aᵀ) c b i (@Quiver.Hom.toPath n (toQuiver Aᵀ) c b
      (PLift.up eT)) ih)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `IsIrreducible.transpose` / 定理 `IsIrreducible.transpose`

English:
theorem IsIrreducible.transpose
  given: (hA : IsIrreducible A)
  statement: IsIrreducible Aᵀ
  proof: by
  have hA_T_nonneg : forall i j, 0 <= Aᵀ i j := fun i j => by
    simpa [Matrix.transpose_apply] using hA.nonneg j i
  refine ⟨hA_T_nonneg, ?_⟩
  intro i j
  let : Quiver n := toQuiver A
  obtain ⟨p, hp_pos⟩ := hA.connected j i
  cases p with
  | nil =>
    simp at hp_pos
  | @cons b _ q e =>
   

中文:
定理 IsIrreducible.transpose
  条件: (hA : IsIrreducible A)
  结论: IsIrreducible Aᵀ
  证明: by
  have hA_T_nonneg : forall i j, 0 <= Aᵀ i j := fun i j => by
    simpa [Matrix.transpose_apply] using hA.nonneg j i
  refine ⟨hA_T_nonneg, ?_⟩
  intro i j
  let : Quiver n := toQuiver A
  obtain ⟨p, hp_pos⟩ := hA.connected j i
  cases p with
  | nil =>
    simp at hp_pos
  | @cons b _ q e =>
   

Depends on / 依赖: Matrix, Matrix.transpose_apply, Quiver, Quiver.Path.length_comp, Quiver.Path.length_toPath, connected, hA.connected, hA.nonneg, hA_T_nonneg, hp_pos, length_comp, length_toPath, nonneg, q.cons, toQuiver, transposePath, transpose_apply
-/
theorem IsIrreducible.transpose (hA : IsIrreducible A) : IsIrreducible Aᵀ := by
  have hA_T_nonneg : forall i j, 0 <= Aᵀ i j := fun i j => by
    simpa [Matrix.transpose_apply] using hA.nonneg j i
  refine ⟨hA_T_nonneg, ?_⟩
  intro i j
  let : Quiver n := toQuiver A
  obtain ⟨p, hp_pos⟩ := hA.connected j i
  cases p with
  | nil =>
    simp at hp_pos
  | @cons b _ q e =>
    let qT := transposePath (A := A) (q.cons e)
    let : Quiver n := toQuiver Aᵀ
    use qT
    simp [qT, transposePath, Quiver.Path.length_comp, Quiver.Path.length_toPath]

@[simp]
/--
theorem `isIrreducible_transpose_iff` / 定理 `isIrreducible_transpose_iff`

English:
theorem isIrreducible_transpose_iff
  proof: by
  by_cases hA_nonneg : forall i j, 0 <= A i j
  · exact ⟨fun h =>
    let hA_T_nonneg : forall i j, 0 <= (Aᵀ) i j := fun i j => by
      simpa [Matrix.transpose_apply] using hA_nonneg j i
    IsIrreducible.transpose h,
   fun h => IsIrreducible.transpose h⟩
  · have : ¬ Aᵀ.IsIrreducible := by
   

中文:
定理 isIrreducible_transpose_iff
  证明: by
  by_cases hA_nonneg : forall i j, 0 <= A i j
  · exact ⟨fun h =>
    let hA_T_nonneg : forall i j, 0 <= (Aᵀ) i j := fun i j => by
      simpa [Matrix.transpose_apply] using hA_nonneg j i
    IsIrreducible.transpose h,
   fun h => IsIrreducible.transpose h⟩
  · have : ¬ Aᵀ.IsIrreducible := by
   

Depends on / 依赖: A.IsIrreducible, IsIrreducible, IsIrreducible.transpose, Matrix, Matrix.transpose_apply, hA_T_nonneg, hA_nonneg, implies_true, isIrreducible_iff, isSStronglyConnected_iff, nonpos_iff_eq_zero, not_and, not_exists, not_forall, not_lt, not_true_eq_false, transpose, transpose_apply
-/
theorem isIrreducible_transpose_iff :
    Aᵀ.IsIrreducible ↔ A.IsIrreducible := by
  by_cases hA_nonneg : forall i j, 0 <= A i j
  · exact ⟨fun h =>
    let hA_T_nonneg : forall i j, 0 <= (Aᵀ) i j := fun i j => by
      simpa [Matrix.transpose_apply] using hA_nonneg j i
    IsIrreducible.transpose h,
   fun h => IsIrreducible.transpose h⟩
  · have : ¬ Aᵀ.IsIrreducible := by
      rw [isIrreducible_iff]
      simp only [transpose_apply, isSStronglyConnected_iff, not_and, not_forall, not_exists,
        not_lt, nonpos_iff_eq_zero]
      intro a; simp_all only [implies_true, not_true_eq_false]
    have : ¬ A.IsIrreducible := by
      rw [isIrreducible_iff]; simp_all only [not_forall, not_le, isSStronglyConnected_iff,
      not_and, not_exists, not_lt, nonpos_iff_eq_zero, isEmpty_Prop, IsEmpty.forall_iff]
    simp_all only [not_forall, not_le]

end Matrix
