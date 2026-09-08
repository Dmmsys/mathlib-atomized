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
/-
**Matrix.toQuiver** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：toQuiver (A : Matrix n n R) : Quiver n
参数：A : Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The directed graph (quiver) associated with a matrix `A`,
with an edge `i ⟶ j` iff `0 < A i j`.
-/
def toQuiver (A : Matrix n n R) : Quiver n :=
  ⟨fun i j => PLift (0 < A i j)⟩

/-- A matrix `A` is irreducible if it is entrywise nonnegative and
its quiver of positive entries (`toQuiver A`) is strongly connected. -/
/-
**Matrix.IsIrreducible** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matrix`。
形式化陈述：{n : Type u_1} → {R : Type u_2} → [Ring R] → [LinearOrder R] → Matrix n n 
R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix `A` is irreducible if it is entrywise nonnegative and
its quiver of positive entries (`toQuiver A`) is strongly connected.
-/
@[mk_iff] structure IsIrreducible (A : Matrix n n R) : Prop where
  nonneg (i j : n) : 0 ≤ A i j
  connected : @IsSStronglyConnected n (toQuiver A)

/-- A matrix `A` is primitive if it is entrywise nonnegative
and some positive power has all entries strictly positive. -/
/-
**Matrix.IsPrimitive** 是 Mathlib 中的一个归纳类型，位于命名空间 `Matrix`。
形式化陈述：{n : Type u_1} → {R : Type u_2} → [Ring R] → [LinearOrder R] → [Fintype n]
 → [DecidableEq n] → Matrix n n R → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix `A` is primitive if it is entrywise nonnegative
and some positive power has all entries strictly positive.
-/
@[mk_iff] structure IsPrimitive [Fintype n] [DecidableEq n] (A : Matrix n n R) : Prop where
  nonneg (i j : n) : 0 ≤ A i j
  exists_pos_pow : ∃ k > 0, ∀ i j, 0 < (A ^ k) i j

variable {A : Matrix n n R}

/-- If `A` is irreducible and `n` is non-trivial then every row has a positive entry. -/
/-
**Matrix.IsIrreducible.exists_pos** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsIrreducibl
e`。
形式化陈述：∀ {n : Type u_1} {R : Type u_2} [inst : Ring R] [inst_1 : LinearOrder R] {
A : Matrix n n R} [Nontrivial n],   A.IsIrreducible → ∀ (i : n), ∃ j, 0 < A i j
参数：i : n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Matrix.IsIrreducible.connected`：∀ {n : Type u_1} {R : Type u_2} [inst : 
Ring R] [inst_1 : LinearOrder R] {A : Matrix n n R},   A.IsIrreducible → Quiver.
IsSStronglyConnected…
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Quiver.Path.exists_eq_comp_of_le_length`：exists_eq_comp_of_le_length {n 
: Nat} (hn : n <= p.length) : exists (v : V) (p₁ : Path a v) (p₂ : Path v b), p 
= p₁.comp p₂ ∧ p₁.length = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Quiver.Path.length_ne_zero_iff_eq_cons`：length_ne_zero_iff_eq_cons : p.l
ength != 0 ↔ exists (c : V) (p' : Path a c) (e : c ⟶ b), p = p'.cons e
· 使用定理 `Quiver.Path.eq_of_length_zero`：eq_of_length_zero (p : Path a b) (hzero :
 p.length = 0) : a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `A` is irreducible and `n` is non-trivial then every row has a positive entry
.
-/
lemma IsIrreducible.exists_pos [Nontrivial n]
    (h_irr : IsIrreducible A) (i : n) :
    ∃ j, 0 < A i j := by
  let : Quiver n := toQuiver A
  by_contra h_row
  have no_out : ∀ j : n, IsEmpty (i ⟶ j) :=
    fun j => ⟨fun e => h_row ⟨j, e.down⟩⟩
  obtain ⟨j, hij⟩ := exists_pair_ne n
  obtain ⟨p, hp_pos⟩ := h_irr.connected i j
  have h_le : 1 ≤ p.length := Nat.succ_le_of_lt hp_pos
  have ⟨v, p₁, p₂, _hp_eq, hp₁_len⟩ := p.exists_eq_comp_of_le_length (n := 1) h_le
  have hlen_ne : p₁.length ≠ 0 := by simp [hp₁_len]
  obtain ⟨c, p', e, rfl⟩ := (Quiver.Path.length_ne_zero_iff_eq_cons (p := p₁)).1 (by lia)
  obtain ⟨rfl⟩ : i = c := Quiver.Path.eq_of_length_zero p' (by simp_all)
  exact (no_out _).false e

/--
For a matrix `A` with nonnegative entries, the `(i, j)`-entry of the `k`-th power `A ^ k`
is strictly positive if and only if there exists a path of length `k` from `i` to `j` in the
quiver associated to `A` via `toQuiver`. -/
/-
**Matrix.pow_apply_pos_iff_nonempty_path** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：pow_apply_pos_iff_nonempty_path [Fintype n] [IsOrderedRing R] [PosMulStric
tMono R] [Nontrivial R] [DecidableEq n] (hA : forall i j, 0 <= A i j) (k : Nat) 
(i j : n) : letI
参数：hA : forall i j, 0 <= A i j；k : Nat；i j : n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Quiver.Path.eq_of_length_zero`：eq_of_length_zero (p : Path a b) (hzero :
 p.length = 0) : a = b
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Matrix.mul_apply`：mul_apply [Fintype m] [Mul α] [AddCommMonoid α] {M : M
atrix l m α} {N : Matrix m n α} {i k} : (M * N) i k = ∑ j, M i j * N j k
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.sum_pos_iff_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : Ad
dCommMonoid N] [inst_1 : PartialOrder N] {f : ι → N} {s : Finset ι}   [AddLeftMo
no N], (∀ x ∈ s, 0…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Matrix.pow_apply_nonneg`：pow_apply_nonneg [Fintype n] [DecidableEq n] [P
artialOrder α] [IsOrderedRing α] {A : Matrix n n α} (hA : forall i j, 0 <= A i j
) (k : Nat) :…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
For a matrix `A` with nonnegative entries, the `(i, j)`-entry of the `k`-th powe
r `A ^ k`
is strictly positive if and only if there exists a path of length `k` from `i` t
o `j` in the
quiver associated to `A` via `toQuiver`.
-/
theorem pow_apply_pos_iff_nonempty_path
    [Fintype n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) (i j : n) :
    letI := toQuiver A
    0 < (A ^ k) i j ↔ Nonempty {p : Path i j // p.length = k} := by
  let := toQuiver A
  induction k generalizing i j with
  | zero =>
    refine ⟨fun h_pos ↦ ?_, fun ⟨p, hp⟩ ↦ ?_⟩
    · rcases eq_or_ne i j with rfl | h_eq
      · exact ⟨⟨Quiver.Path.nil, rfl⟩⟩
      · simp_all
    · simp [Quiver.Path.eq_of_length_zero p hp]
  | succ m ih =>
    rw [pow_succ, mul_apply]
    constructor
    · intro h_pos
      obtain ⟨l, hl_mem, hl_pos⟩ :
          ∃ l ∈ (Finset.univ : Finset n), 0 < (A ^ m) i l * A l j := by
        simpa [Finset.sum_pos_iff_of_nonneg
                 (fun x _ => mul_nonneg (pow_apply_nonneg hA m i x) (hA x j))]
          using h_pos
      have hAm_nonneg : 0 ≤ (A ^ m) i l := pow_apply_nonneg hA m i l
      have hA_nonneg' : 0 ≤ A l j := hA l j
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

/-- Irreducibility of a nonnegative matrix `A` is equivalent to entrywise positivity of some
power: between any two indices `i, j` there exists a positive integer `k` such that the
`(i, j)`-entry of `A ^ k` is strictly positive. -/
/-
**Matrix.isIrreducible_iff_exists_pow_pos** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isIrreducible_iff_exists_pow_pos [Fintype n] [IsOrderedRing R] [PosMulStri
ctMono R] [Nontrivial R] [DecidableEq n] (hA : forall i j, 0 <= A i j) : IsIrred
ucible A ↔ forall i j, exists k > 0, 0 < (A ^ k) i j
参数：hA : forall i j, 0 <= A i j。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsIrreducible.connected`：∀ {n : Type u_1} {R : Type u_2} [inst : 
Ring R] [inst_1 : LinearOrder R] {A : Matrix n n R},   A.IsIrreducible → Quiver.
IsSStronglyConnected…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Matrix.pow_apply_pos_iff_nonempty_path`：pow_apply_pos_iff_nonempty_path 
[Fintype n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n
] (hA : forall i j, 0 <= A i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
Irreducibility of a nonnegative matrix `A` is equivalent to entrywise positivity
 of some
power: between any two indices `i, j` there exists a positive integer `k` such t
hat the
`(i, j)`-entry of `A ^ k` is strictly positive.
-/
theorem isIrreducible_iff_exists_pow_pos
    [Fintype n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (hA : ∀ i j, 0 ≤ A i j) :
    IsIrreducible A ↔ ∀ i j, ∃ k > 0, 0 < (A ^ k) i j := by
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

/-- If a nonnegative square matrix `A` is primitive, then `A` is irreducible. -/
/-
**Matrix.IsPrimitive.isIrreducible** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsPrimitive
`。
形式化陈述：∀ {n : Type u_1} {R : Type u_2} [inst : Ring R] [inst_1 : LinearOrder R] {
A : Matrix n n R} [inst_2 : Fintype n]   [IsOrderedRing R] [PosMulStrictMono R] 
[Nontrivial R] [inst_6 : DecidableEq n], A.IsPrimitive → A.IsIrreducible
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.isIrreducible_iff_exists_pow_pos`：isIrreducible_iff_exists_pow_po
s [Fintype n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq
 n] (hA : forall i j, 0 <= A …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
If a nonnegative square matrix `A` is primitive, then `A` is irreducible.
-/
theorem IsPrimitive.isIrreducible
    [Fintype n] [IsOrderedRing R] [PosMulStrictMono R] [Nontrivial R] [DecidableEq n]
    (h_prim : IsPrimitive A) : IsIrreducible A := by
  obtain ⟨h_nonneg, k, hk_pos, hk_all⟩ := h_prim
  rw [isIrreducible_iff_exists_pow_pos h_nonneg]
  aesop

/-! ## Transposition -/

/-- Reverse a path in `toQuiver A` to a path in `toQuiver Aᵀ`, swapping endpoints. -/
/-
**Matrix.transposePath** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：transposePath {i j : n} (p : @Quiver.Path n A.toQuiver i j) : @Quiver.Path
 n Aᵀ.toQuiver j i
参数：p : @Quiver.Path n A.toQuiver i j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reverse a path in `toQuiver A` to a path in `toQuiver Aᵀ`, swapping endpoints.
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
/-- Irreducibility is invariant under transpose. -/
/-
**Matrix.IsIrreducible.transpose** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.IsIrreducible
`。
形式化陈述：∀ {n : Type u_1} {R : Type u_2} [inst : Ring R] [inst_1 : LinearOrder R] {
A : Matrix n n R},   A.IsIrreducible → A.transpose.IsIrreducible
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsIrreducible.nonneg`：∀ {n : Type u_1} {R : Type u_2} [inst : Rin
g R] [inst_1 : LinearOrder R] {A : Matrix n n R},   A.IsIrreducible → ∀ (i j : n
), 0 ≤ A i j
· 使用定理 `Matrix.IsIrreducible.connected`：∀ {n : Type u_1} {R : Type u_2} [inst : 
Ring R] [inst_1 : LinearOrder R] {A : Matrix n n R},   A.IsIrreducible → Quiver.
IsSStronglyConnected…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.transposePath.eq_1`：∀ {n : Type u_1} {R : Type u_2} [inst : Ring 
R] [inst_1 : LinearOrder R] {A : Matrix n n R} {i j : n}   (p : Quiver.Path i j)
,   Matrix.tran…
· 使用定理 `Quiver.Path.length_comp`：∀ {V : Type u} [inst : Quiver V] {a b : V} (p :
 Quiver.Path a b) {c : V} (q : Quiver.Path b c),   (p.comp q).length = p.length 
+ q.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True

--- 原说明 ---
Irreducibility is invariant under transpose.
-/
theorem IsIrreducible.transpose (hA : IsIrreducible A) : IsIrreducible Aᵀ := by
  have hA_T_nonneg : ∀ i j, 0 ≤ Aᵀ i j := fun i j => by
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
/-
**Matrix.isIrreducible_transpose_iff** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：isIrreducible_transpose_iff : Aᵀ.IsIrreducible ↔ A.IsIrreducible
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.IsIrreducible.transpose`：∀ {n : Type u_1} {R : Type u_2} [inst : 
Ring R] [inst_1 : LinearOrder R] {A : Matrix n n R},   A.IsIrreducible → A.trans
pose.IsIrreducible
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.isIrreducible_iff`：∀ {n : Type u_1} {R : Type u_2} [inst : Ring R
] [inst_1 : LinearOrder R] (A : Matrix n n R),   A.IsIrreducible ↔ (∀ (i j : n),
 0 ≤ A i j) ∧ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isIrreducible_transpose_iff :
    Aᵀ.IsIrreducible ↔ A.IsIrreducible := by
  by_cases hA_nonneg : ∀ i j, 0 ≤ A i j
  · exact ⟨fun h ↦
    let hA_T_nonneg : ∀ i j, 0 ≤ (Aᵀ) i j := fun i j => by
      simpa [Matrix.transpose_apply] using hA_nonneg j i
    IsIrreducible.transpose h,
   fun h ↦ IsIrreducible.transpose h⟩
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

