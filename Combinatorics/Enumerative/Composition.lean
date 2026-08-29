/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Sort

/-!
# Compositions

A composition of a natural number `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum
of positive integers. Combinatorially, it corresponds to a decomposition of `{0, ..., n-1}` into
non-empty blocks of consecutive integers, where the `iⱼ` are the lengths of the blocks.
This notion is closely related to that of a partition of `n`, but in a composition of `n` the
order of the `iⱼ`s matters.

We implement two different structures covering these two viewpoints on compositions. The first
one, made of a list of positive integers summing to `n`, is the main one and is called
`Composition n`. The second one is useful for combinatorial arguments (for instance to show that
the number of compositions of `n` is `2^(n-1)`). It is given by a subset of `{0, ..., n}`
containing `0` and `n`, where the elements of the subset (other than `n`) correspond to the leftmost
points of each block. The main API is built on `Composition n`, and we provide an equivalence
between the two types.

## Main functions

* `c : Composition n` is a structure, made of a list of integers which are all positive and
  add up to `n`.
* `composition_card` states that the cardinality of `Composition n` is exactly
  `2^(n-1)`, which is proved by constructing an equiv with `CompositionAsSet n` (see below), which
  is itself in bijection with the subsets of `Fin (n-1)` (this holds even for `n = 0`, where `-` is
  nat subtraction).

Let `c : Composition n` be a composition of `n`. Then
* `c.blocks` is the list of blocks in `c`.
* `c.length` is the number of blocks in the composition.
* `c.blocksFun : Fin c.length → ℕ` is the realization of `c.blocks` as a function on
  `Fin c.length`. This is the main object when using compositions to understand the composition of
    analytic functions.
* `c.sizeUpTo : ℕ → ℕ` is the sum of the size of the blocks up to `i`.;
* `c.embedding i : Fin (c.blocksFun i) → Fin n` is the increasing embedding of the `i`-th block in
  `Fin n`;
* `c.index j`, for `j : Fin n`, is the index of the block containing `j`.

* `Composition.ones n` is the composition of `n` made of ones, i.e., `[1, ..., 1]`.
* `Composition.single n (hn : 0 < n)` is the composition of `n` made of a single block of size `n`.

Compositions can also be used to split lists. Let `l` be a list of length `n` and `c` a composition
of `n`.
* `l.splitWrtComposition c` is a list of lists, made of the slices of `l` corresponding to the
  blocks of `c`.
* `join_splitWrtComposition` states that splitting a list and then joining it gives back the
  original list.
* `splitWrtComposition_join` states that joining a list of lists, and then splitting it back
  according to the right composition, gives back the original list of lists.

We turn to the second viewpoint on compositions, that we realize as a finset of `Fin (n+1)`.
`c : CompositionAsSet n` is a structure made of a finset of `Fin (n+1)` called `c.boundaries`
and proofs that it contains `0` and `n`. (Taking a finset of `Fin n` containing `0` would not
make sense in the edge case `n = 0`, while the previous description works in all cases).
The elements of this set (other than `n`) correspond to leftmost points of blocks.
Thus, there is an equiv between `Composition n` and `CompositionAsSet n`. We
only construct basic API on `CompositionAsSet` (notably `c.length` and `c.blocks`) to be able
to construct this equiv, called `compositionEquiv n`. Since there is a straightforward equiv
between `CompositionAsSet n` and finsets of `{1, ..., n-1}` (obtained by removing `0` and `n`
from a `CompositionAsSet` and called `compositionAsSetEquiv n`), we deduce that
`CompositionAsSet n` and `Composition n` are both fintypes of cardinality `2^(n - 1)`
(see `compositionAsSet_card` and `composition_card`).

## Implementation details

The main motivation for this structure and its API is in the construction of the composition of
formal multilinear series, and the proof that the composition of analytic functions is analytic.

The representation of a composition as a list is very handy as lists are very flexible and already
have a well-developed API.

## Tags

Composition, partition

## References

<https://en.wikipedia.org/wiki/Composition_(combinatorics)>
-/

@[expose] public section

assert_not_exists Field

open List

variable {n : Nat}

/-- A composition of `n` is a list of positive integers summing to `n`. -/
@[ext]
/--
Definition of `Composition` / `Composition` 的定义

English:
structure Composition
  parameters: (n : Nat)
  axioms and operations (3):
    - blocks : List Nat
    - blocks_pos : forall {i}, i in blocks -> 0 < i
    - blocks_sum : blocks.sum = n

中文:
结构 余mposition
  参数: (n : 自然数)
  公理与运算 (3 个):
    - blocks : 列表 自然数
    - blocks_pos : 对任意 {i}, i in blocks -> 0 < i
    - blocks_sum : blocks.求和 = n
-/
structure Composition (n : Nat) where
  /-- List of positive integers summing to `n` -/
  blocks : List Nat
  /-- Proof of positivity for `blocks` -/
  blocks_pos : forall {i}, i in blocks -> 0 < i
  /-- Proof that `blocks` sums to `n` -/
  blocks_sum : blocks.sum = n
  deriving DecidableEq

attribute [simp] Composition.blocks_sum

/-- Combinatorial viewpoint on a composition of `n`, by seeing it as non-empty blocks of
consecutive integers in `{0, ..., n-1}`. We register every block by its left end-point, yielding
a finset containing `0`. As this does not make sense for `n = 0`, we add `n` to this finset, and
get a finset of `{0, ..., n}` containing `0` and `n`. This is the data in the structure
`CompositionAsSet n`. -/
@[ext]
/--
Definition of `CompositionAsSet` / `CompositionAsSet` 的定义

English:
structure CompositionAsSet
  parameters: (n : Nat)
  axioms and operations (3):
    - boundaries : Finset (Fin n.succ)
    - zero_mem : (0 : Fin n.succ) in boundaries
    - getLast_mem : Fin.last n in boundaries

中文:
结构 余mpositionAsSet
  参数: (n : 自然数)
  公理与运算 (3 个):
    - boundaries : 有限集 (有限集 n.succ)
    - zero_mem : (0 : 有限集 n.succ) in boundaries
    - getLast_mem : 有限集.last n in boundaries
-/
structure CompositionAsSet (n : Nat) where
  /-- Combinatorial viewpoint on a composition of `n` as consecutive integers `{0, ..., n-1}` -/
  boundaries : Finset (Fin n.succ)
  /-- Proof that `0` is a member of `boundaries` -/
  zero_mem : (0 : Fin n.succ) in boundaries
  /-- Last element of the composition -/
  getLast_mem : Fin.last n in boundaries
  deriving DecidableEq

instance {n : Nat} : Inhabited (CompositionAsSet n) :=
  ⟨⟨Finset.univ, Finset.mem_univ _, Finset.mem_univ _⟩⟩

attribute [simp] CompositionAsSet.zero_mem CompositionAsSet.getLast_mem

/-!
### Compositions

A composition of an integer `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum of
positive integers.
-/

namespace Composition

variable (c : Composition n)

instance (n : Nat) : ToString (Composition n) :=
  ⟨fun c => toString c.blocks⟩

/--
Definition of `length` / `length` 的定义

English:
abbreviation length
  signature: : Nat
  body: c.blocks.length

中文:
缩写 length
  签名: : 自然数
  定义体: c.blocks.length

Depends on / 依赖: blocks, c.blocks.length, length
-/
abbrev length : Nat :=
  c.blocks.length

/--
theorem `blocks_length` / 定理 `blocks_length`

English:
theorem blocks_length
  statement: c.blocks.length = c.length
  proof: rfl

中文:
定理 blocks_length
  结论: c.blocks.length = c.length
  证明: rfl
-/
theorem blocks_length : c.blocks.length = c.length :=
  rfl

/--
Definition of `blocksFun` / `blocksFun` 的定义

English:
definition blocksFun
  signature: : Fin c.length -> Nat
  body: c.blocks.get

@[simp]

中文:
定义 blocksFun
  签名: : 有限集 c.length -> 自然数
  定义体: c.blocks.get

@[simp]

Depends on / 依赖: blocks, c.blocks.get
-/
def blocksFun : Fin c.length -> Nat := c.blocks.get

@[simp]
/--
theorem `ofFn_blocksFun` / 定理 `ofFn_blocksFun`

English:
theorem ofFn_blocksFun
  statement: ofFn c.blocksFun = c.blocks
  proof: ofFn_get _

@[simp]

中文:
定理 ofFn_blocksFun
  结论: ofFn c.blocksFun = c.blocks
  证明: ofFn_get _

@[simp]

Depends on / 依赖: ofFn_get
-/
theorem ofFn_blocksFun : ofFn c.blocksFun = c.blocks :=
  ofFn_get _

@[simp]
/--
theorem `sum_blocksFun` / 定理 `sum_blocksFun`

English:
theorem sum_blocksFun
  statement: ∑ i, c.blocksFun i = n
  proof: by
  conv_rhs => rw [← c.blocks_sum, ← ofFn_blocksFun, sum_ofFn]

@[simp]

中文:
定理 sum_blocksFun
  结论: ∑ i, c.blocksFun i = n
  证明: by
  conv_rhs => rw [← c.blocks_sum, ← ofFn_blocksFun, sum_ofFn]

@[simp]

Depends on / 依赖: blocks_sum, c.blocks_sum, conv_rhs, ofFn_blocksFun, sum_ofFn
-/
theorem sum_blocksFun : ∑ i, c.blocksFun i = n := by
  conv_rhs => rw [← c.blocks_sum, ← ofFn_blocksFun, sum_ofFn]

@[simp]
/--
theorem `blocksFun_mem_blocks` / 定理 `blocksFun_mem_blocks`

English:
theorem blocksFun_mem_blocks
  given: (i : Fin c.length)
  statement: c.blocksFun i in c.blocks
  proof: get_mem _ _

中文:
定理 blocksFun_mem_blocks
  条件: (i : 有限集 c.length)
  结论: c.blocksFun i in c.blocks
  证明: get_mem _ _

Depends on / 依赖: X.obj, X.property, get_mem, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition, property
-/
theorem blocksFun_mem_blocks (i : Fin c.length) : c.blocksFun i in c.blocks :=
  get_mem _ _

/--
theorem `one_le_blocks` / 定理 `one_le_blocks`

English:
theorem one_le_blocks
  given: {i : Nat} (h : i in c.blocks)
  statement: 1 <= i
  proof: c.blocks_pos h

中文:
定理 one_le_blocks
  条件: {i : 自然数} (h : i in c.blocks)
  结论: 1 <= i
  证明: c.blocks_pos h

Depends on / 依赖: X.obj, X.property, blocks_pos, c.blocks_pos, isSheaf_iff_preservesFiniteProducts_and_equalizerCondition, property
-/
theorem one_le_blocks {i : Nat} (h : i in c.blocks) : 1 <= i :=
  c.blocks_pos h

/--
theorem `blocks_le` / 定理 `blocks_le`

English:
theorem blocks_le
  given: {i : Nat} (h : i in c.blocks)
  statement: i <= n
  proof: by
  rw [← c.blocks_sum]
  exact List.le_sum_of_mem h

@[simp]

中文:
定理 blocks_le
  条件: {i : 自然数} (h : i in c.blocks)
  结论: i <= n
  证明: by
  rw [← c.blocks_sum]
  exact List.le_sum_of_mem h

@[simp]

Depends on / 依赖: List.le_sum_of_mem, blocks_sum, c.blocks_sum, le_sum_of_mem
-/
theorem blocks_le {i : Nat} (h : i in c.blocks) : i <= n := by
  rw [← c.blocks_sum]
  exact List.le_sum_of_mem h

@[simp]
/--
theorem `one_le_blocks'` / 定理 `one_le_blocks'`

English:
theorem one_le_blocks'
  given: {i : Nat} (h : i < c.length)
  statement: 1 <= c.blocks[i]
  proof: c.one_le_blocks (get_mem (blocks c) _)

@[simp]

中文:
定理 one_le_blocks'
  条件: {i : 自然数} (h : i < c.length)
  结论: 1 <= c.blocks[i]
  证明: c.one_le_blocks (get_mem (blocks c) _)

@[simp]

Depends on / 依赖: X.obj, X.property, blocks, c.one_le_blocks, get_mem, isSheaf_iff_preservesFiniteProducts_of_projective, one_le_blocks, property
-/
theorem one_le_blocks' {i : Nat} (h : i < c.length) : 1 <= c.blocks[i] :=
  c.one_le_blocks (get_mem (blocks c) _)

@[simp]
/--
theorem `blocks_pos'` / 定理 `blocks_pos'`

English:
theorem blocks_pos'
  given: (i : Nat) (h : i < c.length)
  statement: 0 < c.blocks[i]
  proof: c.one_le_blocks' h

@[simp]

中文:
定理 blocks_pos'
  条件: (i : 自然数) (h : i < c.length)
  结论: 0 < c.blocks[i]
  证明: c.one_le_blocks' h

@[simp]

Depends on / 依赖: c.one_le_blocks, one_le_blocks
-/
theorem blocks_pos' (i : Nat) (h : i < c.length) : 0 < c.blocks[i] :=
  c.one_le_blocks' h

@[simp]
/--
theorem `one_le_blocksFun` / 定理 `one_le_blocksFun`

English:
theorem one_le_blocksFun
  given: (i : Fin c.length)
  statement: 1 <= c.blocksFun i
  proof: c.one_le_blocks (c.blocksFun_mem_blocks i)

@[simp]

中文:
定理 one_le_blocksFun
  条件: (i : 有限集 c.length)
  结论: 1 <= c.blocksFun i
  证明: c.one_le_blocks (c.blocksFun_mem_blocks i)

@[simp]

Depends on / 依赖: blocksFun_mem_blocks, c.blocksFun_mem_blocks, c.one_le_blocks, one_le_blocks
-/
theorem one_le_blocksFun (i : Fin c.length) : 1 <= c.blocksFun i :=
  c.one_le_blocks (c.blocksFun_mem_blocks i)

@[simp]
/--
theorem `blocksFun_le` / 定理 `blocksFun_le`

English:
theorem blocksFun_le
  given: {n} (c : Composition n) (i : Fin c.length)
  proof: c.blocks_le getElem_mem _

@[simp]

中文:
定理 blocksFun_le
  条件: {n} (c : 余mposition n) (i : 有限集 c.length)
  证明: c.blocks_le getElem_mem _

@[simp]

Depends on / 依赖: blocks_le, c.blocks_le, getElem_mem
-/
theorem blocksFun_le {n} (c : Composition n) (i : Fin c.length) :
    c.blocksFun i <= n :=
c.blocks_le getElem_mem _

@[simp]
/--
theorem `length_le` / 定理 `length_le`

English:
theorem length_le
  statement: c.length <= n
  proof: by
  conv_rhs => rw [← c.blocks_sum]
  exact length_le_sum_of_one_le _ fun i hi => c.one_le_blocks hi

@[simp]

中文:
定理 length_le
  结论: c.length <= n
  证明: by
  conv_rhs => rw [← c.blocks_sum]
  exact length_le_sum_of_one_le _ fun i hi => c.one_le_blocks hi

@[simp]

Depends on / 依赖: blocks_sum, c.blocks_sum, c.one_le_blocks, conv_rhs, length_le_sum_of_one_le, one_le_blocks
-/
theorem length_le : c.length <= n := by
  conv_rhs => rw [← c.blocks_sum]
  exact length_le_sum_of_one_le _ fun i hi => c.one_le_blocks hi

@[simp]
/--
theorem `blocks_eq_nil` / 定理 `blocks_eq_nil`

English:
theorem blocks_eq_nil
  statement: c.blocks = [] ↔ n = 0
  proof: by
  constructor
  · intro h
    simpa using congr(List.sum $h)
  · rintro rfl
    rw [← length_eq_zero_iff]; rw [← nonpos_iff_eq_zero]
    exact c.length_le

中文:
定理 blocks_eq_nil
  结论: c.blocks = [] ↔ n = 0
  证明: by
  constructor
  · intro h
    simpa using congr(List.sum $h)
  · rintro rfl
    rw [← length_eq_zero_iff]; rw [← nonpos_iff_eq_zero]
    exact c.length_le

Depends on / 依赖: List.sum, c.length_le, length_eq_zero_iff, length_le, nonpos_iff_eq_zero
-/
theorem blocks_eq_nil : c.blocks = [] ↔ n = 0 := by
  constructor
  · intro h
    simpa using congr(List.sum $h)
  · rintro rfl
    rw [← length_eq_zero_iff]; rw [← nonpos_iff_eq_zero]
    exact c.length_le

/--
theorem `length_eq_zero` / 定理 `length_eq_zero`

English:
theorem length_eq_zero
  statement: c.length = 0 ↔ n = 0
  proof: by
  simp

@[simp]

中文:
定理 length_eq_zero
  结论: c.length = 0 ↔ n = 0
  证明: by
  simp

@[simp]
-/
protected theorem length_eq_zero : c.length = 0 ↔ n = 0 := by
  simp

@[simp]
/--
theorem `length_pos_iff` / 定理 `length_pos_iff`

English:
theorem length_pos_iff
  statement: 0 < c.length ↔ 0 < n
  proof: by
  simp [pos_iff_ne_zero]

alias ⟨_, length_pos_of_pos⟩ := length_pos_iff

中文:
定理 length_pos_iff
  结论: 0 < c.length ↔ 0 < n
  证明: by
  simp [pos_iff_ne_zero]

alias ⟨_, length_pos_of_pos⟩ := length_pos_iff

Depends on / 依赖: pos_iff_ne_zero
-/
theorem length_pos_iff : 0 < c.length ↔ 0 < n := by
  simp [pos_iff_ne_zero]

alias ⟨_, length_pos_of_pos⟩ := length_pos_iff

/--
Definition of `sizeUpTo` / `sizeUpTo` 的定义

English:
definition sizeUpTo
  signature: (i : Nat)
  body: (c.blocks.take i).sum

@[simp]

中文:
定义 sizeUpTo
  签名: (i : 自然数)
  定义体: (c.blocks.take i).sum

@[simp]

Depends on / 依赖: blocks, c.blocks.take
-/
def sizeUpTo (i : Nat) : Nat :=
  (c.blocks.take i).sum

@[simp]
/--
theorem `sizeUpTo_zero` / 定理 `sizeUpTo_zero`

English:
theorem sizeUpTo_zero
  statement: c.sizeUpTo 0 = 0
  proof: by simp [sizeUpTo]

中文:
定理 sizeUpTo_zero
  结论: c.sizeUpTo 0 = 0
  证明: by simp [sizeUpTo]

Depends on / 依赖: sizeUpTo
-/
theorem sizeUpTo_zero : c.sizeUpTo 0 = 0 := by simp [sizeUpTo]

/--
theorem `sizeUpTo_ofLength_le` / 定理 `sizeUpTo_ofLength_le`

English:
theorem sizeUpTo_ofLength_le
  given: (i : Nat) (h : c.length <= i)
  statement: c.sizeUpTo i = n
  proof: by
  dsimp [sizeUpTo]
  convert! c.blocks_sum
  exact take_of_length_le h

@[simp]

中文:
定理 sizeUpTo_ofLength_le
  条件: (i : 自然数) (h : c.length <= i)
  结论: c.sizeUpTo i = n
  证明: by
  dsimp [sizeUpTo]
  convert! c.blocks_sum
  exact take_of_length_le h

@[simp]

Depends on / 依赖: blocks_sum, c.blocks_sum, convert, sizeUpTo, take_of_length_le
-/
theorem sizeUpTo_ofLength_le (i : Nat) (h : c.length <= i) : c.sizeUpTo i = n := by
  dsimp [sizeUpTo]
  convert! c.blocks_sum
  exact take_of_length_le h

@[simp]
/--
theorem `sizeUpTo_length` / 定理 `sizeUpTo_length`

English:
theorem sizeUpTo_length
  statement: c.sizeUpTo c.length = n
  proof: c.sizeUpTo_ofLength_le c.length le_rfl

中文:
定理 sizeUpTo_length
  结论: c.sizeUpTo c.length = n
  证明: c.sizeUpTo_ofLength_le c.length le_rfl

Depends on / 依赖: c.length, c.sizeUpTo_ofLength_le, le_rfl, length, sizeUpTo_ofLength_le
-/
theorem sizeUpTo_length : c.sizeUpTo c.length = n :=
  c.sizeUpTo_ofLength_le c.length le_rfl

/--
theorem `sizeUpTo_le` / 定理 `sizeUpTo_le`

English:
theorem sizeUpTo_le
  given: (i : Nat)
  statement: c.sizeUpTo i <= n
  proof: by
  conv_rhs => rw [← c.blocks_sum, ← sum_take_add_sum_drop _ i]
  exact Nat.le_add_right _ _

中文:
定理 sizeUpTo_le
  条件: (i : 自然数)
  结论: c.sizeUpTo i <= n
  证明: by
  conv_rhs => rw [← c.blocks_sum, ← sum_take_add_sum_drop _ i]
  exact Nat.le_add_right _ _

Depends on / 依赖: Nat.le_add_right, blocks_sum, c.blocks_sum, conv_rhs, le_add_right, sum_take_add_sum_drop
-/
theorem sizeUpTo_le (i : Nat) : c.sizeUpTo i <= n := by
  conv_rhs => rw [← c.blocks_sum, ← sum_take_add_sum_drop _ i]
  exact Nat.le_add_right _ _

/--
theorem `sizeUpTo_succ` / 定理 `sizeUpTo_succ`

English:
theorem sizeUpTo_succ
  given: {i : Nat} (h : i < c.length)
  proof: by
  simp only [sizeUpTo]
  rw [sum_take_succ _ _ h]

中文:
定理 sizeUpTo_succ
  条件: {i : 自然数} (h : i < c.length)
  证明: by
  simp only [sizeUpTo]
  rw [sum_take_succ _ _ h]

Depends on / 依赖: sizeUpTo, sum_take_succ
-/
theorem sizeUpTo_succ {i : Nat} (h : i < c.length) :
    c.sizeUpTo (i + 1) = c.sizeUpTo i + c.blocks[i] := by
  simp only [sizeUpTo]
  rw [sum_take_succ _ _ h]

/--
theorem `sizeUpTo_succ'` / 定理 `sizeUpTo_succ'`

English:
theorem sizeUpTo_succ'
  given: (i : Fin c.length)
  proof: c.sizeUpTo_succ i.2

中文:
定理 sizeUpTo_succ'
  条件: (i : 有限集 c.length)
  证明: c.sizeUpTo_succ i.2

Depends on / 依赖: c.sizeUpTo_succ, sizeUpTo_succ
-/
theorem sizeUpTo_succ' (i : Fin c.length) :
    c.sizeUpTo ((i : Nat) + 1) = c.sizeUpTo i + c.blocksFun i :=
  c.sizeUpTo_succ i.2

/--
theorem `sizeUpTo_strict_mono` / 定理 `sizeUpTo_strict_mono`

English:
theorem sizeUpTo_strict_mono
  given: {i : Nat} (h : i < c.length)
  statement: c.sizeUpTo i < c.sizeUpTo (i + 1)
  proof: by
  rw [c.sizeUpTo_succ h]
  simp

中文:
定理 sizeUpTo_strict_mono
  条件: {i : 自然数} (h : i < c.length)
  结论: c.sizeUpTo i < c.sizeUpTo (i + 1)
  证明: by
  rw [c.sizeUpTo_succ h]
  simp

Depends on / 依赖: c.sizeUpTo_succ, sizeUpTo_succ
-/
theorem sizeUpTo_strict_mono {i : Nat} (h : i < c.length) : c.sizeUpTo i < c.sizeUpTo (i + 1) := by
  rw [c.sizeUpTo_succ h]
  simp

/--
theorem `monotone_sizeUpTo` / 定理 `monotone_sizeUpTo`

English:
theorem monotone_sizeUpTo
  statement: Monotone c.sizeUpTo
  proof: monotone_sum_take _

中文:
定理 monotone_sizeUpTo
  结论: 递增 c.sizeUpTo
  证明: monotone_sum_take _

Depends on / 依赖: monotone_sum_take
-/
theorem monotone_sizeUpTo : Monotone c.sizeUpTo :=
  monotone_sum_take _

/--
Definition of `boundary` / `boundary` 的定义

English:
definition boundary
  signature: : Fin (c.length + 1) ↪o Fin (n + 1)
  body: (OrderEmbedding.ofStrictMono fun i => ⟨c.sizeUpTo i, Nat.lt_succ_of_le (c.sizeUpTo_le i)⟩)
    Fin.strictMono_iff_lt_succ.2 fun ⟨_, hi⟩ => c.sizeUpTo_strict_mono hi

@[simp]

中文:
定义 boundary
  签名: : 有限集 (c.length + 1) ↪o 有限集 (n + 1)
  定义体: (OrderEmbedding.ofStrictMono fun i => ⟨c.sizeUpTo i, Nat.lt_succ_of_le (c.sizeUpTo_le i)⟩)
    Fin.strictMono_iff_lt_succ.2 fun ⟨_, hi⟩ => c.sizeUpTo_strict_mono hi

@[simp]

Depends on / 依赖: Fin.strictMono_iff_lt_succ, Nat.lt_succ_of_le, OrderEmbedding, OrderEmbedding.ofStrictMono, c.sizeUpTo, c.sizeUpTo_le, c.sizeUpTo_strict_mono, lt_succ_of_le, ofStrictMono, sizeUpTo, sizeUpTo_le, sizeUpTo_strict_mono, strictMono_iff_lt_succ
-/
def boundary : Fin (c.length + 1) ↪o Fin (n + 1) :=
(OrderEmbedding.ofStrictMono fun i => ⟨c.sizeUpTo i, Nat.lt_succ_of_le (c.sizeUpTo_le i)⟩)
    Fin.strictMono_iff_lt_succ.2 fun ⟨_, hi⟩ => c.sizeUpTo_strict_mono hi

@[simp]
/--
theorem `boundary_zero` / 定理 `boundary_zero`

English:
theorem boundary_zero
  statement: c.boundary 0 = 0
  proof: by simp [boundary]

@[simp]

中文:
定理 boundary_zero
  结论: c.boundary 0 = 0
  证明: by simp [boundary]

@[simp]

Depends on / 依赖: boundary
-/
theorem boundary_zero : c.boundary 0 = 0 := by simp [boundary]

@[simp]
/--
theorem `boundary_last` / 定理 `boundary_last`

English:
theorem boundary_last
  statement: c.boundary (Fin.last c.length) = Fin.last n
  proof: by
  simp [boundary, Fin.ext_iff]

中文:
定理 boundary_last
  结论: c.boundary (有限集.last c.length) = 有限集.last n
  证明: by
  simp [boundary, Fin.ext_iff]

Depends on / 依赖: Fin.ext_iff, boundary, ext_iff
-/
theorem boundary_last : c.boundary (Fin.last c.length) = Fin.last n := by
  simp [boundary, Fin.ext_iff]

/--
Definition of `boundaries` / `boundaries` 的定义

English:
definition boundaries
  signature: : Finset (Fin (n + 1))
  body: Finset.univ.map c.boundary.toEmbedding

中文:
定义 boundaries
  签名: : 有限集 (有限集 (n + 1))
  定义体: Finset.univ.map c.boundary.toEmbedding

Depends on / 依赖: Finset, Finset.univ.map, boundary, c.boundary.toEmbedding, toEmbedding
-/
def boundaries : Finset (Fin (n + 1)) :=
  Finset.univ.map c.boundary.toEmbedding

/--
theorem `card_boundaries_eq_succ_length` / 定理 `card_boundaries_eq_succ_length`

English:
theorem card_boundaries_eq_succ_length
  statement: c.boundaries.card = c.length + 1
  proof: by simp [boundaries]

中文:
定理 card_boundaries_eq_succ_length
  结论: c.boundaries.card = c.length + 1
  证明: by simp [boundaries]

Depends on / 依赖: boundaries
-/
theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 := by simp [boundaries]

/--
Definition of `toCompositionAsSet` / `toCompositionAsSet` 的定义

English:
definition toCompositionAsSet
  signature: : CompositionAsSet n where
  body: c.boundaries
  zero_mem := by
    simp only [boundaries, Finset.mem_univ, Finset.mem_map]
    exact ⟨0, And.intro True.intro rfl⟩
  getLast_mem := by
    simp only [boundaries, Finset.mem_univ, Finset.mem_map]
    exact ⟨Fin.last c.length, And.intro True.intro c.boundary_last⟩

中文:
定义 toCompositionAsSet
  签名: : 余mpositionAsSet n where
  定义体: c.boundaries
  zero_mem := by
    simp only [boundaries, Finset.mem_univ, Finset.mem_map]
    exact ⟨0, And.intro True.intro rfl⟩
  getLast_mem := by
    simp only [boundaries, Finset.mem_univ, Finset.mem_map]
    exact ⟨Fin.last c.length, And.intro True.intro c.boundary_last⟩

Depends on / 依赖: boundaries, c.boundaries
-/
def toCompositionAsSet : CompositionAsSet n where
  boundaries := c.boundaries
  zero_mem := by
    simp only [boundaries, Finset.mem_univ, Finset.mem_map]
    exact ⟨0, And.intro True.intro rfl⟩
  getLast_mem := by
    simp only [boundaries, Finset.mem_univ, Finset.mem_map]
    exact ⟨Fin.last c.length, And.intro True.intro c.boundary_last⟩

/--
theorem `orderEmbOfFin_boundaries` / 定理 `orderEmbOfFin_boundaries`

English:
theorem orderEmbOfFin_boundaries
  proof: by
  refine (Finset.orderEmbOfFin_unique' _ ?_).symm
  exact fun i => (Finset.mem_map' _).2 (Finset.mem_univ _)

中文:
定理 orderEmbOfFin_boundaries
  证明: by
  refine (Finset.orderEmbOfFin_unique' _ ?_).symm
  exact fun i => (Finset.mem_map' _).2 (Finset.mem_univ _)

Depends on / 依赖: Finset, Finset.mem_map, Finset.mem_univ, Finset.orderEmbOfFin_unique, mem_map, mem_univ, orderEmbOfFin_unique
-/
theorem orderEmbOfFin_boundaries :
    c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length = c.boundary := by
  refine (Finset.orderEmbOfFin_unique' _ ?_).symm
  exact fun i => (Finset.mem_map' _).2 (Finset.mem_univ _)

/--
Definition of `embedding` / `embedding` 的定义

English:
definition embedding
  signature: (i : Fin c.length)
  body: (Fin.natAddOrderEmb <| c.sizeUpTo i).trans Fin.castLEOrderEmb
    calc
      c.sizeUpTo i + c.blocksFun i = c.sizeUpTo (i + 1) := (c.sizeUpTo_succ i.2).symm
      _ <= c.sizeUpTo c.length := monotone_sum_take _ i.2
      _ = n := c.sizeUpTo_length

@[simp]

中文:
定义 embedding
  签名: (i : 有限集 c.length)
  定义体: (Fin.natAddOrderEmb <| c.sizeUpTo i).trans Fin.castLEOrderEmb
    calc
      c.sizeUpTo i + c.blocksFun i = c.sizeUpTo (i + 1) := (c.sizeUpTo_succ i.2).symm
      _ <= c.sizeUpTo c.length := monotone_sum_take _ i.2
      _ = n := c.sizeUpTo_length

@[simp]

Depends on / 依赖: Fin.castLEOrderEmb, Fin.natAddOrderEmb, blocksFun, c.blocksFun, c.length, c.sizeUpTo, c.sizeUpTo_length, c.sizeUpTo_succ, castLEOrderEmb, length, monotone_sum_take, natAddOrderEmb, sizeUpTo, sizeUpTo_length, sizeUpTo_succ
-/
def embedding (i : Fin c.length) : Fin (c.blocksFun i) ↪o Fin n :=
(Fin.natAddOrderEmb <| c.sizeUpTo i).trans Fin.castLEOrderEmb
    calc
      c.sizeUpTo i + c.blocksFun i = c.sizeUpTo (i + 1) := (c.sizeUpTo_succ i.2).symm
      _ <= c.sizeUpTo c.length := monotone_sum_take _ i.2
      _ = n := c.sizeUpTo_length

@[simp]
/--
theorem `coe_embedding` / 定理 `coe_embedding`

English:
theorem coe_embedding
  given: (i : Fin c.length) (j : Fin (c.blocksFun i))
  proof: rfl

中文:
定理 coe_embedding
  条件: (i : 有限集 c.length) (j : 有限集 (c.blocksFun i))
  证明: rfl
-/
theorem coe_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    (c.embedding i j : Nat) = c.sizeUpTo i + j :=
  rfl

/--
theorem `index_exists` / 定理 `index_exists`

English:
theorem index_exists
  given: {j : Nat} (h : j < n)
  statement: exists i : Nat, j < c.sizeUpTo (i + 1) ∧ i < c.length
  proof: by
  have length_pos := length_pos_of_sum_pos (blocks c) (h.pos.trans_eq c.blocks_sum.symm)
  refine ⟨_, ?_, Nat.pred_lt length_pos.ne'⟩
  have : c.length - 1 + 1 = c.length := Nat.succ_pred_eq_of_pos length_pos
  simp [this, h]

中文:
定理 index_存在
  条件: {j : 自然数} (h : j < n)
  结论: 存在 i : 自然数, j < c.sizeUpTo (i + 1) ∧ i < c.length
  证明: by
  have length_pos := length_pos_of_sum_pos (blocks c) (h.pos.trans_eq c.blocks_sum.symm)
  refine ⟨_, ?_, Nat.pred_lt length_pos.ne'⟩
  have : c.length - 1 + 1 = c.length := Nat.succ_pred_eq_of_pos length_pos
  simp [this, h]

Depends on / 依赖: Nat.pred_lt, Nat.succ_pred_eq_of_pos, blocks, blocks_sum, c.blocks_sum.symm, c.length, h.pos.trans_eq, length, length_pos, length_pos.ne, length_pos_of_sum_pos, pred_lt, succ_pred_eq_of_pos, trans_eq
-/
theorem index_exists {j : Nat} (h : j < n) : exists i : Nat, j < c.sizeUpTo (i + 1) ∧ i < c.length := by
  have length_pos := length_pos_of_sum_pos (blocks c) (h.pos.trans_eq c.blocks_sum.symm)
  refine ⟨_, ?_, Nat.pred_lt length_pos.ne'⟩
  have : c.length - 1 + 1 = c.length := Nat.succ_pred_eq_of_pos length_pos
  simp [this, h]

/--
Definition of `index` / `index` 的定义

English:
definition index
  signature: (j : Fin n)
  body: ⟨Nat.find (c.index_exists j.2), (Nat.find_spec (c.index_exists j.2)).2⟩

中文:
定义 index
  签名: (j : 有限集 n)
  定义体: ⟨Nat.find (c.index_exists j.2), (Nat.find_spec (c.index_exists j.2)).2⟩

Depends on / 依赖: HasColimitsOfShape, Nat.find, Nat.find_spec, c.index_exists, find_spec, index_exists
-/
def index (j : Fin n) : Fin c.length :=
  ⟨Nat.find (c.index_exists j.2), (Nat.find_spec (c.index_exists j.2)).2⟩

/--
theorem `lt_sizeUpTo_index_succ` / 定理 `lt_sizeUpTo_index_succ`

English:
theorem lt_sizeUpTo_index_succ
  given: (j : Fin n)
  statement: (j : Nat) < c.sizeUpTo (c.index j).succ
  proof: (Nat.find_spec (c.index_exists j.2)).1

中文:
定理 lt_sizeUpTo_index_succ
  条件: (j : 有限集 n)
  结论: (j : 自然数) < c.sizeUpTo (c.index j).succ
  证明: (Nat.find_spec (c.index_exists j.2)).1

Depends on / 依赖: HasLimitsOfShape, Nat.find_spec, c.index_exists, find_spec, index_exists
-/
theorem lt_sizeUpTo_index_succ (j : Fin n) : (j : Nat) < c.sizeUpTo (c.index j).succ :=
  (Nat.find_spec (c.index_exists j.2)).1

/--
theorem `sizeUpTo_index_le` / 定理 `sizeUpTo_index_le`

English:
theorem sizeUpTo_index_le
  given: (j : Fin n)
  statement: c.sizeUpTo (c.index j) <= j
  proof: by
  by_contra! H
  set i := c.index j
  have i_pos : (0 : Nat) < i := by
    by_contra! i_pos
    revert H
    simp [nonpos_iff_eq_zero.1 i_pos, c.sizeUpTo_zero]
  let i₁ := (i : Nat).pred
  have i₁_lt_i : i₁ < i := Nat.pred_lt (ne_of_gt i_pos)
  have i₁_succ : i₁ + 1 = i := Nat.succ_pred_eq_of_pos i_pos
  have := Nat.find_min (c.index_exists j.2) i₁_lt_i
  simp_all [lt_trans i₁_lt_i (c.index j).2]

中文:
定理 sizeUpTo_index_le
  条件: (j : 有限集 n)
  结论: c.sizeUpTo (c.index j) <= j
  证明: by
  by_contra! H
  set i := c.index j
  have i_pos : (0 : Nat) < i := by
    by_contra! i_pos
    revert H
    simp [nonpos_iff_eq_zero.1 i_pos, c.sizeUpTo_zero]
  let i₁ := (i : Nat).pred
  have i₁_lt_i : i₁ < i := Nat.pred_lt (ne_of_gt i_pos)
  have i₁_succ : i₁ + 1 = i := Nat.succ_pred_eq_of_pos i_pos
  have := Nat.find_min (c.index_exists j.2) i₁_lt_i
  simp_all [lt_trans i₁_lt_i (c.index j).2]

Depends on / 依赖: HasFiniteLimits, Nat.find_min, Nat.pred_lt, Nat.succ_pred_eq_of_pos, c.index, c.index_exists, c.sizeUpTo_zero, find_min, i_pos, index_exists, lt_trans, ne_of_gt, nonpos_iff_eq_zero, pred_lt, revert, sizeUpTo_zero, succ_pred_eq_of_pos
-/
theorem sizeUpTo_index_le (j : Fin n) : c.sizeUpTo (c.index j) <= j := by
  by_contra! H
  set i := c.index j
  have i_pos : (0 : Nat) < i := by
    by_contra! i_pos
    revert H
    simp [nonpos_iff_eq_zero.1 i_pos, c.sizeUpTo_zero]
  let i₁ := (i : Nat).pred
  have i₁_lt_i : i₁ < i := Nat.pred_lt (ne_of_gt i_pos)
  have i₁_succ : i₁ + 1 = i := Nat.succ_pred_eq_of_pos i_pos
  have := Nat.find_min (c.index_exists j.2) i₁_lt_i
  simp_all [lt_trans i₁_lt_i (c.index j).2]

/--
Definition of `invEmbedding` / `invEmbedding` 的定义

English:
definition invEmbedding
  signature: (j : Fin n)
  body: ⟨j - c.sizeUpTo (c.index j), by
    rw [tsub_lt_iff_right]; rw [add_comm]; rw [← sizeUpTo_succ']
    · exact lt_sizeUpTo_index_succ _ _
    · exact sizeUpTo_index_le _ _⟩

@[simp]

中文:
定义 invEmbedding
  签名: (j : 有限集 n)
  定义体: ⟨j - c.sizeUpTo (c.index j), by
    rw [tsub_lt_iff_right]; rw [add_comm]; rw [← sizeUpTo_succ']
    · exact lt_sizeUpTo_index_succ _ _
    · exact sizeUpTo_index_le _ _⟩

@[simp]

Depends on / 依赖: HasFiniteColimits, add_comm, c.index, c.sizeUpTo, lt_sizeUpTo_index_succ, sizeUpTo, sizeUpTo_index_le, sizeUpTo_succ, tsub_lt_iff_right
-/
def invEmbedding (j : Fin n) : Fin (c.blocksFun (c.index j)) :=
  ⟨j - c.sizeUpTo (c.index j), by
    rw [tsub_lt_iff_right]; rw [add_comm]; rw [← sizeUpTo_succ']
    · exact lt_sizeUpTo_index_succ _ _
    · exact sizeUpTo_index_le _ _⟩

@[simp]
/--
theorem `coe_invEmbedding` / 定理 `coe_invEmbedding`

English:
theorem coe_invEmbedding
  given: (j : Fin n)
  statement: (c.invEmbedding j : Nat) = j - c.sizeUpTo (c.index j)
  proof: rfl

@[simp]

中文:
定理 coe_invEmbedding
  条件: (j : 有限集 n)
  结论: (c.invEmbedding j : 自然数) = j - c.sizeUpTo (c.index j)
  证明: rfl

@[simp]
-/
theorem coe_invEmbedding (j : Fin n) : (c.invEmbedding j : Nat) = j - c.sizeUpTo (c.index j) :=
  rfl

@[simp]
/--
theorem `embedding_comp_inv` / 定理 `embedding_comp_inv`

English:
theorem embedding_comp_inv
  given: (j : Fin n)
  statement: c.embedding (c.index j) (c.invEmbedding j) = j
  proof: by
  rw [Fin.ext_iff]
  apply add_tsub_cancel_of_le (c.sizeUpTo_index_le j)

中文:
定理 embedding_comp_inv
  条件: (j : 有限集 n)
  结论: c.embedding (c.index j) (c.invEmbedding j) = j
  证明: by
  rw [Fin.ext_iff]
  apply add_tsub_cancel_of_le (c.sizeUpTo_index_le j)

Depends on / 依赖: Fin.ext_iff, add_tsub_cancel_of_le, c.sizeUpTo_index_le, ext_iff, sizeUpTo_index_le
-/
theorem embedding_comp_inv (j : Fin n) : c.embedding (c.index j) (c.invEmbedding j) = j := by
  rw [Fin.ext_iff]
  apply add_tsub_cancel_of_le (c.sizeUpTo_index_le j)

/--
theorem `mem_range_embedding_iff` / 定理 `mem_range_embedding_iff`

English:
theorem mem_range_embedding_iff
  given: {j : Fin n} {i : Fin c.length}
  proof: by
  constructor
  · intro h
    rcases Set.mem_range.2 h with ⟨k, hk⟩
    rw [Fin.ext_iff] at hk
    dsimp at hk
    rw [← hk]
    simp [sizeUpTo_succ', k.is_lt]
  · intro h
    apply Set.mem_range.2
    refine ⟨⟨j - c.sizeUpTo i, ?_⟩, ?_⟩
    · rw [tsub_lt_iff_left, ← sizeUpTo_succ']
      · exact h.2
      · exact h.1
    · rw [Fin.ext_iff]
      exact add_tsub_cancel_of_le h.1

中文:
定理 mem_range_embedding_iff
  条件: {j : 有限集 n} {i : 有限集 c.length}
  证明: by
  constructor
  · intro h
    rcases Set.mem_range.2 h with ⟨k, hk⟩
    rw [Fin.ext_iff] at hk
    dsimp at hk
    rw [← hk]
    simp [sizeUpTo_succ', k.is_lt]
  · intro h
    apply Set.mem_range.2
    refine ⟨⟨j - c.sizeUpTo i, ?_⟩, ?_⟩
    · rw [tsub_lt_iff_left, ← sizeUpTo_succ']
      · exact h.2
      · exact h.1
    · rw [Fin.ext_iff]
      exact add_tsub_cancel_of_le h.1

Depends on / 依赖: Fin.ext_iff, Set.mem_range, add_tsub_cancel_of_le, c.sizeUpTo, ext_iff, is_lt, k.is_lt, mem_range, sizeUpTo, sizeUpTo_succ, tsub_lt_iff_left
-/
theorem mem_range_embedding_iff {j : Fin n} {i : Fin c.length} :
    j in Set.range (c.embedding i) ↔ c.sizeUpTo i <= j ∧ (j : Nat) < c.sizeUpTo (i : Nat).succ := by
  constructor
  · intro h
    rcases Set.mem_range.2 h with ⟨k, hk⟩
    rw [Fin.ext_iff] at hk
    dsimp at hk
    rw [← hk]
    simp [sizeUpTo_succ', k.is_lt]
  · intro h
    apply Set.mem_range.2
    refine ⟨⟨j - c.sizeUpTo i, ?_⟩, ?_⟩
    · rw [tsub_lt_iff_left, ← sizeUpTo_succ']
      · exact h.2
      · exact h.1
    · rw [Fin.ext_iff]
      exact add_tsub_cancel_of_le h.1

/--
theorem `disjoint_range` / 定理 `disjoint_range`

English:
theorem disjoint_range
  given: {i₁ i₂ : Fin c.length} (h : i₁ != i₂)
  proof: by
  wlog h' : i₁ < i₂
  · exact (this c h.symm (h.lt_or_gt.resolve_left h')).symm
  by_contra d
  obtain ⟨x, hx₁, hx₂⟩ :
    exists x : Fin n, x in Set.range (c.embedding i₁) ∧ x in Set.range (c.embedding i₂) :=
    Set.not_disjoint_iff.1 d
  have A : (i₁ : Nat).succ <= i₂ := Nat.succ_le_of_lt h'
  apply lt_irrefl (x : Nat)
  calc
    (x : Nat) < c.sizeUpTo (i₁ : Nat).succ := (c.mem_range_embedding_iff.1 hx₁).2
    _ <= c.sizeUpTo (i₂ : Nat) := monotone_sum_take _ A
    _ <= x := (c.mem_range_embedding_iff.1 hx₂).1

中文:
定理 disjoint_range
  条件: {i₁ i₂ : 有限集 c.length} (h : i₁ != i₂)
  证明: by
  wlog h' : i₁ < i₂
  · exact (this c h.symm (h.lt_or_gt.resolve_left h')).symm
  by_contra d
  obtain ⟨x, hx₁, hx₂⟩ :
    exists x : Fin n, x in Set.range (c.embedding i₁) ∧ x in Set.range (c.embedding i₂) :=
    Set.not_disjoint_iff.1 d
  have A : (i₁ : Nat).succ <= i₂ := Nat.succ_le_of_lt h'
  apply lt_irrefl (x : Nat)
  calc
    (x : Nat) < c.sizeUpTo (i₁ : Nat).succ := (c.mem_range_embedding_iff.1 hx₁).2
    _ <= c.sizeUpTo (i₂ : Nat) := monotone_sum_take _ A
    _ <= x := (c.mem_range_embedding_iff.1 hx₂).1

Depends on / 依赖: Nat.succ_le_of_lt, Set.not_disjoint_iff, Set.range, c.embedding, c.mem_range_embedding_iff, c.sizeUpTo, embedding, h.lt_or_gt.resolve_left, h.symm, lt_irrefl, lt_or_gt, mem_range_embedding_iff, monotone_sum_take, not_disjoint_iff, resolve_left, sizeUpTo, succ_le_of_lt
-/
theorem disjoint_range {i₁ i₂ : Fin c.length} (h : i₁ != i₂) :
    Disjoint (Set.range (c.embedding i₁)) (Set.range (c.embedding i₂)) := by
  wlog h' : i₁ < i₂
  · exact (this c h.symm (h.lt_or_gt.resolve_left h')).symm
  by_contra d
  obtain ⟨x, hx₁, hx₂⟩ :
    exists x : Fin n, x in Set.range (c.embedding i₁) ∧ x in Set.range (c.embedding i₂) :=
    Set.not_disjoint_iff.1 d
  have A : (i₁ : Nat).succ <= i₂ := Nat.succ_le_of_lt h'
  apply lt_irrefl (x : Nat)
  calc
    (x : Nat) < c.sizeUpTo (i₁ : Nat).succ := (c.mem_range_embedding_iff.1 hx₁).2
    _ <= c.sizeUpTo (i₂ : Nat) := monotone_sum_take _ A
    _ <= x := (c.mem_range_embedding_iff.1 hx₂).1

/--
theorem `mem_range_embedding` / 定理 `mem_range_embedding`

English:
theorem mem_range_embedding
  given: (j : Fin n)
  statement: j in Set.range (c.embedding (c.index j))
  proof: by
  have : c.embedding (c.index j) (c.invEmbedding j) in Set.range (c.embedding (c.index j)) :=
    Set.mem_range_self _
  rwa [c.embedding_comp_inv j] at this

中文:
定理 mem_range_embedding
  条件: (j : 有限集 n)
  结论: j in 集合.range (c.embedding (c.index j))
  证明: by
  have : c.embedding (c.index j) (c.invEmbedding j) in Set.range (c.embedding (c.index j)) :=
    Set.mem_range_self _
  rwa [c.embedding_comp_inv j] at this

Depends on / 依赖: Set.mem_range_self, Set.range, c.embedding, c.embedding_comp_inv, c.index, c.invEmbedding, embedding, embedding_comp_inv, invEmbedding, mem_range_self
-/
theorem mem_range_embedding (j : Fin n) : j in Set.range (c.embedding (c.index j)) := by
  have : c.embedding (c.index j) (c.invEmbedding j) in Set.range (c.embedding (c.index j)) :=
    Set.mem_range_self _
  rwa [c.embedding_comp_inv j] at this

/--
theorem `mem_range_embedding_iff'` / 定理 `mem_range_embedding_iff'`

English:
theorem mem_range_embedding_iff'
  given: {j : Fin n} {i : Fin c.length}
  proof: by
  constructor
  · rw [← not_imp_not]
    intro h
    exact Set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j)
  · intro h
    rw [h]
    exact c.mem_range_embedding j

@[simp]

中文:
定理 mem_range_embedding_iff'
  条件: {j : 有限集 n} {i : 有限集 c.length}
  证明: by
  constructor
  · rw [← not_imp_not]
    intro h
    exact Set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j)
  · intro h
    rw [h]
    exact c.mem_range_embedding j

@[simp]

Depends on / 依赖: Set.disjoint_right, c.disjoint_range, c.mem_range_embedding, disjoint_range, disjoint_right, mem_range_embedding, not_imp_not
-/
theorem mem_range_embedding_iff' {j : Fin n} {i : Fin c.length} :
    j in Set.range (c.embedding i) ↔ i = c.index j := by
  constructor
  · rw [← not_imp_not]
    intro h
    exact Set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j)
  · intro h
    rw [h]
    exact c.mem_range_embedding j

@[simp]
/--
theorem `index_embedding` / 定理 `index_embedding`

English:
theorem index_embedding
  given: (i : Fin c.length) (j : Fin (c.blocksFun i))
  proof: by
  symm
  rw [← mem_range_embedding_iff']
  apply Set.mem_range_self

中文:
定理 index_embedding
  条件: (i : 有限集 c.length) (j : 有限集 (c.blocksFun i))
  证明: by
  symm
  rw [← mem_range_embedding_iff']
  apply Set.mem_range_self

Depends on / 依赖: Set.mem_range_self, mem_range_embedding_iff, mem_range_self
-/
theorem index_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    c.index (c.embedding i j) = i := by
  symm
  rw [← mem_range_embedding_iff']
  apply Set.mem_range_self

/--
theorem `invEmbedding_comp` / 定理 `invEmbedding_comp`

English:
theorem invEmbedding_comp
  given: (i : Fin c.length) (j : Fin (c.blocksFun i))
  proof: by
  simp_rw [coe_invEmbedding, index_embedding, coe_embedding, add_tsub_cancel_left]

中文:
定理 invEmbedding_comp
  条件: (i : 有限集 c.length) (j : 有限集 (c.blocksFun i))
  证明: by
  simp_rw [coe_invEmbedding, index_embedding, coe_embedding, add_tsub_cancel_left]

Depends on / 依赖: add_tsub_cancel_left, coe_embedding, coe_invEmbedding, index_embedding, simp_rw
-/
theorem invEmbedding_comp (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    (c.invEmbedding (c.embedding i j) : Nat) = j := by
  simp_rw [coe_invEmbedding, index_embedding, coe_embedding, add_tsub_cancel_left]

/--
Definition of `blocksFinEquiv` / `blocksFinEquiv` 的定义

English:
definition blocksFinEquiv
  signature: : (Σ i : Fin c.length, Fin (c.blocksFun i)) ≃ Fin n where
  body: c.embedding x.1 x.2
  invFun j := ⟨c.index j, c.invEmbedding j⟩
  left_inv x := by
    rcases x with ⟨i, y⟩
    dsimp
    congr; · exact c.index_embedding _ _
    rw [Fin.heq_ext_iff]
    · exact c.invEmbedding_comp _ _
    · rw [c.index_embedding]
  right_inv j := c.embedding_comp_inv j

中文:
定义 blocksFinEquiv
  签名: : (Σ i : 有限集 c.length, 有限集 (c.blocksFun i)) ≃ 有限集 n where
  定义体: c.embedding x.1 x.2
  invFun j := ⟨c.index j, c.invEmbedding j⟩
  left_inv x := by
    rcases x with ⟨i, y⟩
    dsimp
    congr; · exact c.index_embedding _ _
    rw [Fin.heq_ext_iff]
    · exact c.invEmbedding_comp _ _
    · rw [c.index_embedding]
  right_inv j := c.embedding_comp_inv j

Depends on / 依赖: c.embedding, embedding
-/
def blocksFinEquiv : (Σ i : Fin c.length, Fin (c.blocksFun i)) ≃ Fin n where
  toFun x := c.embedding x.1 x.2
  invFun j := ⟨c.index j, c.invEmbedding j⟩
  left_inv x := by
    rcases x with ⟨i, y⟩
    dsimp
    congr; · exact c.index_embedding _ _
    rw [Fin.heq_ext_iff]
    · exact c.invEmbedding_comp _ _
    · rw [c.index_embedding]
  right_inv j := c.embedding_comp_inv j

/--
theorem `blocksFun_congr` / 定理 `blocksFun_congr`

English:
theorem blocksFun_congr
  statement: {n₁ n₂ : Nat} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Fin c₁.length)
  proof: by
  cases hn
  rw [← Composition.ext_iff] at hc
  cases hc
  congr
  rwa [Fin.ext_iff]

中文:
定理 blocksFun_congr
  结论: {n₁ n₂ : 自然数} (c₁ : 余mposition n₁) (c₂ : 余mposition n₂) (i₁ : 有限集 c₁.length)
  证明: by
  cases hn
  rw [← Composition.ext_iff] at hc
  cases hc
  congr
  rwa [Fin.ext_iff]

Depends on / 依赖: Composition, Composition.ext_iff, Fin.ext_iff, ext_iff
-/
theorem blocksFun_congr {n₁ n₂ : Nat} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Fin c₁.length)
    (i₂ : Fin c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : Nat) = i₂) :
    c₁.blocksFun i₁ = c₂.blocksFun i₂ := by
  cases hn
  rw [← Composition.ext_iff] at hc
  cases hc
  congr
  rwa [Fin.ext_iff]

/--
theorem `sigma_eq_iff_blocks_eq` / 定理 `sigma_eq_iff_blocks_eq`

English:
theorem sigma_eq_iff_blocks_eq
  given: {c : Σ n, Composition n} {c' : Σ n, Composition n}
  proof: by
  refine ⟨fun H => by rw [H], fun H => ?_⟩
  rcases c with ⟨n, c⟩
  rcases c' with ⟨n', c'⟩
  have : n = n' := by rw [← c.blocks_sum, ← c'.blocks_sum, H]
  induction this
  congr
  ext1
  exact H

@[to_additive]

中文:
定理 sigma_eq_iff_blocks_eq
  条件: {c : Σ n, 余mposition n} {c' : Σ n, 余mposition n}
  证明: by
  refine ⟨fun H => by rw [H], fun H => ?_⟩
  rcases c with ⟨n, c⟩
  rcases c' with ⟨n', c'⟩
  have : n = n' := by rw [← c.blocks_sum, ← c'.blocks_sum, H]
  induction this
  congr
  ext1
  exact H

@[to_additive]

Depends on / 依赖: blocks_sum, c.blocks_sum
-/
theorem sigma_eq_iff_blocks_eq {c : Σ n, Composition n} {c' : Σ n, Composition n} :
    c = c' ↔ c.2.blocks = c'.2.blocks := by
  refine ⟨fun H => by rw [H], fun H => ?_⟩
  rcases c with ⟨n, c⟩
  rcases c' with ⟨n', c'⟩
  have : n = n' := by rw [← c.blocks_sum, ← c'.blocks_sum, H]
  induction this
  congr
  ext1
  exact H

@[to_additive]
/--
lemma `prod_prod_apply_embedding` / 引理 `prod_prod_apply_embedding`

English:
lemma prod_prod_apply_embedding
  given: {A : Type*} [CommMonoid A] (a : Fin n -> A) (x : Composition n)
  proof: by
  simpa [Finset.prod_sigma', Finset.univ_sigma_univ] using! x.blocksFinEquiv.prod_comp a

中文:
引理 prod_prod_apply_embedding
  条件: {A : 类型} [交换幺半群 A] (a : 有限集 n -> A) (x : 余mposition n)
  证明: by
  simpa [Finset.prod_sigma', Finset.univ_sigma_univ] using! x.blocksFinEquiv.prod_comp a

Depends on / 依赖: Finset, Finset.prod_sigma, Finset.univ_sigma_univ, blocksFinEquiv, prod_comp, prod_sigma, univ_sigma_univ, x.blocksFinEquiv.prod_comp
-/
lemma prod_prod_apply_embedding {A : Type*} [CommMonoid A] (a : Fin n -> A) (x : Composition n) :
    ∏ i, ∏ j, a (x.embedding i j) = ∏ i, a i := by
  simpa [Finset.prod_sigma', Finset.univ_sigma_univ] using! x.blocksFinEquiv.prod_comp a

/-! ### The composition `Composition.ones` -/


/--
Definition of `ones` / `ones` 的定义

English:
definition ones
  signature: (n : Nat)
  body: ⟨replicate n (1 : Nat), fun {i} hi => by simp [List.eq_of_mem_replicate hi], by simp⟩

中文:
定义 ones
  签名: (n : 自然数)
  定义体: ⟨replicate n (1 : Nat), fun {i} hi => by simp [List.eq_of_mem_replicate hi], by simp⟩

Depends on / 依赖: List.eq_of_mem_replicate, eq_of_mem_replicate, replicate
-/
def ones (n : Nat) : Composition n :=
  ⟨replicate n (1 : Nat), fun {i} hi => by simp [List.eq_of_mem_replicate hi], by simp⟩

instance {n : Nat} : Inhabited (Composition n) :=
  ⟨Composition.ones n⟩

@[simp]
/--
theorem `ones_length` / 定理 `ones_length`

English:
theorem ones_length
  given: (n : Nat)
  statement: (ones n).length = n
  proof: List.length_replicate

@[simp]

中文:
定理 ones_length
  条件: (n : 自然数)
  结论: (ones n).length = n
  证明: List.length_replicate

@[simp]

Depends on / 依赖: List.length_replicate, length_replicate
-/
theorem ones_length (n : Nat) : (ones n).length = n :=
  List.length_replicate

@[simp]
/--
theorem `ones_blocks` / 定理 `ones_blocks`

English:
theorem ones_blocks
  given: (n : Nat)
  statement: (ones n).blocks = replicate n (1 : Nat)
  proof: rfl

中文:
定理 ones_blocks
  条件: (n : 自然数)
  结论: (ones n).blocks = replicate n (1 : 自然数)
  证明: rfl
-/
theorem ones_blocks (n : Nat) : (ones n).blocks = replicate n (1 : Nat) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ones_blocksFun` / 定理 `ones_blocksFun`

English:
theorem ones_blocksFun
  given: (n : Nat) (i : Fin (ones n).length)
  statement: (ones n).blocksFun i = 1
  proof: by
  simp only [blocksFun, ones, get_eq_getElem, getElem_replicate]

@[simp]

中文:
定理 ones_blocksFun
  条件: (n : 自然数) (i : 有限集 (ones n).length)
  结论: (ones n).blocksFun i = 1
  证明: by
  simp only [blocksFun, ones, get_eq_getElem, getElem_replicate]

@[simp]

Depends on / 依赖: blocksFun, getElem_replicate, get_eq_getElem
-/
theorem ones_blocksFun (n : Nat) (i : Fin (ones n).length) : (ones n).blocksFun i = 1 := by
  simp only [blocksFun, ones, get_eq_getElem, getElem_replicate]

@[simp]
/--
theorem `ones_sizeUpTo` / 定理 `ones_sizeUpTo`

English:
theorem ones_sizeUpTo
  given: (n : Nat) (i : Nat)
  statement: (ones n).sizeUpTo i = min i n
  proof: by
  simp [sizeUpTo, ones_blocks, take_replicate]

@[simp]

中文:
定理 ones_sizeUpTo
  条件: (n : 自然数) (i : 自然数)
  结论: (ones n).sizeUpTo i = 最小值 i n
  证明: by
  simp [sizeUpTo, ones_blocks, take_replicate]

@[simp]

Depends on / 依赖: ones_blocks, sizeUpTo, take_replicate
-/
theorem ones_sizeUpTo (n : Nat) (i : Nat) : (ones n).sizeUpTo i = min i n := by
  simp [sizeUpTo, ones_blocks, take_replicate]

@[simp]
/--
theorem `ones_embedding` / 定理 `ones_embedding`

English:
theorem ones_embedding
  given: (i : Fin (ones n).length) (h : 0 < (ones n).blocksFun i)
  proof: by
  ext
  simpa using i.2.le

中文:
定理 ones_embedding
  条件: (i : 有限集 (ones n).length) (h : 0 < (ones n).blocksFun i)
  证明: by
  ext
  simpa using i.2.le
-/
theorem ones_embedding (i : Fin (ones n).length) (h : 0 < (ones n).blocksFun i) :
    (ones n).embedding i ⟨0, h⟩ = ⟨i, lt_of_lt_of_le i.2 (ones n).length_le⟩ := by
  ext
  simpa using i.2.le

/--
theorem `eq_ones_iff` / 定理 `eq_ones_iff`

English:
theorem eq_ones_iff
  given: {c : Composition n}
  statement: c = ones n ↔ forall i in c.blocks, i = 1
  proof: by
  constructor
  · rintro rfl
    exact fun i => eq_of_mem_replicate
  · intro H
    ext1
    have A : c.blocks = replicate c.blocks.length 1 := eq_replicate_of_mem H
    have : c.blocks.length = n := by
      conv_rhs => rw [← c.blocks_sum, A]
      simp
    rw [A]; rw [this]; rw [ones_blocks]

中文:
定理 eq_ones_iff
  条件: {c : 余mposition n}
  结论: c = ones n ↔ 对任意 i in c.blocks, i = 1
  证明: by
  constructor
  · rintro rfl
    exact fun i => eq_of_mem_replicate
  · intro H
    ext1
    have A : c.blocks = replicate c.blocks.length 1 := eq_replicate_of_mem H
    have : c.blocks.length = n := by
      conv_rhs => rw [← c.blocks_sum, A]
      simp
    rw [A]; rw [this]; rw [ones_blocks]

Depends on / 依赖: blocks, blocks_sum, c.blocks, c.blocks.length, c.blocks_sum, conv_rhs, eq_of_mem_replicate, eq_replicate_of_mem, length, ones_blocks, replicate
-/
theorem eq_ones_iff {c : Composition n} : c = ones n ↔ forall i in c.blocks, i = 1 := by
  constructor
  · rintro rfl
    exact fun i => eq_of_mem_replicate
  · intro H
    ext1
    have A : c.blocks = replicate c.blocks.length 1 := eq_replicate_of_mem H
    have : c.blocks.length = n := by
      conv_rhs => rw [← c.blocks_sum, A]
      simp
    rw [A]; rw [this]; rw [ones_blocks]

/--
theorem `ne_ones_iff` / 定理 `ne_ones_iff`

English:
theorem ne_ones_iff
  given: {c : Composition n}
  statement: c != ones n ↔ exists i in c.blocks, 1 < i
  proof: by
  refine (not_congr eq_ones_iff).trans ?_
  have : forall j in c.blocks, j = 1 ↔ j <= 1 := fun j hj => by simp [le_antisymm_iff, c.one_le_blocks hj]
  simp +contextual [this]

中文:
定理 ne_ones_iff
  条件: {c : 余mposition n}
  结论: c != ones n ↔ 存在 i in c.blocks, 1 < i
  证明: by
  refine (not_congr eq_ones_iff).trans ?_
  have : forall j in c.blocks, j = 1 ↔ j <= 1 := fun j hj => by simp [le_antisymm_iff, c.one_le_blocks hj]
  simp +contextual [this]

Depends on / 依赖: blocks, c.blocks, c.one_le_blocks, contextual, eq_ones_iff, le_antisymm_iff, not_congr, one_le_blocks
-/
theorem ne_ones_iff {c : Composition n} : c != ones n ↔ exists i in c.blocks, 1 < i := by
  refine (not_congr eq_ones_iff).trans ?_
  have : forall j in c.blocks, j = 1 ↔ j <= 1 := fun j hj => by simp [le_antisymm_iff, c.one_le_blocks hj]
  simp +contextual [this]

/--
theorem `eq_ones_iff_length` / 定理 `eq_ones_iff_length`

English:
theorem eq_ones_iff_length
  given: {c : Composition n}
  statement: c = ones n ↔ c.length = n
  proof: by
  constructor
  · rintro rfl
    exact ones_length n
  · contrapose
    intro H length_n
    apply lt_irrefl n
    calc
      n = ∑ i : Fin c.length, 1 := by simp [length_n]
      _ < ∑ i : Fin c.length, c.blocksFun i := by
        {
        obtain ⟨i, hi, i_blocks⟩ : exists i in c.blocks, 1 < i := ne_ones_iff.1 H
        rw [← ofFn_blocksFun]; rw [mem_ofFn' c.blocksFun]; rw [Set.mem_range] at hi
        obtain ⟨j : Fin c.length, hj : c.blocksFun j = i⟩ := hi
        rw [← hj] at i_blocks
        exact Finset.sum_lt_sum (fun i _ => one_le_blocksFun c i) ⟨j, Finset.mem_univ _, i_blocks⟩
        }
      _ = n := c.sum_blocksFun

中文:
定理 eq_ones_iff_length
  条件: {c : 余mposition n}
  结论: c = ones n ↔ c.length = n
  证明: by
  constructor
  · rintro rfl
    exact ones_length n
  · contrapose
    intro H length_n
    apply lt_irrefl n
    calc
      n = ∑ i : Fin c.length, 1 := by simp [length_n]
      _ < ∑ i : Fin c.length, c.blocksFun i := by
        {
        obtain ⟨i, hi, i_blocks⟩ : exists i in c.blocks, 1 < i := ne_ones_iff.1 H
        rw [← ofFn_blocksFun]; rw [mem_ofFn' c.blocksFun]; rw [Set.mem_range] at hi
        obtain ⟨j : Fin c.length, hj : c.blocksFun j = i⟩ := hi
        rw [← hj] at i_blocks
        exact Finset.sum_lt_sum (fun i _ => one_le_blocksFun c i) ⟨j, Finset.mem_univ _, i_blocks⟩
        }
      _ = n := c.sum_blocksFun

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum_lt_sum, Set.mem_range, blocks, blocksFun, c.blocks, c.blocksFun, c.length, contrapose, i_blocks, length, length_n, lt_irrefl, mem_ofFn, mem_range, mem_univ, ne_ones_iff, ofFn_blocksFun, one_le_blocksFun
-/
theorem eq_ones_iff_length {c : Composition n} : c = ones n ↔ c.length = n := by
  constructor
  · rintro rfl
    exact ones_length n
  · contrapose
    intro H length_n
    apply lt_irrefl n
    calc
      n = ∑ i : Fin c.length, 1 := by simp [length_n]
      _ < ∑ i : Fin c.length, c.blocksFun i := by
        {
        obtain ⟨i, hi, i_blocks⟩ : exists i in c.blocks, 1 < i := ne_ones_iff.1 H
        rw [← ofFn_blocksFun]; rw [mem_ofFn' c.blocksFun]; rw [Set.mem_range] at hi
        obtain ⟨j : Fin c.length, hj : c.blocksFun j = i⟩ := hi
        rw [← hj] at i_blocks
        exact Finset.sum_lt_sum (fun i _ => one_le_blocksFun c i) ⟨j, Finset.mem_univ _, i_blocks⟩
        }
      _ = n := c.sum_blocksFun

/--
theorem `eq_ones_iff_le_length` / 定理 `eq_ones_iff_le_length`

English:
theorem eq_ones_iff_le_length
  given: {c : Composition n}
  statement: c = ones n ↔ n <= c.length
  proof: by
  simp [eq_ones_iff_length, le_antisymm_iff, c.length_le]

中文:
定理 eq_ones_iff_le_length
  条件: {c : 余mposition n}
  结论: c = ones n ↔ n <= c.length
  证明: by
  simp [eq_ones_iff_length, le_antisymm_iff, c.length_le]

Depends on / 依赖: c.length_le, eq_ones_iff_length, le_antisymm_iff, length_le
-/
theorem eq_ones_iff_le_length {c : Composition n} : c = ones n ↔ n <= c.length := by
  simp [eq_ones_iff_length, le_antisymm_iff, c.length_le]

/-! ### The composition `Composition.single` -/

/--
Definition of `single` / `single` 的定义

English:
definition single
  signature: (n : Nat) (h : 0 < n)
  body: ⟨[n], by simp [h], by simp⟩

@[simp]

中文:
定义 single
  签名: (n : 自然数) (h : 0 < n)
  定义体: ⟨[n], by simp [h], by simp⟩

@[simp]
-/
def single (n : Nat) (h : 0 < n) : Composition n :=
  ⟨[n], by simp [h], by simp⟩

@[simp]
/--
theorem `single_length` / 定理 `single_length`

English:
theorem single_length
  given: {n : Nat} (h : 0 < n)
  statement: (single n h).length = 1
  proof: rfl

@[simp]

中文:
定理 single_length
  条件: {n : 自然数} (h : 0 < n)
  结论: (single n h).length = 1
  证明: rfl

@[simp]
-/
theorem single_length {n : Nat} (h : 0 < n) : (single n h).length = 1 :=
  rfl

@[simp]
/--
theorem `single_blocks` / 定理 `single_blocks`

English:
theorem single_blocks
  given: {n : Nat} (h : 0 < n)
  statement: (single n h).blocks = [n]
  proof: rfl

中文:
定理 single_blocks
  条件: {n : 自然数} (h : 0 < n)
  结论: (single n h).blocks = [n]
  证明: rfl
-/
theorem single_blocks {n : Nat} (h : 0 < n) : (single n h).blocks = [n] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `single_blocksFun` / 定理 `single_blocksFun`

English:
theorem single_blocksFun
  given: {n : Nat} (h : 0 < n) (i : Fin (single n h).length)
  proof: by simp [blocksFun, single]

中文:
定理 single_blocksFun
  条件: {n : 自然数} (h : 0 < n) (i : 有限集 (single n h).length)
  证明: by simp [blocksFun, single]

Depends on / 依赖: blocksFun, single
-/
theorem single_blocksFun {n : Nat} (h : 0 < n) (i : Fin (single n h).length) :
    (single n h).blocksFun i = n := by simp [blocksFun, single]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `single_embedding` / 定理 `single_embedding`

English:
theorem single_embedding
  given: {n : Nat} (h : 0 < n) (i : Fin n)
  proof: by
  ext
  simp

中文:
定理 single_embedding
  条件: {n : 自然数} (h : 0 < n) (i : 有限集 n)
  证明: by
  ext
  simp

Depends on / 依赖: TopCat, TopCat.epi_iff_surjective, epi_iff_surjective, topCatAdjunctionCounit_bijective
-/
theorem single_embedding {n : Nat} (h : 0 < n) (i : Fin n) :
    ((single n h).embedding (0 : Fin 1)) i = i := by
  ext
  simp

/--
theorem `eq_single_iff_length` / 定理 `eq_single_iff_length`

English:
theorem eq_single_iff_length
  given: {n : Nat} (h : 0 < n) {c : Composition n}
  proof: by
  constructor
  · intro H
    rw [H]
    exact single_length h
  · intro H
    ext1
    have A : c.blocks.length = 1 := H ▸ c.blocks_length
    have B : c.blocks.sum = n := c.blocks_sum
    rw [eq_cons_of_length_one A] at B ⊢
    simpa [single_blocks] using B

中文:
定理 eq_single_iff_length
  条件: {n : 自然数} (h : 0 < n) {c : 余mposition n}
  证明: by
  constructor
  · intro H
    rw [H]
    exact single_length h
  · intro H
    ext1
    have A : c.blocks.length = 1 := H ▸ c.blocks_length
    have B : c.blocks.sum = n := c.blocks_sum
    rw [eq_cons_of_length_one A] at B ⊢
    simpa [single_blocks] using B

Depends on / 依赖: blocks, blocks_length, blocks_sum, c.blocks.length, c.blocks.sum, c.blocks_length, c.blocks_sum, eq_cons_of_length_one, length, single_blocks, single_length
-/
theorem eq_single_iff_length {n : Nat} (h : 0 < n) {c : Composition n} :
    c = single n h ↔ c.length = 1 := by
  constructor
  · intro H
    rw [H]
    exact single_length h
  · intro H
    ext1
    have A : c.blocks.length = 1 := H ▸ c.blocks_length
    have B : c.blocks.sum = n := c.blocks_sum
    rw [eq_cons_of_length_one A] at B ⊢
    simpa [single_blocks] using B

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ne_single_iff` / 定理 `ne_single_iff`

English:
theorem ne_single_iff
  given: {n : Nat} (hn : 0 < n) {c : Composition n}
  proof: by
  contrapose!
  constructor
  · rintro rfl
    exact ⟨⟨0, by simp⟩, by simp⟩
  · rintro ⟨i, hi⟩
    rw [eq_single_iff_length]
    have : forall j : Fin c.length, j = i := by
      intro j
      by_contra ji
      apply lt_irrefl (∑ k, c.blocksFun k)
      calc
        ∑ k, c.blocksFun k <= c.blocksFun i := by simp only [c.sum_blocksFun, hi]
        _ < ∑ k, c.blocksFun k :=
          Finset.single_lt_sum ji (Finset.mem_univ _) (Finset.mem_univ _) (c.one_le_blocksFun j)
            fun _ _ _ => zero_le
    simpa using Fintype.card_eq_one_of_forall_eq this

中文:
定理 ne_single_iff
  条件: {n : 自然数} (hn : 0 < n) {c : 余mposition n}
  证明: by
  contrapose!
  constructor
  · rintro rfl
    exact ⟨⟨0, by simp⟩, by simp⟩
  · rintro ⟨i, hi⟩
    rw [eq_single_iff_length]
    have : forall j : Fin c.length, j = i := by
      intro j
      by_contra ji
      apply lt_irrefl (∑ k, c.blocksFun k)
      calc
        ∑ k, c.blocksFun k <= c.blocksFun i := by simp only [c.sum_blocksFun, hi]
        _ < ∑ k, c.blocksFun k :=
          Finset.single_lt_sum ji (Finset.mem_univ _) (Finset.mem_univ _) (c.one_le_blocksFun j)
            fun _ _ _ => zero_le
    simpa using Fintype.card_eq_one_of_forall_eq this

Depends on / 依赖: Finset, Finset.mem_univ, Finset.single_lt_sum, Fintype, Fintype.card_eq_one_of_forall_eq, blocksFun, c.blocksFun, c.length, c.one_le_blocksFun, c.sum_blocksFun, card_eq_one_of_forall_eq, continuous_coinduced_dom, continuous_coinducingCoprod, continuous_sigma_iff, contrapose, eq_single_iff_length, length, lt_irrefl, mem_univ, one_le_blocksFun
-/
theorem ne_single_iff {n : Nat} (hn : 0 < n) {c : Composition n} :
    c != single n hn ↔ forall i, c.blocksFun i < n := by
  contrapose!
  constructor
  · rintro rfl
    exact ⟨⟨0, by simp⟩, by simp⟩
  · rintro ⟨i, hi⟩
    rw [eq_single_iff_length]
    have : forall j : Fin c.length, j = i := by
      intro j
      by_contra ji
      apply lt_irrefl (∑ k, c.blocksFun k)
      calc
        ∑ k, c.blocksFun k <= c.blocksFun i := by simp only [c.sum_blocksFun, hi]
        _ < ∑ k, c.blocksFun k :=
          Finset.single_lt_sum ji (Finset.mem_univ _) (Finset.mem_univ _) (c.one_le_blocksFun j)
            fun _ _ _ => zero_le
    simpa using Fintype.card_eq_one_of_forall_eq this

variable {m : Nat}

/-- Change `n` in `(c : Composition n)` to a propositionally equal value. -/
@[simps]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: (c : Composition m) (hmn : m = n)
  body: c
  blocks_sum := c.blocks_sum.trans hmn

@[simp]

中文:
定义 cast
  签名: (c : 余mposition m) (hmn : m = n)
  定义体: c
  blocks_sum := c.blocks_sum.trans hmn

@[simp]

Depends on / 依赖: UCompactlyGeneratedSpace, X.toTopCat, toTopCat
-/
protected def cast (c : Composition m) (hmn : m = n) : Composition n where
  __ := c
  blocks_sum := c.blocks_sum.trans hmn

@[simp]
/--
theorem `cast_rfl` / 定理 `cast_rfl`

English:
theorem cast_rfl
  given: (c : Composition n)
  statement: c.cast rfl = c
  proof: rfl

中文:
定理 cast_rfl
  条件: (c : 余mposition n)
  结论: c.cast rfl = c
  证明: rfl
-/
theorem cast_rfl (c : Composition n) : c.cast rfl = c := rfl

/--
theorem `cast_heq` / 定理 `cast_heq`

English:
theorem cast_heq
  given: (c : Composition m) (hmn : m = n)
  statement: c.cast hmn ≍ c
  proof: by subst m; rfl

中文:
定理 cast_heq
  条件: (c : 余mposition m) (hmn : m = n)
  结论: c.cast hmn ≍ c
  证明: by subst m; rfl
-/
theorem cast_heq (c : Composition m) (hmn : m = n) : c.cast hmn ≍ c := by subst m; rfl

/--
theorem `cast_eq_cast` / 定理 `cast_eq_cast`

English:
theorem cast_eq_cast
  given: (c : Composition m) (hmn : m = n)
  proof: by
  subst m
  rfl

中文:
定理 cast_eq_cast
  条件: (c : 余mposition m) (hmn : m = n)
  证明: by
  subst m
  rfl
-/
theorem cast_eq_cast (c : Composition m) (hmn : m = n) :
    c.cast hmn = cast (hmn ▸ rfl) c := by
  subst m
  rfl

/-- Append two compositions to get a composition of the sum of numbers. -/
@[simps]
/--
Definition of `append` / `append` 的定义

English:
definition append
  signature: (c₁ : Composition m) (c₂ : Composition n)
  body: c₁.blocks ++ c₂.blocks
  blocks_pos := by
    intro i hi
    rw [mem_append] at hi
    exact hi.elim c₁.blocks_pos c₂.blocks_pos
  blocks_sum := by simp

中文:
定义 append
  签名: (c₁ : 余mposition m) (c₂ : 余mposition n)
  定义体: c₁.blocks ++ c₂.blocks
  blocks_pos := by
    intro i hi
    rw [mem_append] at hi
    exact hi.elim c₁.blocks_pos c₂.blocks_pos
  blocks_sum := by simp

Depends on / 依赖: blocks
-/
def append (c₁ : Composition m) (c₂ : Composition n) : Composition (m + n) where
  blocks := c₁.blocks ++ c₂.blocks
  blocks_pos := by
    intro i hi
    rw [mem_append] at hi
    exact hi.elim c₁.blocks_pos c₂.blocks_pos
  blocks_sum := by simp

/-- Reverse the order of blocks in a composition. -/
@[simps]
/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: (c : Composition n)
  body: c.blocks.reverse
  blocks_pos hi := c.blocks_pos (mem_reverse.mp hi)
  blocks_sum := by simp

@[simp]

中文:
定义 reverse
  签名: (c : 余mposition n)
  定义体: c.blocks.reverse
  blocks_pos hi := c.blocks_pos (mem_reverse.mp hi)
  blocks_sum := by simp

@[simp]

Depends on / 依赖: blocks, c.blocks.reverse, reverse
-/
def reverse (c : Composition n) : Composition n where
  blocks := c.blocks.reverse
  blocks_pos hi := c.blocks_pos (mem_reverse.mp hi)
  blocks_sum := by simp

@[simp]
/--
lemma `reverse_reverse` / 引理 `reverse_reverse`

English:
lemma reverse_reverse
  given: (c : Composition n)
  statement: c.reverse.reverse = c
  proof: Composition.ext List.reverse_reverse _

中文:
引理 reverse_reverse
  条件: (c : 余mposition n)
  结论: c.reverse.reverse = c
  证明: Composition.ext List.reverse_reverse _

Depends on / 依赖: Composition, Composition.ext, List.reverse_reverse, reverse_reverse
-/
lemma reverse_reverse (c : Composition n) : c.reverse.reverse = c :=
Composition.ext List.reverse_reverse _

/--
lemma `reverse_involutive` / 引理 `reverse_involutive`

English:
lemma reverse_involutive
  statement: Function.Involutive (@reverse n)
  proof: reverse_reverse

中文:
引理 reverse_involutive
  结论: 函数.对合 (@reverse n)
  证明: reverse_reverse

Depends on / 依赖: reverse_reverse
-/
lemma reverse_involutive : Function.Involutive (@reverse n) := reverse_reverse
/--
lemma `reverse_bijective` / 引理 `reverse_bijective`

English:
lemma reverse_bijective
  statement: Function.Bijective (@reverse n)
  proof: reverse_involutive.bijective

中文:
引理 reverse_bijective
  结论: 函数.双射 (@reverse n)
  证明: reverse_involutive.bijective

Depends on / 依赖: bijective, reverse_involutive, reverse_involutive.bijective
-/
lemma reverse_bijective : Function.Bijective (@reverse n) := reverse_involutive.bijective
/--
lemma `reverse_injective` / 引理 `reverse_injective`

English:
lemma reverse_injective
  statement: Function.Injective (@reverse n)
  proof: reverse_involutive.injective

中文:
引理 reverse_injective
  结论: 函数.单射 (@reverse n)
  证明: reverse_involutive.injective

Depends on / 依赖: injective, reverse_involutive, reverse_involutive.injective
-/
lemma reverse_injective : Function.Injective (@reverse n) := reverse_involutive.injective
/--
lemma `reverse_surjective` / 引理 `reverse_surjective`

English:
lemma reverse_surjective
  statement: Function.Surjective (@reverse n)
  proof: reverse_involutive.surjective

@[simp]

中文:
引理 reverse_surjective
  结论: 函数.满射 (@reverse n)
  证明: reverse_involutive.surjective

@[simp]

Depends on / 依赖: reverse_involutive, reverse_involutive.surjective, surjective
-/
lemma reverse_surjective : Function.Surjective (@reverse n) := reverse_involutive.surjective

@[simp]
/--
lemma `reverse_inj` / 引理 `reverse_inj`

English:
lemma reverse_inj
  given: {c₁ c₂ : Composition n}
  statement: c₁.reverse = c₂.reverse ↔ c₁ = c₂
  proof: reverse_injective.eq_iff

@[simp]

中文:
引理 reverse_inj
  条件: {c₁ c₂ : 余mposition n}
  结论: c₁.reverse = c₂.reverse ↔ c₁ = c₂
  证明: reverse_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, reverse_injective, reverse_injective.eq_iff
-/
lemma reverse_inj {c₁ c₂ : Composition n} : c₁.reverse = c₂.reverse ↔ c₁ = c₂ :=
  reverse_injective.eq_iff

@[simp]
/--
lemma `reverse_ones` / 引理 `reverse_ones`

English:
lemma reverse_ones
  statement: (ones n).reverse = ones n
  proof: by ext1; simp

@[simp]

中文:
引理 reverse_ones
  结论: (ones n).reverse = ones n
  证明: by ext1; simp

@[simp]
-/
lemma reverse_ones : (ones n).reverse = ones n := by ext1; simp

@[simp]
/--
lemma `reverse_single` / 引理 `reverse_single`

English:
lemma reverse_single
  given: (hn : 0 < n)
  statement: (single n hn).reverse = single n hn
  proof: by ext1; simp

@[simp]

中文:
引理 reverse_single
  条件: (hn : 0 < n)
  结论: (single n hn).reverse = single n hn
  证明: by ext1; simp

@[simp]
-/
lemma reverse_single (hn : 0 < n) : (single n hn).reverse = single n hn := by ext1; simp

@[simp]
/--
lemma `reverse_eq_ones` / 引理 `reverse_eq_ones`

English:
lemma reverse_eq_ones
  given: {c : Composition n}
  statement: c.reverse = ones n ↔ c = ones n
  proof: reverse_injective.eq_iff' reverse_ones

@[simp]

中文:
引理 reverse_eq_ones
  条件: {c : 余mposition n}
  结论: c.reverse = ones n ↔ c = ones n
  证明: reverse_injective.eq_iff' reverse_ones

@[simp]

Depends on / 依赖: eq_iff, reverse_injective, reverse_injective.eq_iff, reverse_ones
-/
lemma reverse_eq_ones {c : Composition n} : c.reverse = ones n ↔ c = ones n :=
  reverse_injective.eq_iff' reverse_ones

@[simp]
/--
lemma `reverse_eq_single` / 引理 `reverse_eq_single`

English:
lemma reverse_eq_single
  given: {hn : 0 < n} {c : Composition n}
  proof: reverse_injective.eq_iff' reverse_single _

中文:
引理 reverse_eq_single
  条件: {hn : 0 < n} {c : 余mposition n}
  证明: reverse_injective.eq_iff' reverse_single _

Depends on / 依赖: eq_iff, reverse_injective, reverse_injective.eq_iff, reverse_single
-/
lemma reverse_eq_single {hn : 0 < n} {c : Composition n} :
    c.reverse = single n hn ↔ c = single n hn :=
reverse_injective.eq_iff' reverse_single _

/--
lemma `reverse_append` / 引理 `reverse_append`

English:
lemma reverse_append
  given: (c₁ : Composition m) (c₂ : Composition n)
  proof: Composition.ext by simp

中文:
引理 reverse_append
  条件: (c₁ : 余mposition m) (c₂ : 余mposition n)
  证明: Composition.ext by simp

Depends on / 依赖: Composition, Composition.ext
-/
lemma reverse_append (c₁ : Composition m) (c₂ : Composition n) :
    reverse (append c₁ c₂) = (append c₂.reverse c₁.reverse).cast (add_comm _ _) :=
Composition.ext by simp

/-- Induction (recursion) principle on `c : Composition _`
that corresponds to the usual induction on the list of blocks of `c`. -/
@[elab_as_elim]
/--
Definition of `recOnSingleAppend` / `recOnSingleAppend` 的定义

English:
definition recOnSingleAppend
  signature: {motive : forall n, Composition n -> Sort*} {n : Nat} (c : Composition n)
  body: match n, c with
  | _, ⟨blocks, blocks_pos, rfl⟩ =>
    match blocks with
    | [] => zero
    | 0 :: _ => by simp at blocks_pos
    | (k + 1) :: l =>
single_append k l.sum ⟨l, fun hi => blocks_pos mem_cons_of_mem _ hi, rfl⟩
        recOnSingleAppend _ zero single_append

中文:
定义 recOnSingleAppend
  签名: {motive : 对任意 n, 余mposition n -> 类型层*} {n : 自然数} (c : 余mposition n)
  定义体: match n, c with
  | _, ⟨blocks, blocks_pos, rfl⟩ =>
    match blocks with
    | [] => zero
    | 0 :: _ => by simp at blocks_pos
    | (k + 1) :: l =>
single_append k l.sum ⟨l, fun hi => blocks_pos mem_cons_of_mem _ hi, rfl⟩
        recOnSingleAppend _ zero single_append

Depends on / 依赖: blocks, blocks_pos, l.sum, mem_cons_of_mem, recOnSingleAppend, single_append
-/
def recOnSingleAppend {motive : forall n, Composition n -> Sort*} {n : Nat} (c : Composition n)
    (zero : motive 0 (ones 0))
    (single_append : forall k n c, motive n c ->
      motive (k + 1 + n) (append (single (k + 1) k.succ_pos) c)) :
    motive n c :=
  match n, c with
  | _, ⟨blocks, blocks_pos, rfl⟩ =>
    match blocks with
    | [] => zero
    | 0 :: _ => by simp at blocks_pos
    | (k + 1) :: l =>
single_append k l.sum ⟨l, fun hi => blocks_pos mem_cons_of_mem _ hi, rfl⟩
        recOnSingleAppend _ zero single_append

/-- Induction (recursion) principle on `c : Composition _`
that corresponds to the reverse induction on the list of blocks of `c`. -/
@[elab_as_elim]
/--
Definition of `recOnAppendSingle` / `recOnAppendSingle` 的定义

English:
definition recOnAppendSingle
  signature: {motive : forall n, Composition n -> Sort*} {n : Nat} (c : Composition n)
  body: reverse_reverse c ▸ c.reverse.recOnSingleAppend zero fun k n c ih => by
    convert! append_single k n c.reverse ih using 1
    · apply add_comm
    · rw [reverse_append, reverse_single]
      apply cast_heq

中文:
定义 recOnAppendSingle
  签名: {motive : 对任意 n, 余mposition n -> 类型层*} {n : 自然数} (c : 余mposition n)
  定义体: reverse_reverse c ▸ c.reverse.recOnSingleAppend zero fun k n c ih => by
    convert! append_single k n c.reverse ih using 1
    · apply add_comm
    · rw [reverse_append, reverse_single]
      apply cast_heq

Depends on / 依赖: add_comm, append_single, c.reverse, c.reverse.recOnSingleAppend, cast_heq, convert, recOnSingleAppend, reverse, reverse_append, reverse_reverse, reverse_single
-/
def recOnAppendSingle {motive : forall n, Composition n -> Sort*} {n : Nat} (c : Composition n)
    (zero : motive 0 (ones 0))
    (append_single : forall k n c, motive n c ->
      motive (n + (k + 1)) (append c (single (k + 1) k.succ_pos))) :
    motive n c :=
  reverse_reverse c ▸ c.reverse.recOnSingleAppend zero fun k n c ih => by
    convert! append_single k n c.reverse ih using 1
    · apply add_comm
    · rw [reverse_append, reverse_single]
      apply cast_heq

end Composition

/-!
### Splitting a list

Given a list of length `n` and a composition `c` of `n`, one can split `l` into `c.length` sublists
of respective lengths `c.blocksFun 0`, ..., `c.blocksFun (c.length-1)`. This is inverse to the
join operation.
-/


namespace List

variable {α : Type*}

/--
Definition of `splitWrtCompositionAux` / `splitWrtCompositionAux` 的定义

English:
definition splitWrtCompositionAux
  signature: : List α -> List Nat -> List (List α)
  body: l.splitAt n
    l₁::splitWrtCompositionAux l₂ ns

中文:
定义 splitWrtCompositionAux
  签名: : 列表 α -> 列表 自然数 -> 列表 (列表 α)
  定义体: l.splitAt n
    l₁::splitWrtCompositionAux l₂ ns

Depends on / 依赖: l.splitAt, splitAt
-/
def splitWrtCompositionAux : List α -> List Nat -> List (List α)
  | _, [] => []
  | l, n::ns =>
    let (l₁, l₂) := l.splitAt n
    l₁::splitWrtCompositionAux l₂ ns

/--
Definition of `splitWrtComposition` / `splitWrtComposition` 的定义

English:
definition splitWrtComposition
  signature: (l : List α) (c : Composition n)
  body: splitWrtCompositionAux l c.blocks

@[local simp]

中文:
定义 splitWrtComposition
  签名: (l : 列表 α) (c : 余mposition n)
  定义体: splitWrtCompositionAux l c.blocks

@[local simp]

Depends on / 依赖: blocks, c.blocks, splitWrtCompositionAux
-/
def splitWrtComposition (l : List α) (c : Composition n) : List (List α) :=
  splitWrtCompositionAux l c.blocks

@[local simp]
/--
theorem `splitWrtCompositionAux_cons` / 定理 `splitWrtCompositionAux_cons`

English:
theorem splitWrtCompositionAux_cons
  given: (l : List α) (n ns)
  proof: by
  simp [splitWrtCompositionAux]

中文:
定理 splitWrtCompositionAux_cons
  条件: (l : 列表 α) (n ns)
  证明: by
  simp [splitWrtCompositionAux]

Depends on / 依赖: splitWrtCompositionAux
-/
theorem splitWrtCompositionAux_cons (l : List α) (n ns) :
    l.splitWrtCompositionAux (n::ns) = take n l::(drop n l).splitWrtCompositionAux ns := by
  simp [splitWrtCompositionAux]

/--
theorem `length_splitWrtCompositionAux` / 定理 `length_splitWrtCompositionAux`

English:
theorem length_splitWrtCompositionAux
  given: (l : List α) (ns)
  proof: by
    induction ns generalizing l
    · simp [splitWrtCompositionAux, *]
    · simp [*]

中文:
定理 length_splitWrtCompositionAux
  条件: (l : 列表 α) (ns)
  证明: by
    induction ns generalizing l
    · simp [splitWrtCompositionAux, *]
    · simp [*]

Depends on / 依赖: generalizing, splitWrtCompositionAux
-/
theorem length_splitWrtCompositionAux (l : List α) (ns) :
    length (l.splitWrtCompositionAux ns) = ns.length := by
    induction ns generalizing l
    · simp [splitWrtCompositionAux, *]
    · simp [*]

/-- When one splits a list along a composition `c`, the number of sublists thus created is
`c.length`. -/
@[simp]
/--
theorem `length_splitWrtComposition` / 定理 `length_splitWrtComposition`

English:
theorem length_splitWrtComposition
  given: (l : List α) (c : Composition n)
  proof: length_splitWrtCompositionAux _ _

中文:
定理 length_splitWrtComposition
  条件: (l : 列表 α) (c : 余mposition n)
  证明: length_splitWrtCompositionAux _ _

Depends on / 依赖: length_splitWrtCompositionAux
-/
theorem length_splitWrtComposition (l : List α) (c : Composition n) :
    length (l.splitWrtComposition c) = c.length :=
  length_splitWrtCompositionAux _ _


/--
theorem `map_length_splitWrtCompositionAux` / 定理 `map_length_splitWrtCompositionAux`

English:
theorem map_length_splitWrtCompositionAux
  given: {ns : List Nat}
  proof: by
  induction ns with
  | nil => simp [splitWrtCompositionAux]
  | cons n ns IH => grind [splitWrtCompositionAux_cons]

中文:
定理 map_length_splitWrtCompositionAux
  条件: {ns : 列表 自然数}
  证明: by
  induction ns with
  | nil => simp [splitWrtCompositionAux]
  | cons n ns IH => grind [splitWrtCompositionAux_cons]

Depends on / 依赖: splitWrtCompositionAux, splitWrtCompositionAux_cons
-/
theorem map_length_splitWrtCompositionAux {ns : List Nat} :
    forall {l : List α}, ns.sum <= l.length -> map length (l.splitWrtCompositionAux ns) = ns := by
  induction ns with
  | nil => simp [splitWrtCompositionAux]
  | cons n ns IH => grind [splitWrtCompositionAux_cons]

/--
theorem `map_length_splitWrtComposition` / 定理 `map_length_splitWrtComposition`

English:
theorem map_length_splitWrtComposition
  given: (l : List α) (c : Composition l.length)
  proof: map_length_splitWrtCompositionAux (le_of_eq c.blocks_sum)

中文:
定理 map_length_splitWrtComposition
  条件: (l : 列表 α) (c : 余mposition l.length)
  证明: map_length_splitWrtCompositionAux (le_of_eq c.blocks_sum)

Depends on / 依赖: blocks_sum, c.blocks_sum, le_of_eq, map_length_splitWrtCompositionAux
-/
theorem map_length_splitWrtComposition (l : List α) (c : Composition l.length) :
    map length (l.splitWrtComposition c) = c.blocks :=
  map_length_splitWrtCompositionAux (le_of_eq c.blocks_sum)

/--
theorem `length_pos_of_mem_splitWrtComposition` / 定理 `length_pos_of_mem_splitWrtComposition`

English:
theorem length_pos_of_mem_splitWrtComposition
  statement: {l l' : List α} {c : Composition l.length}
  proof: by
  have : l'.length in (l.splitWrtComposition c).map List.length :=
    List.mem_map_of_mem h
  rw [map_length_splitWrtComposition] at this
  exact c.blocks_pos this

中文:
定理 length_pos_of_mem_splitWrtComposition
  结论: {l l' : 列表 α} {c : 余mposition l.length}
  证明: by
  have : l'.length in (l.splitWrtComposition c).map List.length :=
    List.mem_map_of_mem h
  rw [map_length_splitWrtComposition] at this
  exact c.blocks_pos this

Depends on / 依赖: List.length, List.mem_map_of_mem, blocks_pos, c.blocks_pos, l.splitWrtComposition, length, map_length_splitWrtComposition, mem_map_of_mem, splitWrtComposition
-/
theorem length_pos_of_mem_splitWrtComposition {l l' : List α} {c : Composition l.length}
    (h : l' in l.splitWrtComposition c) : 0 < length l' := by
  have : l'.length in (l.splitWrtComposition c).map List.length :=
    List.mem_map_of_mem h
  rw [map_length_splitWrtComposition] at this
  exact c.blocks_pos this

/--
theorem `sum_take_map_length_splitWrtComposition` / 定理 `sum_take_map_length_splitWrtComposition`

English:
theorem sum_take_map_length_splitWrtComposition
  given: (l : List α) (c : Composition l.length) (i : Nat)
  proof: by
  congr
  exact map_length_splitWrtComposition l c

中文:
定理 sum_take_map_length_splitWrtComposition
  条件: (l : 列表 α) (c : 余mposition l.length) (i : 自然数)
  证明: by
  congr
  exact map_length_splitWrtComposition l c

Depends on / 依赖: map_length_splitWrtComposition
-/
theorem sum_take_map_length_splitWrtComposition (l : List α) (c : Composition l.length) (i : Nat) :
    (((l.splitWrtComposition c).map length).take i).sum = c.sizeUpTo i := by
  congr
  exact map_length_splitWrtComposition l c

/--
theorem `getElem_splitWrtCompositionAux` / 定理 `getElem_splitWrtCompositionAux`

English:
theorem getElem_splitWrtCompositionAux
  statement: (l : List α) (ns : List Nat) {i : Nat}
  proof: by
  induction ns generalizing l i with
  | nil => cases hi
  | cons n ns IH =>
    rcases i with - | i
    · simp
    · simp only [splitWrtCompositionAux, getElem_cons_succ, IH, take,
          sum_cons, splitAt_eq, drop_take, drop_drop]
      rw [Nat.add_sub_add_left]

中文:
定理 getElem_splitWrtCompositionAux
  结论: (l : 列表 α) (ns : 列表 自然数) {i : 自然数}
  证明: by
  induction ns generalizing l i with
  | nil => cases hi
  | cons n ns IH =>
    rcases i with - | i
    · simp
    · simp only [splitWrtCompositionAux, getElem_cons_succ, IH, take,
          sum_cons, splitAt_eq, drop_take, drop_drop]
      rw [Nat.add_sub_add_left]

Depends on / 依赖: Nat.add_sub_add_left, add_sub_add_left, drop_drop, drop_take, generalizing, getElem_cons_succ, splitAt_eq, splitWrtCompositionAux, sum_cons
-/
theorem getElem_splitWrtCompositionAux (l : List α) (ns : List Nat) {i : Nat}
    (hi : i < (l.splitWrtCompositionAux ns).length) :
    (l.splitWrtCompositionAux ns)[i] =
      (l.take (ns.take (i + 1)).sum).drop (ns.take i).sum := by
  induction ns generalizing l i with
  | nil => cases hi
  | cons n ns IH =>
    rcases i with - | i
    · simp
    · simp only [splitWrtCompositionAux, getElem_cons_succ, IH, take,
          sum_cons, splitAt_eq, drop_take, drop_drop]
      rw [Nat.add_sub_add_left]

/--
theorem `getElem_splitWrtComposition'` / 定理 `getElem_splitWrtComposition'`

English:
theorem getElem_splitWrtComposition'
  statement: (l : List α) (c : Composition n) {i : Nat}
  proof: getElem_splitWrtCompositionAux _ _ hi

中文:
定理 getElem_splitWrtComposition'
  结论: (l : 列表 α) (c : 余mposition n) {i : 自然数}
  证明: getElem_splitWrtCompositionAux _ _ hi

Depends on / 依赖: getElem_splitWrtCompositionAux
-/
theorem getElem_splitWrtComposition' (l : List α) (c : Composition n) {i : Nat}
    (hi : i < (l.splitWrtComposition c).length) :
    (l.splitWrtComposition c)[i] = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  getElem_splitWrtCompositionAux _ _ hi

/--
theorem `getElem_splitWrtComposition` / 定理 `getElem_splitWrtComposition`

English:
theorem getElem_splitWrtComposition
  statement: (l : List α) (c : Composition n)
  proof: getElem_splitWrtComposition' _ _ h

中文:
定理 getElem_splitWrtComposition
  结论: (l : 列表 α) (c : 余mposition n)
  证明: getElem_splitWrtComposition' _ _ h

Depends on / 依赖: getElem_splitWrtComposition
-/
theorem getElem_splitWrtComposition (l : List α) (c : Composition n)
    (i : Nat) (h : i < (l.splitWrtComposition c).length) :
    (l.splitWrtComposition c)[i] = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  getElem_splitWrtComposition' _ _ h

/--
theorem `flatten_splitWrtCompositionAux` / 定理 `flatten_splitWrtCompositionAux`

English:
theorem flatten_splitWrtCompositionAux
  given: {ns : List Nat}
  proof: by
  induction ns with
  | nil => exact fun h => (length_eq_zero_iff.1 h.symm).symm
  | cons n ns IH =>
    intro l h; rw [sum_cons] at h
    simp only [splitWrtCompositionAux_cons]; dsimp
    rw [IH]
    · simp
    · rw [length_drop, ← h, add_tsub_cancel_left]

中文:
定理 flatten_splitWrtCompositionAux
  条件: {ns : 列表 自然数}
  证明: by
  induction ns with
  | nil => exact fun h => (length_eq_zero_iff.1 h.symm).symm
  | cons n ns IH =>
    intro l h; rw [sum_cons] at h
    simp only [splitWrtCompositionAux_cons]; dsimp
    rw [IH]
    · simp
    · rw [length_drop, ← h, add_tsub_cancel_left]

Depends on / 依赖: add_tsub_cancel_left, h.symm, length_drop, length_eq_zero_iff, splitWrtCompositionAux_cons, sum_cons
-/
theorem flatten_splitWrtCompositionAux {ns : List Nat} :
    forall {l : List α}, ns.sum = l.length -> (l.splitWrtCompositionAux ns).flatten = l := by
  induction ns with
  | nil => exact fun h => (length_eq_zero_iff.1 h.symm).symm
  | cons n ns IH =>
    intro l h; rw [sum_cons] at h
    simp only [splitWrtCompositionAux_cons]; dsimp
    rw [IH]
    · simp
    · rw [length_drop, ← h, add_tsub_cancel_left]

/-- If one splits a list along a composition, and then flattens the sublists, one gets back the
original list. -/
@[simp]
/--
theorem `flatten_splitWrtComposition` / 定理 `flatten_splitWrtComposition`

English:
theorem flatten_splitWrtComposition
  given: (l : List α) (c : Composition l.length)
  proof: flatten_splitWrtCompositionAux c.blocks_sum

中文:
定理 flatten_splitWrtComposition
  条件: (l : 列表 α) (c : 余mposition l.length)
  证明: flatten_splitWrtCompositionAux c.blocks_sum

Depends on / 依赖: blocks_sum, c.blocks_sum, flatten_splitWrtCompositionAux
-/
theorem flatten_splitWrtComposition (l : List α) (c : Composition l.length) :
    (l.splitWrtComposition c).flatten = l :=
  flatten_splitWrtCompositionAux c.blocks_sum

/-- If one joins a list of lists and then splits the flattening along the right composition,
one gets back the original list of lists. -/
@[simp]
/--
theorem `splitWrtComposition_flatten` / 定理 `splitWrtComposition_flatten`

English:
theorem splitWrtComposition_flatten
  statement: (L : List (List α)) (c : Composition L.flatten.length)
  proof: by
  simp only [and_self_iff, eq_iff_flatten_eq, flatten_splitWrtComposition,
    map_length_splitWrtComposition, h]

中文:
定理 splitWrtComposition_flatten
  结论: (L : 列表 (列表 α)) (c : 余mposition L.flatten.length)
  证明: by
  simp only [and_self_iff, eq_iff_flatten_eq, flatten_splitWrtComposition,
    map_length_splitWrtComposition, h]

Depends on / 依赖: CompHausLike, CompHausLike.LocallyConstant.adjunction, LocallyConstant, adjunction, and_self_iff, eq_iff_flatten_eq, flatten_splitWrtComposition, map_length_splitWrtComposition
-/
theorem splitWrtComposition_flatten (L : List (List α)) (c : Composition L.flatten.length)
    (h : map length L = c.blocks) : splitWrtComposition (flatten L) c = L := by
  simp only [and_self_iff, eq_iff_flatten_eq, flatten_splitWrtComposition,
    map_length_splitWrtComposition, h]

end List

/-!
### Compositions as sets

Combinatorial viewpoints on compositions, seen as finite subsets of `Fin (n+1)` containing `0` and
`n`, where the points of the set (other than `n`) correspond to the leftmost points of each block.
-/


set_option backward.isDefEq.respectTransparency false in
/--
Definition of `compositionAsSetEquiv` / `compositionAsSetEquiv` 的定义

English:
definition compositionAsSetEquiv
  signature: (n : Nat)
  body: { i : Fin (n - 1) |
        (⟨1 + (i : Nat), by lia⟩ : Fin n.succ) in c.boundaries }.toFinset
  invFun s :=
    { boundaries :=
        { i : Fin n.succ |
            i = 0 ∨ i = Fin.last n ∨ exists (j : Fin (n - 1)) (_hj : j in s), (i : Nat) = j + 1 }.toFinset
      zero_mem := by simp
      getLast_mem := by simp }
  left_inv := by
    intro c
    ext i
    simp only [add_comm, Set.toFinset_ofPred, Finset.mem_univ,
     Finset.mem_filter, true_and, exists_prop]
    constructor
    · rintro (rfl | rfl | ⟨j, hj1, hj2⟩)
      · exact c.zero_mem
      · exact c.getLast_mem
      · convert! hj1
    · simp only [or_iff_not_imp_left, ← ne_eq, ← Fin.exists_succ_eq]
      rintro i_mem ⟨j, rfl⟩ i_ne_last
      rcases Nat.exists_add_one_eq.mpr j.pos with ⟨n, rfl⟩
      obtain ⟨k, rfl⟩ : exists k : Fin n, k.castSucc = j := by
        simpa [Fin.exists_castSucc_eq] using! i_ne_last
      use k
      simpa using! i_mem
  right_inv := by
    intro s
    ext i
    have : (i : Nat) + 1 != n := by lia
    simp_rw [add_comm, Fin.ext_iff, Fin.val_zero, Fin.val_last, exists_prop, Set.toFinset_ofPred,
      Finset.mem_filter_univ, reduceCtorEq, this, false_or, add_left_inj, ← Fin.ext_iff,
      exists_eq_right']

中文:
定义 compositionAsSetEquiv
  签名: (n : 自然数)
  定义体: { i : Fin (n - 1) |
        (⟨1 + (i : Nat), by lia⟩ : Fin n.succ) in c.boundaries }.toFinset
  invFun s :=
    { boundaries :=
        { i : Fin n.succ |
            i = 0 ∨ i = Fin.last n ∨ exists (j : Fin (n - 1)) (_hj : j in s), (i : Nat) = j + 1 }.toFinset
      zero_mem := by simp
      getLast_mem := by simp }
  left_inv := by
    intro c
    ext i
    simp only [add_comm, Set.toFinset_ofPred, Finset.mem_univ,
     Finset.mem_filter, true_and, exists_prop]
    constructor
    · rintro (rfl | rfl | ⟨j, hj1, hj2⟩)
      · exact c.zero_mem
      · exact c.getLast_mem
      · convert! hj1
    · simp only [or_iff_not_imp_left, ← ne_eq, ← Fin.exists_succ_eq]
      rintro i_mem ⟨j, rfl⟩ i_ne_last
      rcases Nat.exists_add_one_eq.mpr j.pos with ⟨n, rfl⟩
      obtain ⟨k, rfl⟩ : exists k : Fin n, k.castSucc = j := by
        simpa [Fin.exists_castSucc_eq] using! i_ne_last
      use k
      simpa using! i_mem
  right_inv := by
    intro s
    ext i
    have : (i : Nat) + 1 != n := by lia
    simp_rw [add_comm, Fin.ext_iff, Fin.val_zero, Fin.val_last, exists_prop, Set.toFinset_ofPred,
      Finset.mem_filter_univ, reduceCtorEq, this, false_or, add_left_inj, ← Fin.ext_iff,
      exists_eq_right']

Depends on / 依赖: Fin.last, Finset, Finset.mem_filter, Finset.mem_univ, Set.toFinset_ofPred, add_comm, boundaries, c.boundaries, c.getLast_mem, c.zero_mem, exists_prop, getLast_mem, invFun, left_inv, mem_filter, mem_univ, n.succ, toFinset, toFinset_ofPred, true_and
-/
def compositionAsSetEquiv (n : Nat) : CompositionAsSet n ≃ Finset (Fin (n - 1)) where
  toFun c :=
    { i : Fin (n - 1) |
        (⟨1 + (i : Nat), by lia⟩ : Fin n.succ) in c.boundaries }.toFinset
  invFun s :=
    { boundaries :=
        { i : Fin n.succ |
            i = 0 ∨ i = Fin.last n ∨ exists (j : Fin (n - 1)) (_hj : j in s), (i : Nat) = j + 1 }.toFinset
      zero_mem := by simp
      getLast_mem := by simp }
  left_inv := by
    intro c
    ext i
    simp only [add_comm, Set.toFinset_ofPred, Finset.mem_univ,
     Finset.mem_filter, true_and, exists_prop]
    constructor
    · rintro (rfl | rfl | ⟨j, hj1, hj2⟩)
      · exact c.zero_mem
      · exact c.getLast_mem
      · convert! hj1
    · simp only [or_iff_not_imp_left, ← ne_eq, ← Fin.exists_succ_eq]
      rintro i_mem ⟨j, rfl⟩ i_ne_last
      rcases Nat.exists_add_one_eq.mpr j.pos with ⟨n, rfl⟩
      obtain ⟨k, rfl⟩ : exists k : Fin n, k.castSucc = j := by
        simpa [Fin.exists_castSucc_eq] using! i_ne_last
      use k
      simpa using! i_mem
  right_inv := by
    intro s
    ext i
    have : (i : Nat) + 1 != n := by lia
    simp_rw [add_comm, Fin.ext_iff, Fin.val_zero, Fin.val_last, exists_prop, Set.toFinset_ofPred,
      Finset.mem_filter_univ, reduceCtorEq, this, false_or, add_left_inj, ← Fin.ext_iff,
      exists_eq_right']

/--
Instance `compositionAsSetFintype` / 实例 `compositionAsSetFintype`

English:
instance compositionAsSetFintype
  signature: (n : Nat)
  body: Fintype.ofEquiv _ (compositionAsSetEquiv n).symm

中文:
实例 compositionAsSetFintype
  签名: (n : 自然数)
  定义体: Fintype.ofEquiv _ (compositionAsSetEquiv n).symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, compositionAsSetEquiv, ofEquiv
-/
instance compositionAsSetFintype (n : Nat) : Fintype (CompositionAsSet n) :=
  Fintype.ofEquiv _ (compositionAsSetEquiv n).symm

/--
theorem `compositionAsSet_card` / 定理 `compositionAsSet_card`

English:
theorem compositionAsSet_card
  given: (n : Nat)
  statement: Fintype.card (CompositionAsSet n) = 2 ^ (n - 1)
  proof: by
  have : Fintype.card (Finset (Fin (n - 1))) = 2 ^ (n - 1) := by simp
  rw [← this]
  exact Fintype.card_congr (compositionAsSetEquiv n)

中文:
定理 compositionAsSet_card
  条件: (n : 自然数)
  结论: 有限类型.card (余mpositionAsSet n) = 2 ^ (n - 1)
  证明: by
  have : Fintype.card (Finset (Fin (n - 1))) = 2 ^ (n - 1) := by simp
  rw [← this]
  exact Fintype.card_congr (compositionAsSetEquiv n)

Depends on / 依赖: Finset, Fintype, Fintype.card, Fintype.card_congr, card_congr, compositionAsSetEquiv
-/
theorem compositionAsSet_card (n : Nat) : Fintype.card (CompositionAsSet n) = 2 ^ (n - 1) := by
  have : Fintype.card (Finset (Fin (n - 1))) = 2 ^ (n - 1) := by simp
  rw [← this]
  exact Fintype.card_congr (compositionAsSetEquiv n)

namespace CompositionAsSet

variable (c : CompositionAsSet n)

/--
theorem `boundaries_nonempty` / 定理 `boundaries_nonempty`

English:
theorem boundaries_nonempty
  statement: c.boundaries.Nonempty
  proof: ⟨0, c.zero_mem⟩

中文:
定理 boundaries_nonempty
  结论: c.boundaries.非空
  证明: ⟨0, c.zero_mem⟩

Depends on / 依赖: c.zero_mem, zero_mem
-/
theorem boundaries_nonempty : c.boundaries.Nonempty :=
  ⟨0, c.zero_mem⟩

/--
theorem `card_boundaries_pos` / 定理 `card_boundaries_pos`

English:
theorem card_boundaries_pos
  statement: 0 < Finset.card c.boundaries
  proof: Finset.card_pos.mpr c.boundaries_nonempty

中文:
定理 card_boundaries_pos
  结论: 0 < 有限集.card c.boundaries
  证明: Finset.card_pos.mpr c.boundaries_nonempty

Depends on / 依赖: Finset, Finset.card_pos.mpr, boundaries_nonempty, c.boundaries_nonempty, card_pos
-/
theorem card_boundaries_pos : 0 < Finset.card c.boundaries :=
  Finset.card_pos.mpr c.boundaries_nonempty

/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: : Nat
  body: Finset.card c.boundaries - 1

中文:
定义 length
  签名: : 自然数
  定义体: Finset.card c.boundaries - 1

Depends on / 依赖: Finset, Finset.card, boundaries, c.boundaries
-/
def length : Nat :=
  Finset.card c.boundaries - 1

/--
theorem `card_boundaries_eq_succ_length` / 定理 `card_boundaries_eq_succ_length`

English:
theorem card_boundaries_eq_succ_length
  statement: c.boundaries.card = c.length + 1
  proof: (tsub_eq_iff_eq_add_of_le (Nat.succ_le_of_lt c.card_boundaries_pos)).mp rfl

中文:
定理 card_boundaries_eq_succ_length
  结论: c.boundaries.card = c.length + 1
  证明: (tsub_eq_iff_eq_add_of_le (Nat.succ_le_of_lt c.card_boundaries_pos)).mp rfl

Depends on / 依赖: Nat.succ_le_of_lt, c.card_boundaries_pos, card_boundaries_pos, succ_le_of_lt, tsub_eq_iff_eq_add_of_le
-/
theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 :=
  (tsub_eq_iff_eq_add_of_le (Nat.succ_le_of_lt c.card_boundaries_pos)).mp rfl

/--
theorem `length_lt_card_boundaries` / 定理 `length_lt_card_boundaries`

English:
theorem length_lt_card_boundaries
  statement: c.length < c.boundaries.card
  proof: by
  rw [c.card_boundaries_eq_succ_length]
  exact Nat.lt_add_one _

中文:
定理 length_lt_card_boundaries
  结论: c.length < c.boundaries.card
  证明: by
  rw [c.card_boundaries_eq_succ_length]
  exact Nat.lt_add_one _

Depends on / 依赖: Nat.lt_add_one, c.card_boundaries_eq_succ_length, card_boundaries_eq_succ_length, lt_add_one
-/
theorem length_lt_card_boundaries : c.length < c.boundaries.card := by
  rw [c.card_boundaries_eq_succ_length]
  exact Nat.lt_add_one _

/--
theorem `lt_length` / 定理 `lt_length`

English:
theorem lt_length
  given: (i : Fin c.length)
  statement: (i : Nat) + 1 < c.boundaries.card
  proof: lt_tsub_iff_right.mp i.2

中文:
定理 lt_length
  条件: (i : 有限集 c.length)
  结论: (i : 自然数) + 1 < c.boundaries.card
  证明: lt_tsub_iff_right.mp i.2

Depends on / 依赖: lt_tsub_iff_right, lt_tsub_iff_right.mp
-/
theorem lt_length (i : Fin c.length) : (i : Nat) + 1 < c.boundaries.card :=
  lt_tsub_iff_right.mp i.2

/--
theorem `lt_length'` / 定理 `lt_length'`

English:
theorem lt_length'
  given: (i : Fin c.length)
  statement: (i : Nat) < c.boundaries.card
  proof: lt_of_le_of_lt (Nat.le_succ i) (c.lt_length i)

中文:
定理 lt_length'
  条件: (i : 有限集 c.length)
  结论: (i : 自然数) < c.boundaries.card
  证明: lt_of_le_of_lt (Nat.le_succ i) (c.lt_length i)

Depends on / 依赖: Nat.le_succ, c.lt_length, le_succ, lt_length, lt_of_le_of_lt
-/
theorem lt_length' (i : Fin c.length) : (i : Nat) < c.boundaries.card :=
  lt_of_le_of_lt (Nat.le_succ i) (c.lt_length i)

/--
Definition of `boundary` / `boundary` 的定义

English:
definition boundary
  signature: : Fin c.boundaries.card ↪o Fin (n + 1)
  body: c.boundaries.orderEmbOfFin rfl

@[simp]

中文:
定义 boundary
  签名: : 有限集 c.boundaries.card ↪o 有限集 (n + 1)
  定义体: c.boundaries.orderEmbOfFin rfl

@[simp]

Depends on / 依赖: boundaries, c.boundaries.orderEmbOfFin, orderEmbOfFin
-/
def boundary : Fin c.boundaries.card ↪o Fin (n + 1) :=
  c.boundaries.orderEmbOfFin rfl

@[simp]
/--
theorem `boundary_zero` / 定理 `boundary_zero`

English:
theorem boundary_zero
  statement: (c.boundary ⟨0, c.card_boundaries_pos⟩ : Fin (n + 1)) = 0
  proof: by
  rw [boundary]; rw [Finset.orderEmbOfFin_zero rfl c.card_boundaries_pos]
  exact le_antisymm (Finset.min'_le _ _ c.zero_mem) (Fin.zero_le _)

@[simp]

中文:
定理 boundary_zero
  结论: (c.boundary ⟨0, c.card_boundaries_pos⟩ : 有限集 (n + 1)) = 0
  证明: by
  rw [boundary]; rw [Finset.orderEmbOfFin_zero rfl c.card_boundaries_pos]
  exact le_antisymm (Finset.min'_le _ _ c.zero_mem) (Fin.zero_le _)

@[simp]

Depends on / 依赖: Fin.zero_le, Finset, Finset.min, Finset.orderEmbOfFin_zero, boundary, c.card_boundaries_pos, c.zero_mem, card_boundaries_pos, le_antisymm, orderEmbOfFin_zero, zero_le, zero_mem
-/
theorem boundary_zero : (c.boundary ⟨0, c.card_boundaries_pos⟩ : Fin (n + 1)) = 0 := by
  rw [boundary]; rw [Finset.orderEmbOfFin_zero rfl c.card_boundaries_pos]
  exact le_antisymm (Finset.min'_le _ _ c.zero_mem) (Fin.zero_le _)

@[simp]
/--
theorem `boundary_length` / 定理 `boundary_length`

English:
theorem boundary_length
  statement: c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = Fin.last n
  proof: by
  convert! Finset.orderEmbOfFin_last rfl c.card_boundaries_pos
  exact le_antisymm (Finset.le_max' _ _ c.getLast_mem) (Fin.le_last _)

中文:
定理 boundary_length
  结论: c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = 有限集.last n
  证明: by
  convert! Finset.orderEmbOfFin_last rfl c.card_boundaries_pos
  exact le_antisymm (Finset.le_max' _ _ c.getLast_mem) (Fin.le_last _)

Depends on / 依赖: Fin.le_last, Finset, Finset.le_max, Finset.orderEmbOfFin_last, c.card_boundaries_pos, c.getLast_mem, card_boundaries_pos, convert, getLast_mem, le_antisymm, le_last, le_max, orderEmbOfFin_last
-/
theorem boundary_length : c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = Fin.last n := by
  convert! Finset.orderEmbOfFin_last rfl c.card_boundaries_pos
  exact le_antisymm (Finset.le_max' _ _ c.getLast_mem) (Fin.le_last _)

/--
Definition of `blocksFun` / `blocksFun` 的定义

English:
definition blocksFun
  signature: (i : Fin c.length)
  body: c.boundary ⟨(i : Nat) + 1, c.lt_length i⟩ - c.boundary ⟨i, c.lt_length' i⟩

中文:
定义 blocksFun
  签名: (i : 有限集 c.length)
  定义体: c.boundary ⟨(i : Nat) + 1, c.lt_length i⟩ - c.boundary ⟨i, c.lt_length' i⟩

Depends on / 依赖: boundary, c.boundary, c.lt_length, lt_length
-/
def blocksFun (i : Fin c.length) : Nat :=
  c.boundary ⟨(i : Nat) + 1, c.lt_length i⟩ - c.boundary ⟨i, c.lt_length' i⟩

/--
theorem `blocksFun_pos` / 定理 `blocksFun_pos`

English:
theorem blocksFun_pos
  given: (i : Fin c.length)
  statement: 0 < c.blocksFun i
  proof: haveI : (⟨i, c.lt_length' i⟩ : Fin c.boundaries.card) < ⟨i + 1, c.lt_length i⟩ :=
    Nat.lt_succ_self _
  lt_tsub_iff_left.mpr ((c.boundaries.orderEmbOfFin rfl).strictMono this)

中文:
定理 blocksFun_pos
  条件: (i : 有限集 c.length)
  结论: 0 < c.blocksFun i
  证明: haveI : (⟨i, c.lt_length' i⟩ : Fin c.boundaries.card) < ⟨i + 1, c.lt_length i⟩ :=
    Nat.lt_succ_self _
  lt_tsub_iff_left.mpr ((c.boundaries.orderEmbOfFin rfl).strictMono this)

Depends on / 依赖: Nat.lt_succ_self, boundaries, c.boundaries.card, c.boundaries.orderEmbOfFin, c.lt_length, lt_length, lt_succ_self, lt_tsub_iff_left, lt_tsub_iff_left.mpr, orderEmbOfFin, strictMono
-/
theorem blocksFun_pos (i : Fin c.length) : 0 < c.blocksFun i :=
  haveI : (⟨i, c.lt_length' i⟩ : Fin c.boundaries.card) < ⟨i + 1, c.lt_length i⟩ :=
    Nat.lt_succ_self _
  lt_tsub_iff_left.mpr ((c.boundaries.orderEmbOfFin rfl).strictMono this)

/--
Definition of `blocks` / `blocks` 的定义

English:
definition blocks
  signature: (c : CompositionAsSet n)
  body: ofFn c.blocksFun

@[simp]

中文:
定义 blocks
  签名: (c : 余mpositionAsSet n)
  定义体: ofFn c.blocksFun

@[simp]

Depends on / 依赖: blocksFun, c.blocksFun
-/
def blocks (c : CompositionAsSet n) : List Nat :=
  ofFn c.blocksFun

@[simp]
/--
theorem `blocks_length` / 定理 `blocks_length`

English:
theorem blocks_length
  statement: c.blocks.length = c.length
  proof: length_ofFn

中文:
定理 blocks_length
  结论: c.blocks.length = c.length
  证明: length_ofFn

Depends on / 依赖: length_ofFn
-/
theorem blocks_length : c.blocks.length = c.length :=
  length_ofFn

set_option backward.isDefEq.respectTransparency false in
/--
theorem `blocks_partial_sum` / 定理 `blocks_partial_sum`

English:
theorem blocks_partial_sum
  given: {i : Nat} (h : i < c.boundaries.card)
  proof: by
  induction i with
  | zero => simp
  | succ i IH =>
    have A : i < c.blocks.length := by
      rw [c.card_boundaries_eq_succ_length] at h
      simp [blocks, Nat.lt_of_succ_lt_succ h]
    have B : i < c.boundaries.card := lt_of_lt_of_le A (by simp [blocks, length])
    rw [sum_take_succ _ _ A]; rw [IH B]
    simp [blocks, blocksFun]

中文:
定理 blocks_partial_sum
  条件: {i : 自然数} (h : i < c.boundaries.card)
  证明: by
  induction i with
  | zero => simp
  | succ i IH =>
    have A : i < c.blocks.length := by
      rw [c.card_boundaries_eq_succ_length] at h
      simp [blocks, Nat.lt_of_succ_lt_succ h]
    have B : i < c.boundaries.card := lt_of_lt_of_le A (by simp [blocks, length])
    rw [sum_take_succ _ _ A]; rw [IH B]
    simp [blocks, blocksFun]

Depends on / 依赖: Nat.lt_of_succ_lt_succ, blocks, blocksFun, boundaries, c.blocks.length, c.boundaries.card, c.card_boundaries_eq_succ_length, card_boundaries_eq_succ_length, length, lt_of_lt_of_le, lt_of_succ_lt_succ, sum_take_succ
-/
theorem blocks_partial_sum {i : Nat} (h : i < c.boundaries.card) :
    (c.blocks.take i).sum = c.boundary ⟨i, h⟩ := by
  induction i with
  | zero => simp
  | succ i IH =>
    have A : i < c.blocks.length := by
      rw [c.card_boundaries_eq_succ_length] at h
      simp [blocks, Nat.lt_of_succ_lt_succ h]
    have B : i < c.boundaries.card := lt_of_lt_of_le A (by simp [blocks, length])
    rw [sum_take_succ _ _ A]; rw [IH B]
    simp [blocks, blocksFun]

/--
theorem `mem_boundaries_iff_exists_blocks_sum_take_eq` / 定理 `mem_boundaries_iff_exists_blocks_sum_take_eq`

English:
theorem mem_boundaries_iff_exists_blocks_sum_take_eq
  given: {j : Fin (n + 1)}
  proof: by
  constructor
  · intro hj
    rcases (c.boundaries.orderIsoOfFin rfl).surjective ⟨j, hj⟩ with ⟨i, hi⟩
    rw [Subtype.ext_iff]; rw [Subtype.coe_mk] at hi
    refine ⟨i.1, i.2, ?_⟩
    dsimp at hi
    rw [← hi]; rw [c.blocks_partial_sum i.2]
    rfl
  · rintro ⟨i, hi, H⟩
    convert! (c.boundaries.orderIsoOfFin rfl ⟨i, hi⟩).2
    have : c.boundary ⟨i, hi⟩ = j := by rwa [Fin.ext_iff, ← c.blocks_partial_sum hi]
    exact this.symm

中文:
定理 mem_boundaries_iff_存在_blocks_sum_take_eq
  条件: {j : 有限集 (n + 1)}
  证明: by
  constructor
  · intro hj
    rcases (c.boundaries.orderIsoOfFin rfl).surjective ⟨j, hj⟩ with ⟨i, hi⟩
    rw [Subtype.ext_iff]; rw [Subtype.coe_mk] at hi
    refine ⟨i.1, i.2, ?_⟩
    dsimp at hi
    rw [← hi]; rw [c.blocks_partial_sum i.2]
    rfl
  · rintro ⟨i, hi, H⟩
    convert! (c.boundaries.orderIsoOfFin rfl ⟨i, hi⟩).2
    have : c.boundary ⟨i, hi⟩ = j := by rwa [Fin.ext_iff, ← c.blocks_partial_sum hi]
    exact this.symm

Depends on / 依赖: Fin.ext_iff, Subtype, Subtype.coe_mk, Subtype.ext_iff, blocks_partial_sum, boundaries, boundary, c.blocks_partial_sum, c.boundaries.orderIsoOfFin, c.boundary, coe_mk, convert, ext_iff, orderIsoOfFin, surjective, this.symm
-/
theorem mem_boundaries_iff_exists_blocks_sum_take_eq {j : Fin (n + 1)} :
    j in c.boundaries ↔ exists i < c.boundaries.card, (c.blocks.take i).sum = j := by
  constructor
  · intro hj
    rcases (c.boundaries.orderIsoOfFin rfl).surjective ⟨j, hj⟩ with ⟨i, hi⟩
    rw [Subtype.ext_iff]; rw [Subtype.coe_mk] at hi
    refine ⟨i.1, i.2, ?_⟩
    dsimp at hi
    rw [← hi]; rw [c.blocks_partial_sum i.2]
    rfl
  · rintro ⟨i, hi, H⟩
    convert! (c.boundaries.orderIsoOfFin rfl ⟨i, hi⟩).2
    have : c.boundary ⟨i, hi⟩ = j := by rwa [Fin.ext_iff, ← c.blocks_partial_sum hi]
    exact this.symm

/--
theorem `blocks_sum` / 定理 `blocks_sum`

English:
theorem blocks_sum
  statement: c.blocks.sum = n
  proof: by
  have : c.blocks.take c.length = c.blocks := take_of_length_le (by simp [blocks])
  rw [← this]; rw [c.blocks_partial_sum c.length_lt_card_boundaries]; rw [c.boundary_length]
  rfl

中文:
定理 blocks_sum
  结论: c.blocks.求和 = n
  证明: by
  have : c.blocks.take c.length = c.blocks := take_of_length_le (by simp [blocks])
  rw [← this]; rw [c.blocks_partial_sum c.length_lt_card_boundaries]; rw [c.boundary_length]
  rfl

Depends on / 依赖: blocks, blocks_partial_sum, boundary_length, c.blocks, c.blocks.take, c.blocks_partial_sum, c.boundary_length, c.length, c.length_lt_card_boundaries, length, length_lt_card_boundaries, take_of_length_le
-/
theorem blocks_sum : c.blocks.sum = n := by
  have : c.blocks.take c.length = c.blocks := take_of_length_le (by simp [blocks])
  rw [← this]; rw [c.blocks_partial_sum c.length_lt_card_boundaries]; rw [c.boundary_length]
  rfl

/--
Definition of `toComposition` / `toComposition` 的定义

English:
definition toComposition
  signature: : Composition n where
  body: c.blocks
  blocks_pos := by simp only [blocks, forall_mem_ofFn_iff, blocksFun_pos c, forall_true_iff]
  blocks_sum := c.blocks_sum

中文:
定义 toComposition
  签名: : 余mposition n where
  定义体: c.blocks
  blocks_pos := by simp only [blocks, forall_mem_ofFn_iff, blocksFun_pos c, forall_true_iff]
  blocks_sum := c.blocks_sum

Depends on / 依赖: blocks, c.blocks
-/
def toComposition : Composition n where
  blocks := c.blocks
  blocks_pos := by simp only [blocks, forall_mem_ofFn_iff, blocksFun_pos c, forall_true_iff]
  blocks_sum := c.blocks_sum

end CompositionAsSet

/-!
### Equivalence between compositions and compositions as sets

In this section, we explain how to go back and forth between a `Composition` and a
`CompositionAsSet`, by showing that their `blocks` and `length` and `boundaries` correspond to
each other, and construct an equivalence between them called `compositionEquiv`.
-/


@[simp]
/--
theorem `Composition.toCompositionAsSet_length` / 定理 `Composition.toCompositionAsSet_length`

English:
theorem Composition.toCompositionAsSet_length
  given: (c : Composition n)
  proof: by
  simp [Composition.toCompositionAsSet, CompositionAsSet.length, c.card_boundaries_eq_succ_length]

@[simp]

中文:
定理 余mposition.toCompositionAsSet_length
  条件: (c : 余mposition n)
  证明: by
  simp [Composition.toCompositionAsSet, CompositionAsSet.length, c.card_boundaries_eq_succ_length]

@[simp]

Depends on / 依赖: Composition, Composition.toCompositionAsSet, CompositionAsSet, CompositionAsSet.length, c.card_boundaries_eq_succ_length, card_boundaries_eq_succ_length, length, toCompositionAsSet
-/
theorem Composition.toCompositionAsSet_length (c : Composition n) :
    c.toCompositionAsSet.length = c.length := by
  simp [Composition.toCompositionAsSet, CompositionAsSet.length, c.card_boundaries_eq_succ_length]

@[simp]
/--
theorem `CompositionAsSet.toComposition_length` / 定理 `CompositionAsSet.toComposition_length`

English:
theorem CompositionAsSet.toComposition_length
  given: (c : CompositionAsSet n)
  proof: by
  simp [CompositionAsSet.toComposition, Composition.length]

@[simp]

中文:
定理 余mpositionAsSet.toComposition_length
  条件: (c : 余mpositionAsSet n)
  证明: by
  simp [CompositionAsSet.toComposition, Composition.length]

@[simp]

Depends on / 依赖: Composition, Composition.length, CompositionAsSet, CompositionAsSet.toComposition, length, toComposition
-/
theorem CompositionAsSet.toComposition_length (c : CompositionAsSet n) :
    c.toComposition.length = c.length := by
  simp [CompositionAsSet.toComposition, Composition.length]

@[simp]
/--
theorem `Composition.toCompositionAsSet_blocks` / 定理 `Composition.toCompositionAsSet_blocks`

English:
theorem Composition.toCompositionAsSet_blocks
  given: (c : Composition n)
  proof: by
  let d := c.toCompositionAsSet
  change d.blocks = c.blocks
  have length_eq : d.blocks.length = c.blocks.length := by simp [d, blocks_length]
  suffices H : forall i <= d.blocks.length, (d.blocks.take i).sum = (c.blocks.take i).sum from
    eq_of_sum_take_eq length_eq H
  intro i hi
  have i_lt : i < d.boundaries.card := by
    simpa [CompositionAsSet.blocks, length_ofFn,
      d.card_boundaries_eq_succ_length] using Nat.lt_succ_iff.2 hi
  have i_lt' : i < c.boundaries.card := i_lt
  have i_lt'' : i < c.length + 1 := by rwa [c.card_boundaries_eq_succ_length] at i_lt'
  have A :
    d.boundaries.orderEmbOfFin rfl ⟨i, i_lt⟩ =
      c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length ⟨i, i_lt''⟩ :=
    rfl
  have B : c.sizeUpTo i = c.boundary ⟨i, i_lt''⟩ := rfl
  rw [d.blocks_partial_sum i_lt]; rw [CompositionAsSet.boundary]; rw [← Composition.sizeUpTo]; rw [B]; rw [A]; rw [c.orderEmbOfFin_boundaries]

@[simp]

中文:
定理 余mposition.toCompositionAsSet_blocks
  条件: (c : 余mposition n)
  证明: by
  let d := c.toCompositionAsSet
  change d.blocks = c.blocks
  have length_eq : d.blocks.length = c.blocks.length := by simp [d, blocks_length]
  suffices H : forall i <= d.blocks.length, (d.blocks.take i).sum = (c.blocks.take i).sum from
    eq_of_sum_take_eq length_eq H
  intro i hi
  have i_lt : i < d.boundaries.card := by
    simpa [CompositionAsSet.blocks, length_ofFn,
      d.card_boundaries_eq_succ_length] using Nat.lt_succ_iff.2 hi
  have i_lt' : i < c.boundaries.card := i_lt
  have i_lt'' : i < c.length + 1 := by rwa [c.card_boundaries_eq_succ_length] at i_lt'
  have A :
    d.boundaries.orderEmbOfFin rfl ⟨i, i_lt⟩ =
      c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length ⟨i, i_lt''⟩ :=
    rfl
  have B : c.sizeUpTo i = c.boundary ⟨i, i_lt''⟩ := rfl
  rw [d.blocks_partial_sum i_lt]; rw [CompositionAsSet.boundary]; rw [← Composition.sizeUpTo]; rw [B]; rw [A]; rw [c.orderEmbOfFin_boundaries]

@[simp]

Depends on / 依赖: CompositionAsSet, CompositionAsSet.blocks, Countable, Countable.toSmall, Discrete, Discrete.equivalence, Finite, Nat.lt_succ_iff, blocks, blocks_length, boundaries, c.blocks, c.blocks.length, c.blocks.take, c.boundaries.card, c.length, c.toCompositionAsSet, card_boundaries_eq_succ_length, choose_spec, d.blocks
-/
theorem Composition.toCompositionAsSet_blocks (c : Composition n) :
    c.toCompositionAsSet.blocks = c.blocks := by
  let d := c.toCompositionAsSet
  change d.blocks = c.blocks
  have length_eq : d.blocks.length = c.blocks.length := by simp [d, blocks_length]
  suffices H : forall i <= d.blocks.length, (d.blocks.take i).sum = (c.blocks.take i).sum from
    eq_of_sum_take_eq length_eq H
  intro i hi
  have i_lt : i < d.boundaries.card := by
    simpa [CompositionAsSet.blocks, length_ofFn,
      d.card_boundaries_eq_succ_length] using Nat.lt_succ_iff.2 hi
  have i_lt' : i < c.boundaries.card := i_lt
  have i_lt'' : i < c.length + 1 := by rwa [c.card_boundaries_eq_succ_length] at i_lt'
  have A :
    d.boundaries.orderEmbOfFin rfl ⟨i, i_lt⟩ =
      c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length ⟨i, i_lt''⟩ :=
    rfl
  have B : c.sizeUpTo i = c.boundary ⟨i, i_lt''⟩ := rfl
  rw [d.blocks_partial_sum i_lt]; rw [CompositionAsSet.boundary]; rw [← Composition.sizeUpTo]; rw [B]; rw [A]; rw [c.orderEmbOfFin_boundaries]

@[simp]
/--
theorem `CompositionAsSet.toComposition_blocks` / 定理 `CompositionAsSet.toComposition_blocks`

English:
theorem CompositionAsSet.toComposition_blocks
  given: (c : CompositionAsSet n)
  proof: rfl

@[simp]

中文:
定理 余mpositionAsSet.toComposition_blocks
  条件: (c : 余mpositionAsSet n)
  证明: rfl

@[simp]
-/
theorem CompositionAsSet.toComposition_blocks (c : CompositionAsSet n) :
    c.toComposition.blocks = c.blocks :=
  rfl

@[simp]
/--
theorem `CompositionAsSet.toComposition_boundaries` / 定理 `CompositionAsSet.toComposition_boundaries`

English:
theorem CompositionAsSet.toComposition_boundaries
  given: (c : CompositionAsSet n)
  proof: by
  ext ⟨j, hj⟩
  simp [c.mem_boundaries_iff_exists_blocks_sum_take_eq, Composition.boundaries,
    c.card_boundaries_eq_succ_length, Composition.boundary, Composition.sizeUpTo, Fin.exists_iff]

@[simp]

中文:
定理 余mpositionAsSet.toComposition_boundaries
  条件: (c : 余mpositionAsSet n)
  证明: by
  ext ⟨j, hj⟩
  simp [c.mem_boundaries_iff_exists_blocks_sum_take_eq, Composition.boundaries,
    c.card_boundaries_eq_succ_length, Composition.boundary, Composition.sizeUpTo, Fin.exists_iff]

@[simp]

Depends on / 依赖: Composition, Composition.boundaries, Composition.boundary, Composition.sizeUpTo, Fin.exists_iff, boundaries, boundary, c.card_boundaries_eq_succ_length, c.mem_boundaries_iff_exists_blocks_sum_take_eq, card_boundaries_eq_succ_length, exists_iff, mem_boundaries_iff_exists_blocks_sum_take_eq, sizeUpTo
-/
theorem CompositionAsSet.toComposition_boundaries (c : CompositionAsSet n) :
    c.toComposition.boundaries = c.boundaries := by
  ext ⟨j, hj⟩
  simp [c.mem_boundaries_iff_exists_blocks_sum_take_eq, Composition.boundaries,
    c.card_boundaries_eq_succ_length, Composition.boundary, Composition.sizeUpTo, Fin.exists_iff]

@[simp]
/--
theorem `Composition.toCompositionAsSet_boundaries` / 定理 `Composition.toCompositionAsSet_boundaries`

English:
theorem Composition.toCompositionAsSet_boundaries
  given: (c : Composition n)
  proof: rfl

中文:
定理 余mposition.toCompositionAsSet_boundaries
  条件: (c : 余mposition n)
  证明: rfl
-/
theorem Composition.toCompositionAsSet_boundaries (c : Composition n) :
    c.toCompositionAsSet.boundaries = c.boundaries :=
  rfl

/--
Definition of `compositionEquiv` / `compositionEquiv` 的定义

English:
definition compositionEquiv
  signature: (n : Nat)
  body: c.toCompositionAsSet
  invFun c := c.toComposition
  left_inv c := by
    ext1
    exact c.toCompositionAsSet_blocks
  right_inv c := by
    ext1
    exact c.toComposition_boundaries

中文:
定义 compositionEquiv
  签名: (n : 自然数)
  定义体: c.toCompositionAsSet
  invFun c := c.toComposition
  left_inv c := by
    ext1
    exact c.toCompositionAsSet_blocks
  right_inv c := by
    ext1
    exact c.toComposition_boundaries

Depends on / 依赖: c.toCompositionAsSet, toCompositionAsSet
-/
def compositionEquiv (n : Nat) : Composition n ≃ CompositionAsSet n where
  toFun c := c.toCompositionAsSet
  invFun c := c.toComposition
  left_inv c := by
    ext1
    exact c.toCompositionAsSet_blocks
  right_inv c := by
    ext1
    exact c.toComposition_boundaries

/--
Instance `compositionFintype` / 实例 `compositionFintype`

English:
instance compositionFintype
  signature: (n : Nat)
  body: Fintype.ofEquiv _ (compositionEquiv n).symm

中文:
实例 compositionFintype
  签名: (n : 自然数)
  定义体: Fintype.ofEquiv _ (compositionEquiv n).symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, compositionEquiv, ofEquiv
-/
instance compositionFintype (n : Nat) : Fintype (Composition n) :=
  Fintype.ofEquiv _ (compositionEquiv n).symm

/--
theorem `composition_card` / 定理 `composition_card`

English:
theorem composition_card
  given: (n : Nat)
  statement: Fintype.card (Composition n) = 2 ^ (n - 1)
  proof: by
  rw [← compositionAsSet_card n]
  exact Fintype.card_congr (compositionEquiv n)

中文:
定理 composition_card
  条件: (n : 自然数)
  结论: 有限类型.card (余mposition n) = 2 ^ (n - 1)
  证明: by
  rw [← compositionAsSet_card n]
  exact Fintype.card_congr (compositionEquiv n)

Depends on / 依赖: Fintype, Fintype.card_congr, card_congr, compositionAsSet_card, compositionEquiv
-/
theorem composition_card (n : Nat) : Fintype.card (Composition n) = 2 ^ (n - 1) := by
  rw [← compositionAsSet_card n]
  exact Fintype.card_congr (compositionEquiv n)
