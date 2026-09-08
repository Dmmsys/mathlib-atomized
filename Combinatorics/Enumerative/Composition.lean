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

variable {n : ℕ}

/-- A composition of `n` is a list of positive integers summing to `n`. -/
@[ext]
/-
**Composition** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ℕ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A composition of `n` is a list of positive integers summing to `n`.
-/
structure Composition (n : ℕ) where
  /-- List of positive integers summing to `n` -/
  blocks : List ℕ
  /-- Proof of positivity for `blocks` -/
  blocks_pos : ∀ {i}, i ∈ blocks → 0 < i
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
/-
**CompositionAsSet** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ℕ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Combinatorial viewpoint on a composition of `n`, by seeing it as non-empty block
s of
consecutive integers in `{0, ..., n-1}`. We register every block by its left end
-point, yielding
a finset containing `0`. As this does not make sense for `n = 0`, we add `n` to 
this finset, and
get a finset of `{0, ..., n}` containing `0` and `n`. This is the data in the st
ructure
`CompositionAsSet n`.
-/
structure CompositionAsSet (n : ℕ) where
  /-- Combinatorial viewpoint on a composition of `n` as consecutive integers `{0, ..., n-1}` -/
  boundaries : Finset (Fin n.succ)
  /-- Proof that `0` is a member of `boundaries` -/
  zero_mem : (0 : Fin n.succ) ∈ boundaries
  /-- Last element of the composition -/
  getLast_mem : Fin.last n ∈ boundaries
  deriving DecidableEq
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} : Inhabited (CompositionAsSet n) :=
  ⟨⟨Finset.univ, Finset.mem_univ _, Finset.mem_univ _⟩⟩

attribute [simp] CompositionAsSet.zero_mem CompositionAsSet.getLast_mem

/-!
### Compositions

A composition of an integer `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum of
positive integers.
-/

namespace Composition

variable (c : Composition n)

/-
**Composition.** 是 Mathlib 中的一个实例，位于命名空间 `Composition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℕ) : ToString (Composition n) :=
  ⟨fun c => toString c.blocks⟩

/-- The length of a composition, i.e., the number of blocks in the composition. -/
/-
**Composition.length** 是 Mathlib 中的一个缩写定义，位于命名空间 `Composition`。
形式化陈述：length : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of a composition, i.e., the number of blocks in the composition.
-/
abbrev length : ℕ :=
  c.blocks.length
/-
**Composition.blocks_length** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：blocks_length : c.blocks.length = c.length
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem blocks_length : c.blocks.length = c.length :=
  rfl

/-- The blocks of a composition, seen as a function on `Fin c.length`. When composing analytic
functions using compositions, this is the main player. -/
/-
**Composition.blocksFun** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：blocksFun : Fin c.length -> Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The blocks of a composition, seen as a function on `Fin c.length`. When composin
g analytic
functions using compositions, this is the main player.
-/
def blocksFun : Fin c.length → ℕ := c.blocks.get

@[simp]
/-
**Composition.ofFn_blocksFun** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：ofFn_blocksFun : ofFn c.blocksFun = c.blocks
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ofFn_get`：∀ {α : Type u} (l : List α), List.ofFn l.get = l
-/
theorem ofFn_blocksFun : ofFn c.blocksFun = c.blocks :=
  ofFn_get _

@[simp]
/-
**Composition.sum_blocksFun** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sum_blocksFun : ∑ i, c.blocksFun i = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
· 使用定理 `Composition.ofFn_blocksFun`：ofFn_blocksFun : ofFn c.blocksFun = c.blocks
· 使用定理 `List.sum_ofFn`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ} {f : Fi
n n → M}, (List.ofFn f).sum = ∑ i, f i
-/
theorem sum_blocksFun : ∑ i, c.blocksFun i = n := by
  conv_rhs => rw [← c.blocks_sum, ← ofFn_blocksFun, sum_ofFn]

@[simp]
/-
**Composition.blocksFun_mem_blocks** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：blocksFun_mem_blocks (i : Fin c.length) : c.blocksFun i in c.blocks
参数：i : Fin c.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
-/
theorem blocksFun_mem_blocks (i : Fin c.length) : c.blocksFun i ∈ c.blocks :=
  get_mem _ _
/-
**Composition.one_le_blocks** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：one_le_blocks {i : Nat} (h : i in c.blocks) : 1 <= i
参数：h : i in c.blocks。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.blocks_pos`：∀ {n : ℕ} (self : Composition n) {i : ℕ}, i ∈ se
lf.blocks → 0 < i
-/
theorem one_le_blocks {i : ℕ} (h : i ∈ c.blocks) : 1 ≤ i :=
  c.blocks_pos h
/-
**Composition.blocks_le** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：blocks_le {i : Nat} (h : i in c.blocks) : i <= n
参数：h : i in c.blocks。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
· 使用定理 `List.le_sum_of_mem`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Preo
rder M] [CanonicallyOrderedAdd M] {xs : List M} {x : M},   x ∈ xs → x ≤ xs.sum
-/
theorem blocks_le {i : ℕ} (h : i ∈ c.blocks) : i ≤ n := by
  rw [← c.blocks_sum]
  exact List.le_sum_of_mem h

@[simp]
/-
**Composition.one_le_blocks'** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：one_le_blocks' {i : Nat} (h : i < c.length) : 1 <= c.blocks[i]
参数：h : i < c.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.one_le_blocks`：one_le_blocks {i : Nat} (h : i in c.blocks) :
 1 <= i
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
-/
theorem one_le_blocks' {i : ℕ} (h : i < c.length) : 1 ≤ c.blocks[i] :=
  c.one_le_blocks (get_mem (blocks c) _)

@[simp]
/-
**Composition.blocks_pos'** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：blocks_pos' (i : Nat) (h : i < c.length) : 0 < c.blocks[i]
参数：i : Nat；h : i < c.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.one_le_blocks'`：one_le_blocks' {i : Nat} (h : i < c.length) 
: 1 <= c.blocks[i]
-/
theorem blocks_pos' (i : ℕ) (h : i < c.length) : 0 < c.blocks[i] :=
  c.one_le_blocks' h

@[simp]
/-
**Composition.one_le_blocksFun** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：one_le_blocksFun (i : Fin c.length) : 1 <= c.blocksFun i
参数：i : Fin c.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.one_le_blocks`：one_le_blocks {i : Nat} (h : i in c.blocks) :
 1 <= i
· 使用定理 `Composition.blocksFun_mem_blocks`：blocksFun_mem_blocks (i : Fin c.length
) : c.blocksFun i in c.blocks
-/
theorem one_le_blocksFun (i : Fin c.length) : 1 ≤ c.blocksFun i :=
  c.one_le_blocks (c.blocksFun_mem_blocks i)

@[simp]
/-
**Composition.blocksFun_le** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：blocksFun_le {n} (c : Composition n) (i : Fin c.length) : c.blocksFun i <=
 n
参数：c : Composition n；i : Fin c.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.blocks_le`：blocks_le {i : Nat} (h : i in c.blocks) : i <= n
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem blocksFun_le {n} (c : Composition n) (i : Fin c.length) :
    c.blocksFun i ≤ n :=
  c.blocks_le <| getElem_mem _

@[simp]
/-
**Composition.length_le** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：length_le : c.length <= n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
· 使用定理 `List.length_le_sum_of_one_le`：length_le_sum_of_one_le (L : List Nat) (h 
: forall i in L, 1 <= i) : L.length <= L.sum
· 使用定理 `Composition.one_le_blocks`：one_le_blocks {i : Nat} (h : i in c.blocks) :
 1 <= i
-/
theorem length_le : c.length ≤ n := by
  conv_rhs => rw [← c.blocks_sum]
  exact length_le_sum_of_one_le _ fun i hi => c.one_le_blocks hi

@[simp]
/-
**Composition.blocks_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：blocks_eq_nil : c.blocks = [] ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_eq_zero_iff`：∀ {α : Type u_1} {l : List α}, l.length = 0 ↔ l
 = []
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Composition.length_le`：length_le : c.length <= n
-/
theorem blocks_eq_nil : c.blocks = [] ↔ n = 0 := by
  constructor
  · intro h
    simpa using congr(List.sum $h)
  · rintro rfl
    rw [← length_eq_zero_iff, ← nonpos_iff_eq_zero]
    exact c.length_le
/-
**Composition.length_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：∀ {n : ℕ} (c : Composition n), c.length = 0 ↔ n = 0
参数：c : Composition n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem length_eq_zero : c.length = 0 ↔ n = 0 := by
  simp

@[simp]
/-
**Composition.length_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：length_pos_iff : 0 < c.length ↔ 0 < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem length_pos_iff : 0 < c.length ↔ 0 < n := by
  simp [pos_iff_ne_zero]

alias ⟨_, length_pos_of_pos⟩ := length_pos_iff

/-- The sum of the sizes of the blocks in a composition up to `i`. -/
/-
**Composition.sizeUpTo** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：sizeUpTo (i : Nat) : Nat
参数：i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The sum of the sizes of the blocks in a composition up to `i`.
-/
def sizeUpTo (i : ℕ) : ℕ :=
  (c.blocks.take i).sum

@[simp]
/-
**Composition.sizeUpTo_zero** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sizeUpTo_zero : c.sizeUpTo 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sizeUpTo_zero : c.sizeUpTo 0 = 0 := by simp [sizeUpTo]
/-
**Composition.sizeUpTo_ofLength_le** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sizeUpTo_ofLength_le (i : Nat) (h : c.length <= i) : c.sizeUpTo i = n
参数：i : Nat；h : c.length <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
-/
theorem sizeUpTo_ofLength_le (i : ℕ) (h : c.length ≤ i) : c.sizeUpTo i = n := by
  dsimp [sizeUpTo]
  convert! c.blocks_sum
  exact take_of_length_le h

@[simp]
/-
**Composition.sizeUpTo_length** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sizeUpTo_length : c.sizeUpTo c.length = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.sizeUpTo_ofLength_le`：sizeUpTo_ofLength_le (i : Nat) (h : c.
length <= i) : c.sizeUpTo i = n
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem sizeUpTo_length : c.sizeUpTo c.length = n :=
  c.sizeUpTo_ofLength_le c.length le_rfl
/-
**Composition.sizeUpTo_le** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sizeUpTo_le (i : Nat) : c.sizeUpTo i <= n
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
· 使用定理 `List.sum_take_add_sum_drop`：∀ {M : Type u_4} [inst : AddMonoid M] (L : L
ist M) (i : ℕ), (List.take i L).sum + (List.drop i L).sum = L.sum
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem sizeUpTo_le (i : ℕ) : c.sizeUpTo i ≤ n := by
  conv_rhs => rw [← c.blocks_sum, ← sum_take_add_sum_drop _ i]
  exact Nat.le_add_right _ _
/-
**Composition.sizeUpTo_succ** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sizeUpTo_succ {i : Nat} (h : i < c.length) : c.sizeUpTo (i + 1) = c.sizeUp
To i + c.blocks[i]
参数：h : i < c.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sum_take_succ`：∀ {M : Type u_4} [inst : AddMonoid M] (L : List M) (
i : ℕ) (p : i < L.length),   (List.take (i + 1) L).sum = (List.take i L).sum + L
[i]
-/
theorem sizeUpTo_succ {i : ℕ} (h : i < c.length) :
    c.sizeUpTo (i + 1) = c.sizeUpTo i + c.blocks[i] := by
  simp only [sizeUpTo]
  rw [sum_take_succ _ _ h]
/-
**Composition.sizeUpTo_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sizeUpTo_succ' (i : Fin c.length) : c.sizeUpTo ((i : Nat) + 1) = c.sizeUpT
o i + c.blocksFun i
参数：i : Fin c.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.sizeUpTo_succ`：sizeUpTo_succ {i : Nat} (h : i < c.length) : 
c.sizeUpTo (i + 1) = c.sizeUpTo i + c.blocks[i]
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem sizeUpTo_succ' (i : Fin c.length) :
    c.sizeUpTo ((i : ℕ) + 1) = c.sizeUpTo i + c.blocksFun i :=
  c.sizeUpTo_succ i.2
/-
**Composition.sizeUpTo_strict_mono** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sizeUpTo_strict_mono {i : Nat} (h : i < c.length) : c.sizeUpTo i < c.sizeU
pTo (i + 1)
参数：h : i < c.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.sizeUpTo_succ`：sizeUpTo_succ {i : Nat} (h : i < c.length) : 
c.sizeUpTo (i + 1) = c.sizeUpTo i + c.blocks[i]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem sizeUpTo_strict_mono {i : ℕ} (h : i < c.length) : c.sizeUpTo i < c.sizeUpTo (i + 1) := by
  rw [c.sizeUpTo_succ h]
  simp
/-
**Composition.monotone_sizeUpTo** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：monotone_sizeUpTo : Monotone c.sizeUpTo
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.monotone_sum_take`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : 
Preorder M] [CanonicallyOrderedAdd M] (L : List M),   Monotone fun i => (List.ta
ke i L).sum
-/
theorem monotone_sizeUpTo : Monotone c.sizeUpTo :=
  monotone_sum_take _

/-- The `i`-th boundary of a composition, i.e., the leftmost point of the `i`-th block. We include
a virtual point at the right of the last block, to make for a nice equiv with
`CompositionAsSet n`. -/
/-
**Composition.boundary** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：boundary : Fin (c.length + 1) ↪o Fin (n + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th boundary of a composition, i.e., the leftmost point of the `i`-th blo
ck. We include
a virtual point at the right of the last block, to make for a nice equiv with
`CompositionAsSet n`.
-/
def boundary : Fin (c.length + 1) ↪o Fin (n + 1) :=
  (OrderEmbedding.ofStrictMono fun i => ⟨c.sizeUpTo i, Nat.lt_succ_of_le (c.sizeUpTo_le i)⟩) <|
    Fin.strictMono_iff_lt_succ.2 fun ⟨_, hi⟩ => c.sizeUpTo_strict_mono hi

@[simp]
/-
**Composition.boundary_zero** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：boundary_zero : c.boundary 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Composition.sizeUpTo_zero`：sizeUpTo_zero : c.sizeUpTo 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem boundary_zero : c.boundary 0 = 0 := by simp [boundary]

@[simp]
/-
**Composition.boundary_last** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：boundary_last : c.boundary (Fin.last c.length) = Fin.last n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Composition.sizeUpTo_length`：sizeUpTo_length : c.sizeUpTo c.length = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem boundary_last : c.boundary (Fin.last c.length) = Fin.last n := by
  simp [boundary, Fin.ext_iff]

/-- The boundaries of a composition, i.e., the leftmost point of all the blocks. We include
a virtual point at the right of the last block, to make for a nice equiv with
`CompositionAsSet n`. -/
/-
**Composition.boundaries** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：boundaries : Finset (Fin (n + 1))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The boundaries of a composition, i.e., the leftmost point of all the blocks. We 
include
a virtual point at the right of the last block, to make for a nice equiv with
`CompositionAsSet n`.
-/
def boundaries : Finset (Fin (n + 1)) :=
  Finset.univ.map c.boundary.toEmbedding
/-
**Composition.card_boundaries_eq_succ_length** 是 Mathlib 中的一个定理，位于命名空间 `Composit
ion`。
形式化陈述：card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 := by simp [boundaries]

/-- To `c : Composition n`, one can associate a `CompositionAsSet n` by registering the leftmost
point of each block, and adding a virtual point at the right of the last block. -/
/-
**Composition.toCompositionAsSet** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：toCompositionAsSet : CompositionAsSet n where boundaries
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To `c : Composition n`, one can associate a `CompositionAsSet n` by registering 
the leftmost
point of each block, and adding a virtual point at the right of the last block.
-/
def toCompositionAsSet : CompositionAsSet n where
  boundaries := c.boundaries
  zero_mem := by
    simp only [boundaries, Finset.mem_univ, Finset.mem_map]
    exact ⟨0, And.intro True.intro rfl⟩
  getLast_mem := by
    simp only [boundaries, Finset.mem_univ, Finset.mem_map]
    exact ⟨Fin.last c.length, And.intro True.intro c.boundary_last⟩

/-- The canonical increasing bijection between `Fin (c.length + 1)` and `c.boundaries` is
exactly `c.boundary`. -/
/-
**Composition.orderEmbOfFin_boundaries** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：orderEmbOfFin_boundaries : c.boundaries.orderEmbOfFin c.card_boundaries_eq
_succ_length = c.boundary
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.card_boundaries_eq_succ_length`：card_boundaries_eq_succ_leng
th : c.boundaries.card = c.length + 1
· 使用定理 `Finset.orderEmbOfFin_unique'`：orderEmbOfFin_unique' {s : Finset α} {k : 
Nat} (h : s.card = k) {f : Fin k ↪o α} (hfs : forall x, f x in s) : f = s.orderE
mbOfFin h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_map'`：mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map 
f ↔ a in s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)

--- 原说明 ---
The canonical increasing bijection between `Fin (c.length + 1)` and `c.boundarie
s` is
exactly `c.boundary`.
-/
theorem orderEmbOfFin_boundaries :
    c.boundaries.orderEmbOfFin c.card_boundaries_eq_succ_length = c.boundary := by
  refine (Finset.orderEmbOfFin_unique' _ ?_).symm
  exact fun i => (Finset.mem_map' _).2 (Finset.mem_univ _)

/-- Embedding the `i`-th block of a composition (identified with `Fin (c.blocksFun i)`) into
`Fin n` at the relevant position. -/
/-
**Composition.embedding** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：embedding (i : Fin c.length) : Fin (c.blocksFun i) ↪o Fin n
参数：i : Fin c.length。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding the `i`-th block of a composition (identified with `Fin (c.blocksFun i
)`) into
`Fin n` at the relevant position.
-/
def embedding (i : Fin c.length) : Fin (c.blocksFun i) ↪o Fin n :=
  (Fin.natAddOrderEmb <| c.sizeUpTo i).trans <| Fin.castLEOrderEmb <|
    calc
      c.sizeUpTo i + c.blocksFun i = c.sizeUpTo (i + 1) := (c.sizeUpTo_succ i.2).symm
      _ ≤ c.sizeUpTo c.length := monotone_sum_take _ i.2
      _ = n := c.sizeUpTo_length

@[simp]
/-
**Composition.coe_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：coe_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) : (c.embedding 
i j : Nat) = c.sizeUpTo i + j
参数：i : Fin c.length；j : Fin (c.blocksFun i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    (c.embedding i j : ℕ) = c.sizeUpTo i + j :=
  rfl

/-- `index_exists` asserts there is some `i` with `j < c.sizeUpTo (i+1)`.
In the next definition `index` we use `Nat.find` to produce the minimal such index.
-/
/-
**Composition.index_exists** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：index_exists {j : Nat} (h : j < n) : exists i : Nat, j < c.sizeUpTo (i + 1
) ∧ i < c.length
参数：h : j < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_pos_of_sum_pos`：∀ {M : Type u_4} [inst : AddMonoid M] [inst_
1 : Preorder M] (L : List M), 0 < L.sum → 0 < L.length
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `LT.lt.pos`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.sizeUpTo_length`：sizeUpTo_length : c.sizeUpTo c.length = n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.pred_lt`：∀ {n : ℕ}, n ≠ 0 → n.pred < n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
`index_exists` asserts there is some `i` with `j < c.sizeUpTo (i+1)`.
In the next definition `index` we use `Nat.find` to produce the minimal such ind
ex.
-/
theorem index_exists {j : ℕ} (h : j < n) : ∃ i : ℕ, j < c.sizeUpTo (i + 1) ∧ i < c.length := by
  have length_pos := length_pos_of_sum_pos (blocks c) (h.pos.trans_eq c.blocks_sum.symm)
  refine ⟨_, ?_, Nat.pred_lt length_pos.ne'⟩
  have : c.length - 1 + 1 = c.length := Nat.succ_pred_eq_of_pos length_pos
  simp [this, h]

/-- `c.index j` is the index of the block in the composition `c` containing `j`. -/
/-
**Composition.index** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：index (j : Fin n) : Fin c.length
参数：j : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`c.index j` is the index of the block in the composition `c` containing `j`.
-/
def index (j : Fin n) : Fin c.length :=
  ⟨Nat.find (c.index_exists j.2), (Nat.find_spec (c.index_exists j.2)).2⟩
/-
**Composition.lt_sizeUpTo_index_succ** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：lt_sizeUpTo_index_succ (j : Fin n) : (j : Nat) < c.sizeUpTo (c.index j).su
cc
参数：j : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Composition.index_exists`：index_exists {j : Nat} (h : j < n) : exists i 
: Nat, j < c.sizeUpTo (i + 1) ∧ i < c.length
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem lt_sizeUpTo_index_succ (j : Fin n) : (j : ℕ) < c.sizeUpTo (c.index j).succ :=
  (Nat.find_spec (c.index_exists j.2)).1
/-
**Composition.sizeUpTo_index_le** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sizeUpTo_index_le (j : Fin n) : c.sizeUpTo (c.index j) <= j
参数：j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Composition.sizeUpTo_zero`：sizeUpTo_zero : c.sizeUpTo 0 = 0
· 使用定理 `Nat.pred_lt`：∀ {n : ℕ}, n ≠ 0 → n.pred < n
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.succ_pred_eq_of_pos`：∀ {n : ℕ}, 0 < n → n.pred.succ = n
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `Composition.index_exists`：index_exists {j : Nat} (h : j < n) : exists i 
: Nat, j < c.sizeUpTo (i + 1) ∧ i < c.length
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem sizeUpTo_index_le (j : Fin n) : c.sizeUpTo (c.index j) ≤ j := by
  by_contra! H
  set i := c.index j
  have i_pos : (0 : ℕ) < i := by
    by_contra! i_pos
    revert H
    simp [nonpos_iff_eq_zero.1 i_pos, c.sizeUpTo_zero]
  let i₁ := (i : ℕ).pred
  have i₁_lt_i : i₁ < i := Nat.pred_lt (ne_of_gt i_pos)
  have i₁_succ : i₁ + 1 = i := Nat.succ_pred_eq_of_pos i_pos
  have := Nat.find_min (c.index_exists j.2) i₁_lt_i
  simp_all [lt_trans i₁_lt_i (c.index j).2]

/-- Mapping an element `j` of `Fin n` to the element in the block containing it, identified with
`Fin (c.blocksFun (c.index j))` through the canonical increasing bijection. -/
/-
**Composition.invEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：invEmbedding (j : Fin n) : Fin (c.blocksFun (c.index j))
参数：j : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Mapping an element `j` of `Fin n` to the element in the block containing it, ide
ntified with
`Fin (c.blocksFun (c.index j))` through the canonical increasing bijection.
-/
def invEmbedding (j : Fin n) : Fin (c.blocksFun (c.index j)) :=
  ⟨j - c.sizeUpTo (c.index j), by
    rw [tsub_lt_iff_right, add_comm, ← sizeUpTo_succ']
    · exact lt_sizeUpTo_index_succ _ _
    · exact sizeUpTo_index_le _ _⟩

@[simp]
/-
**Composition.coe_invEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：coe_invEmbedding (j : Fin n) : (c.invEmbedding j : Nat) = j - c.sizeUpTo (
c.index j)
参数：j : Fin n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_invEmbedding (j : Fin n) : (c.invEmbedding j : ℕ) = j - c.sizeUpTo (c.index j) :=
  rfl

@[simp]
/-
**Composition.embedding_comp_inv** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：embedding_comp_inv (j : Fin n) : c.embedding (c.index j) (c.invEmbedding j
) = j
参数：j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Composition.sizeUpTo_index_le`：sizeUpTo_index_le (j : Fin n) : c.sizeUpT
o (c.index j) <= j
-/
theorem embedding_comp_inv (j : Fin n) : c.embedding (c.index j) (c.invEmbedding j) = j := by
  rw [Fin.ext_iff]
  apply add_tsub_cancel_of_le (c.sizeUpTo_index_le j)
/-
**Composition.mem_range_embedding_iff** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：mem_range_embedding_iff {j : Fin n} {i : Fin c.length} : j in Set.range (c
.embedding i) ↔ c.sizeUpTo i <= j ∧ (j : Nat) < c.sizeUpTo (i : Nat).succ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Composition.sizeUpTo_succ'`：sizeUpTo_succ' (i : Fin c.length) : c.sizeUp
To ((i : Nat) + 1) = c.sizeUpTo i + c.blocksFun i
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Fin.is_lt`：∀ {n : ℕ} (a : Fin n), ↑a < n
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `tsub_lt_iff_left`：tsub_lt_iff_left (hbc : b <= a) : a - b < c ↔ a < b + 
c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
-/
theorem mem_range_embedding_iff {j : Fin n} {i : Fin c.length} :
    j ∈ Set.range (c.embedding i) ↔ c.sizeUpTo i ≤ j ∧ (j : ℕ) < c.sizeUpTo (i : ℕ).succ := by
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

/-- The embeddings of different blocks of a composition are disjoint. -/
/-
**Composition.disjoint_range** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：disjoint_range {i₁ i₂ : Fin c.length} (h : i₁ != i₂) : Disjoint (Set.range
 (c.embedding i₁)) (Set.range (c.embedding i₂))
参数：h : i₁ != i₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Composition.mem_range_embedding_iff`：mem_range_embedding_iff {j : Fin n}
 {i : Fin c.length} : j in Set.range (c.embedding i) ↔ c.sizeUpTo i <= j ∧ (j : 
Nat) < c.sizeUpTo (i : Na…
· 使用定理 `List.monotone_sum_take`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : 
Preorder M] [CanonicallyOrderedAdd M] (L : List M),   Monotone fun i => (List.ta
ke i L).sum
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a

--- 原说明 ---
The embeddings of different blocks of a composition are disjoint.
-/
theorem disjoint_range {i₁ i₂ : Fin c.length} (h : i₁ ≠ i₂) :
    Disjoint (Set.range (c.embedding i₁)) (Set.range (c.embedding i₂)) := by
  wlog h' : i₁ < i₂
  · exact (this c h.symm (h.lt_or_gt.resolve_left h')).symm
  by_contra d
  obtain ⟨x, hx₁, hx₂⟩ :
    ∃ x : Fin n, x ∈ Set.range (c.embedding i₁) ∧ x ∈ Set.range (c.embedding i₂) :=
    Set.not_disjoint_iff.1 d
  have A : (i₁ : ℕ).succ ≤ i₂ := Nat.succ_le_of_lt h'
  apply lt_irrefl (x : ℕ)
  calc
    (x : ℕ) < c.sizeUpTo (i₁ : ℕ).succ := (c.mem_range_embedding_iff.1 hx₁).2
    _ ≤ c.sizeUpTo (i₂ : ℕ) := monotone_sum_take _ A
    _ ≤ x := (c.mem_range_embedding_iff.1 hx₂).1
/-
**Composition.mem_range_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：mem_range_embedding (j : Fin n) : j in Set.range (c.embedding (c.index j))
参数：j : Fin n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.embedding_comp_inv`：embedding_comp_inv (j : Fin n) : c.embed
ding (c.index j) (c.invEmbedding j) = j
-/
theorem mem_range_embedding (j : Fin n) : j ∈ Set.range (c.embedding (c.index j)) := by
  have : c.embedding (c.index j) (c.invEmbedding j) ∈ Set.range (c.embedding (c.index j)) :=
    Set.mem_range_self _
  rwa [c.embedding_comp_inv j] at this
/-
**Composition.mem_range_embedding_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：mem_range_embedding_iff' {j : Fin n} {i : Fin c.length} : j in Set.range (
c.embedding i) ↔ i = c.index j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `Composition.disjoint_range`：disjoint_range {i₁ i₂ : Fin c.length} (h : i
₁ != i₂) : Disjoint (Set.range (c.embedding i₁)) (Set.range (c.embedding i₂))
· 使用定理 `Composition.mem_range_embedding`：mem_range_embedding (j : Fin n) : j in 
Set.range (c.embedding (c.index j))
-/
theorem mem_range_embedding_iff' {j : Fin n} {i : Fin c.length} :
    j ∈ Set.range (c.embedding i) ↔ i = c.index j := by
  constructor
  · rw [← not_imp_not]
    intro h
    exact Set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j)
  · intro h
    rw [h]
    exact c.mem_range_embedding j

@[simp]
/-
**Composition.index_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：index_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) : c.index (c.
embedding i j) = i
参数：i : Fin c.length；j : Fin (c.blocksFun i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.mem_range_embedding_iff'`：mem_range_embedding_iff' {j : Fin 
n} {i : Fin c.length} : j in Set.range (c.embedding i) ↔ i = c.index j
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
-/
theorem index_embedding (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    c.index (c.embedding i j) = i := by
  symm
  rw [← mem_range_embedding_iff']
  apply Set.mem_range_self
/-
**Composition.invEmbedding_comp** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：invEmbedding_comp (i : Fin c.length) (j : Fin (c.blocksFun i)) : (c.invEmb
edding (c.embedding i j) : Nat) = j
参数：i : Fin c.length；j : Fin (c.blocksFun i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.index_embedding`：index_embedding (i : Fin c.length) (j : Fin
 (c.blocksFun i)) : c.index (c.embedding i j) = i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem invEmbedding_comp (i : Fin c.length) (j : Fin (c.blocksFun i)) :
    (c.invEmbedding (c.embedding i j) : ℕ) = j := by
  simp_rw [coe_invEmbedding, index_embedding, coe_embedding, add_tsub_cancel_left]

/-- Equivalence between the disjoint union of the blocks (each of them seen as
`Fin (c.blocksFun i)`) with `Fin n`. -/
/-
**Composition.blocksFinEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：blocksFinEquiv : (Σ i : Fin c.length, Fin (c.blocksFun i)) ≃ Fin n where t
oFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.embedding_comp_inv`：embedding_comp_inv (j : Fin n) : c.embed
ding (c.index j) (c.invEmbedding j) = j

--- 原说明 ---
Equivalence between the disjoint union of the blocks (each of them seen as
`Fin (c.blocksFun i)`) with `Fin n`.
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
/-
**Composition.blocksFun_congr** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：blocksFun_congr {n₁ n₂ : Nat} (c₁ : Composition n₁) (c₂ : Composition n₂) 
(i₁ : Fin c₁.length) (i₂ : Fin c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.bl
ocks) (hi : (i₁ : Nat) = i₂) : c₁.blocksFun i₁ = c₂.blocksFun i₂
参数：c₁ : Composition n₁；c₂ : Composition n₂；i₁ : Fin c₁.length；i₂ : Fin c₂.length
；hn : n₁ = n₂；hc : c₁.blocks = c₂.blocks；hi : (i₁ : Nat) = i₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.ext_iff`：∀ {n : ℕ} {x y : Composition n}, x = y ↔ x.blocks =
 y.blocks
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
-/
theorem blocksFun_congr {n₁ n₂ : ℕ} (c₁ : Composition n₁) (c₂ : Composition n₂) (i₁ : Fin c₁.length)
    (i₂ : Fin c₂.length) (hn : n₁ = n₂) (hc : c₁.blocks = c₂.blocks) (hi : (i₁ : ℕ) = i₂) :
    c₁.blocksFun i₁ = c₂.blocksFun i₂ := by
  cases hn
  rw [← Composition.ext_iff] at hc
  cases hc
  congr
  rwa [Fin.ext_iff]

/-- Two compositions (possibly of different integers) coincide if and only if they have the
same sequence of blocks. -/
/-
**Composition.sigma_eq_iff_blocks_eq** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：sigma_eq_iff_blocks_eq {c : Σ n, Composition n} {c' : Σ n, Composition n} 
: c = c' ↔ c.2.blocks = c'.2.blocks
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
· 使用定理 `Composition.ext`：∀ {n : ℕ} {x y : Composition n}, x.blocks = y.blocks → 
x = y

--- 原说明 ---
Two compositions (possibly of different integers) coincide if and only if they h
ave the
same sequence of blocks.
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
/-
**Composition.prod_prod_apply_embedding** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：prod_prod_apply_embedding {A : Type*} [CommMonoid A] (a : Fin n -> A) (x :
 Composition n) : ∏ i, ∏ j, a (x.embedding i j) = ∏ i, a i
参数：a : Fin n -> A；x : Composition n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_sigma'`：prod_sigma' {σ : α -> Type*} (s : Finset α) (t : for
all a, Finset (σ a)) (f : forall a, σ a -> β) : (∏ a in s, ∏ s in t a, f a s) = 
∏ x in s…
· 使用定理 `Equiv.prod_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
Fintype ι] [inst_1 : Fintype κ] [inst_2 : CommMonoid M]   (e : ι ≃ κ) (g : κ → M
), ∏ …
-/
lemma prod_prod_apply_embedding {A : Type*} [CommMonoid A] (a : Fin n → A) (x : Composition n) :
    ∏ i, ∏ j, a (x.embedding i j) = ∏ i, a i := by
  simpa [Finset.prod_sigma', Finset.univ_sigma_univ] using! x.blocksFinEquiv.prod_comp a

/-! ### The composition `Composition.ones` -/


/-- The composition made of blocks all of size `1`. -/
/-
**Composition.ones** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：ones (n : Nat) : Composition n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition made of blocks all of size `1`.
-/
def ones (n : ℕ) : Composition n :=
  ⟨replicate n (1 : ℕ), fun {i} hi => by simp [List.eq_of_mem_replicate hi], by simp⟩
/-
**Composition.** 是 Mathlib 中的一个实例，位于命名空间 `Composition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n : ℕ} : Inhabited (Composition n) :=
  ⟨Composition.ones n⟩

@[simp]
/-
**Composition.ones_length** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：ones_length (n : Nat) : (ones n).length = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_replicate`：∀ {α : Type u} {n : ℕ} {a : α}, (List.replicate n
 a).length = n
-/
theorem ones_length (n : ℕ) : (ones n).length = n :=
  List.length_replicate

@[simp]
/-
**Composition.ones_blocks** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：ones_blocks (n : Nat) : (ones n).blocks = replicate n (1 : Nat)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ones_blocks (n : ℕ) : (ones n).blocks = replicate n (1 : ℕ) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Composition.ones_blocksFun** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：ones_blocksFun (n : Nat) (i : Fin (ones n).length) : (ones n).blocksFun i 
= 1
参数：n : Nat；i : Fin (ones n).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_replicate`：∀ {α : Type u_1} {a : α} {n i : ℕ} (h : i < (Lis
t.replicate n a).length), (List.replicate n a)[i] = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ones_blocksFun (n : ℕ) (i : Fin (ones n).length) : (ones n).blocksFun i = 1 := by
  simp only [blocksFun, ones, get_eq_getElem, getElem_replicate]

@[simp]
/-
**Composition.ones_sizeUpTo** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：ones_sizeUpTo (n : Nat) (i : Nat) : (ones n).sizeUpTo i = min i n
参数：n : Nat；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.take_replicate`：∀ {α : Type u_1} {a : α} {i n : ℕ}, List.take i (Li
st.replicate n a) = List.replicate (min i n) a
· 使用定理 `List.sum_replicate`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ) (a : M
), (List.replicate n a).sum = n • a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ones_sizeUpTo (n : ℕ) (i : ℕ) : (ones n).sizeUpTo i = min i n := by
  simp [sizeUpTo, ones_blocks, take_replicate]

@[simp]
/-
**Composition.ones_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：ones_embedding (i : Fin (ones n).length) (h : 0 < (ones n).blocksFun i) : 
(ones n).embedding i ⟨0, h⟩ = ⟨i, lt_of_lt_of_le i.2 (ones n).length_le⟩
参数：i : Fin (ones n).length；h : 0 < (ones n).blocksFun i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Composition.length_le`：length_le : c.length <= n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.ones_sizeUpTo`：ones_sizeUpTo (n : Nat) (i : Nat) : (ones n).
sizeUpTo i = min i n
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Composition.ones_length`：ones_length (n : Nat) : (ones n).length = n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem ones_embedding (i : Fin (ones n).length) (h : 0 < (ones n).blocksFun i) :
    (ones n).embedding i ⟨0, h⟩ = ⟨i, lt_of_lt_of_le i.2 (ones n).length_le⟩ := by
  ext
  simpa using i.2.le
/-
**Composition.eq_ones_iff** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：eq_ones_iff {c : Composition n} : c = ones n ↔ forall i in c.blocks, i = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.eq_of_mem_replicate`：∀ {α : Type u_1} {a b : α} {n : ℕ}, b ∈ List.r
eplicate n a → b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.ext`：∀ {n : ℕ} {x y : Composition n}, x.blocks = y.blocks → 
x = y
· 使用定理 `List.eq_replicate_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, (∀ b ∈ 
l, b = a) → l = List.replicate l.length a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.sum_replicate`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ) (a : M
), (List.replicate n a).sum = n • a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Composition.ones_blocks`：ones_blocks (n : Nat) : (ones n).blocks = repli
cate n (1 : Nat)
-/
theorem eq_ones_iff {c : Composition n} : c = ones n ↔ ∀ i ∈ c.blocks, i = 1 := by
  constructor
  · rintro rfl
    exact fun i => eq_of_mem_replicate
  · intro H
    ext1
    have A : c.blocks = replicate c.blocks.length 1 := eq_replicate_of_mem H
    have : c.blocks.length = n := by
      conv_rhs => rw [← c.blocks_sum, A]
      simp
    rw [A, this, ones_blocks]
/-
**Composition.ne_ones_iff** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：ne_ones_iff {c : Composition n} : c != ones n ↔ exists i in c.blocks, 1 < 
i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Composition.eq_ones_iff`：eq_ones_iff {c : Composition n} : c = ones n ↔ 
forall i in c.blocks, i = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Composition.one_le_blocks`：one_le_blocks {i : Nat} (h : i in c.blocks) :
 1 <= i
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ne_ones_iff {c : Composition n} : c ≠ ones n ↔ ∃ i ∈ c.blocks, 1 < i := by
  refine (not_congr eq_ones_iff).trans ?_
  have : ∀ j ∈ c.blocks, j = 1 ↔ j ≤ 1 := fun j hj => by simp [le_antisymm_iff, c.one_le_blocks hj]
  simp +contextual [this]
/-
**Composition.eq_ones_iff_length** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：eq_ones_iff_length {c : Composition n} : c = ones n ↔ c.length = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.ones_length`：ones_length (n : Nat) : (ones n).length = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Composition.ne_ones_iff`：ne_ones_iff {c : Composition n} : c != ones n ↔
 exists i in c.blocks, 1 < i
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `List.mem_ofFn'`：mem_ofFn' {n} (f : Fin n -> α) (a : α) : a in ofFn f ↔ a
 in Set.range f
· 使用定理 `Composition.ofFn_blocksFun`：ofFn_blocksFun : ofFn c.blocksFun = c.blocks
· 使用定理 `Finset.sum_lt_sum`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M]   {f g : ι → M} {s : Fins
et ι} […
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Composition.one_le_blocksFun`：one_le_blocksFun (i : Fin c.length) : 1 <=
 c.blocksFun i
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Composition.sum_blocksFun`：sum_blocksFun : ∑ i, c.blocksFun i = n
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
        obtain ⟨i, hi, i_blocks⟩ : ∃ i ∈ c.blocks, 1 < i := ne_ones_iff.1 H
        rw [← ofFn_blocksFun, mem_ofFn' c.blocksFun, Set.mem_range] at hi
        obtain ⟨j : Fin c.length, hj : c.blocksFun j = i⟩ := hi
        rw [← hj] at i_blocks
        exact Finset.sum_lt_sum (fun i _ => one_le_blocksFun c i) ⟨j, Finset.mem_univ _, i_blocks⟩
        }
      _ = n := c.sum_blocksFun
/-
**Composition.eq_ones_iff_le_length** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：eq_ones_iff_le_length {c : Composition n} : c = ones n ↔ n <= c.length
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Composition.length_le`：length_le : c.length <= n
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_ones_iff_le_length {c : Composition n} : c = ones n ↔ n ≤ c.length := by
  simp [eq_ones_iff_length, le_antisymm_iff, c.length_le]

/-! ### The composition `Composition.single` -/

/-- The composition made of a single block of size `n`. -/
/-
**Composition.single** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：single (n : Nat) (h : 0 < n) : Composition n
参数：n : Nat；h : 0 < n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition made of a single block of size `n`.
-/
def single (n : ℕ) (h : 0 < n) : Composition n :=
  ⟨[n], by simp [h], by simp⟩

@[simp]
/-
**Composition.single_length** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：single_length {n : Nat} (h : 0 < n) : (single n h).length = 1
参数：h : 0 < n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_length {n : ℕ} (h : 0 < n) : (single n h).length = 1 :=
  rfl

@[simp]
/-
**Composition.single_blocks** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：single_blocks {n : Nat} (h : 0 < n) : (single n h).blocks = [n]
参数：h : 0 < n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_blocks {n : ℕ} (h : 0 < n) : (single n h).blocks = [n] :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Composition.single_blocksFun** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：single_blocksFun {n : Nat} (h : 0 < n) (i : Fin (single n h).length) : (si
ngle n h).blocksFun i = n
参数：h : 0 < n；i : Fin (single n h).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_blocksFun {n : ℕ} (h : 0 < n) (i : Fin (single n h).length) :
    (single n h).blocksFun i = n := by simp [blocksFun, single]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Composition.single_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：single_embedding {n : Nat} (h : 0 < n) (i : Fin n) : ((single n h).embeddi
ng (0 : Fin 1)) i = i
参数：h : 0 < n；i : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `Composition.sizeUpTo_zero`：sizeUpTo_zero : c.sizeUpTo 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem single_embedding {n : ℕ} (h : 0 < n) (i : Fin n) :
    ((single n h).embedding (0 : Fin 1)) i = i := by
  ext
  simp
/-
**Composition.eq_single_iff_length** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：eq_single_iff_length {n : Nat} (h : 0 < n) {c : Composition n} : c = singl
e n h ↔ c.length = 1
参数：h : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.single_length`：single_length {n : Nat} (h : 0 < n) : (single
 n h).length = 1
· 使用定理 `Composition.ext`：∀ {n : ℕ} {x y : Composition n}, x.blocks = y.blocks → 
x = y
· 使用定理 `Composition.blocks_length`：blocks_length : c.blocks.length = c.length
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n
· 使用定理 `List.eq_cons_of_length_one`：eq_cons_of_length_one {l : List α} (h : l.le
ngth = 1) : l = [l.get ⟨0, by lia⟩]
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem eq_single_iff_length {n : ℕ} (h : 0 < n) {c : Composition n} :
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
/-
**Composition.ne_single_iff** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：ne_single_iff {n : Nat} (hn : 0 < n) {c : Composition n} : c != single n h
n ↔ forall i, c.blocksFun i < n
参数：hn : 0 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₂`：contrapose_iff₂ {p q : Prop} 
: (p ↔ ¬ q) -> (¬ p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Composition.single_blocksFun`：single_blocksFun {n : Nat} (h : 0 < n) (i 
: Fin (single n h).length) : (single n h).blocksFun i = n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.eq_single_iff_length`：eq_single_iff_length {n : Nat} (h : 0 
< n) {c : Composition n} : c = single n h ↔ c.length = 1
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Composition.sum_blocksFun`：sum_blocksFun : ∑ i, c.blocksFun i = n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.single_lt_sum`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Fin
set ι} [Ad…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Composition.one_le_blocksFun`：one_le_blocksFun (i : Fin c.length) : 1 <=
 c.blocksFun i
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_eq_one_of_forall_eq`：card_eq_one_of_forall_eq {i : α} (h : 
forall j, j = i) : card α = 1
-/
theorem ne_single_iff {n : ℕ} (hn : 0 < n) {c : Composition n} :
    c ≠ single n hn ↔ ∀ i, c.blocksFun i < n := by
  contrapose!
  constructor
  · rintro rfl
    exact ⟨⟨0, by simp⟩, by simp⟩
  · rintro ⟨i, hi⟩
    rw [eq_single_iff_length]
    have : ∀ j : Fin c.length, j = i := by
      intro j
      by_contra ji
      apply lt_irrefl (∑ k, c.blocksFun k)
      calc
        ∑ k, c.blocksFun k ≤ c.blocksFun i := by simp only [c.sum_blocksFun, hi]
        _ < ∑ k, c.blocksFun k :=
          Finset.single_lt_sum ji (Finset.mem_univ _) (Finset.mem_univ _) (c.one_le_blocksFun j)
            fun _ _ _ => zero_le
    simpa using Fintype.card_eq_one_of_forall_eq this

variable {m : ℕ}

/-- Change `n` in `(c : Composition n)` to a propositionally equal value. -/
@[simps]
/-
**Composition.cast** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：{n m : ℕ} → Composition m → m = n → Composition n
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.blocks_pos`：∀ {n : ℕ} (self : Composition n) {i : ℕ}, i ∈ se
lf.blocks → 0 < i

--- 原说明 ---
Change `n` in `(c : Composition n)` to a propositionally equal value.
-/
protected def cast (c : Composition m) (hmn : m = n) : Composition n where
  __ := c
  blocks_sum := c.blocks_sum.trans hmn

@[simp]
/-
**Composition.cast_rfl** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：cast_rfl (c : Composition n) : c.cast rfl = c
参数：c : Composition n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cast_rfl (c : Composition n) : c.cast rfl = c := rfl
/-
**Composition.cast_heq** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：cast_heq (c : Composition m) (hmn : m = n) : c.cast hmn ≍ c
参数：c : Composition m；hmn : m = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cast_heq (c : Composition m) (hmn : m = n) : c.cast hmn ≍ c := by subst m; rfl
/-
**Composition.cast_eq_cast** 是 Mathlib 中的一个定理，位于命名空间 `Composition`。
形式化陈述：cast_eq_cast (c : Composition m) (hmn : m = n) : c.cast hmn = cast (hmn ▸ 
rfl) c
参数：c : Composition m；hmn : m = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cast_eq_cast (c : Composition m) (hmn : m = n) :
    c.cast hmn = cast (hmn ▸ rfl) c := by
  subst m
  rfl

/-- Append two compositions to get a composition of the sum of numbers. -/
@[simps]
/-
**Composition.append** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：append (c₁ : Composition m) (c₂ : Composition n) : Composition (m + n) whe
re blocks
参数：c₁ : Composition m；c₂ : Composition n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Append two compositions to get a composition of the sum of numbers.
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
/-
**Composition.reverse** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：reverse (c : Composition n) : Composition n where blocks
参数：c : Composition n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reverse the order of blocks in a composition.
-/
def reverse (c : Composition n) : Composition n where
  blocks := c.blocks.reverse
  blocks_pos hi := c.blocks_pos (mem_reverse.mp hi)
  blocks_sum := by simp

@[simp]
/-
**Composition.reverse_reverse** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_reverse (c : Composition n) : c.reverse.reverse = c
参数：c : Composition n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.ext`：∀ {n : ℕ} {x y : Composition n}, x.blocks = y.blocks → 
x = y
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
lemma reverse_reverse (c : Composition n) : c.reverse.reverse = c :=
  Composition.ext <| List.reverse_reverse _
/-
**Composition.reverse_involutive** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_involutive : Function.Involutive (@reverse n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Composition.reverse_reverse`：reverse_reverse (c : Composition n) : c.rev
erse.reverse = c
-/
lemma reverse_involutive : Function.Involutive (@reverse n) := reverse_reverse
/-
**Composition.reverse_bijective** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_bijective : Function.Bijective (@reverse n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.bijective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Bijective f
· 使用引理 `Composition.reverse_involutive`：reverse_involutive : Function.Involutive
 (@reverse n)
-/
lemma reverse_bijective : Function.Bijective (@reverse n) := reverse_involutive.bijective
/-
**Composition.reverse_injective** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_injective : Function.Injective (@reverse n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用引理 `Composition.reverse_involutive`：reverse_involutive : Function.Involutive
 (@reverse n)
-/
lemma reverse_injective : Function.Injective (@reverse n) := reverse_involutive.injective
/-
**Composition.reverse_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_surjective : Function.Surjective (@reverse n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.surjective`：∀ {α : Sort u} {f : α → α}, Function.Inv
olutive f → Function.Surjective f
· 使用引理 `Composition.reverse_involutive`：reverse_involutive : Function.Involutive
 (@reverse n)
-/
lemma reverse_surjective : Function.Surjective (@reverse n) := reverse_involutive.surjective

@[simp]
/-
**Composition.reverse_inj** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_inj {c₁ c₂ : Composition n} : c₁.reverse = c₂.reverse ↔ c₁ = c₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Composition.reverse_injective`：reverse_injective : Function.Injective (@
reverse n)
-/
lemma reverse_inj {c₁ c₂ : Composition n} : c₁.reverse = c₂.reverse ↔ c₁ = c₂ :=
  reverse_injective.eq_iff

@[simp]
/-
**Composition.reverse_ones** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_ones : (ones n).reverse = ones n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.ext`：∀ {n : ℕ} {x y : Composition n}, x.blocks = y.blocks → 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.reverse_blocks`：∀ {n : ℕ} (c : Composition n), c.reverse.blo
cks = c.blocks.reverse
· 使用定理 `List.reverse_replicate`：∀ {α : Type u_1} {n : ℕ} {a : α}, (List.replicat
e n a).reverse = List.replicate n a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reverse_ones : (ones n).reverse = ones n := by ext1; simp

@[simp]
/-
**Composition.reverse_single** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_single (hn : 0 < n) : (single n hn).reverse = single n hn
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.ext`：∀ {n : ℕ} {x y : Composition n}, x.blocks = y.blocks → 
x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.reverse_blocks`：∀ {n : ℕ} (c : Composition n), c.reverse.blo
cks = c.blocks.reverse
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reverse_single (hn : 0 < n) : (single n hn).reverse = single n hn := by ext1; simp

@[simp]
/-
**Composition.reverse_eq_ones** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_eq_ones {c : Composition n} : c.reverse = ones n ↔ c = ones n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用引理 `Composition.reverse_injective`：reverse_injective : Function.Injective (@
reverse n)
· 使用引理 `Composition.reverse_ones`：reverse_ones : (ones n).reverse = ones n
-/
lemma reverse_eq_ones {c : Composition n} : c.reverse = ones n ↔ c = ones n :=
  reverse_injective.eq_iff' reverse_ones

@[simp]
/-
**Composition.reverse_eq_single** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_eq_single {hn : 0 < n} {c : Composition n} : c.reverse = single n 
hn ↔ c = single n hn
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
 Function.Injective f → ∀ {a b : α} {c : β}, f b = c → (f a = c ↔ a = b)
· 使用引理 `Composition.reverse_injective`：reverse_injective : Function.Injective (@
reverse n)
· 使用引理 `Composition.reverse_single`：reverse_single (hn : 0 < n) : (single n hn).
reverse = single n hn
-/
lemma reverse_eq_single {hn : 0 < n} {c : Composition n} :
    c.reverse = single n hn ↔ c = single n hn :=
  reverse_injective.eq_iff' <| reverse_single _
/-
**Composition.reverse_append** 是 Mathlib 中的一个引理，位于命名空间 `Composition`。
形式化陈述：reverse_append (c₁ : Composition m) (c₂ : Composition n) : reverse (append
 c₁ c₂) = (append c₂.reverse c₁.reverse).cast (add_comm _ _)
参数：c₁ : Composition m；c₂ : Composition n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Composition.ext`：∀ {n : ℕ} {x y : Composition n}, x.blocks = y.blocks → 
x = y
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.reverse_blocks`：∀ {n : ℕ} (c : Composition n), c.reverse.blo
cks = c.blocks.reverse
· 使用定理 `Composition.append_blocks`：∀ {n m : ℕ} (c₁ : Composition m) (c₂ : Compos
ition n), (c₁.append c₂).blocks = c₁.blocks ++ c₂.blocks
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `Composition.cast_blocks`：∀ {n m : ℕ} (c : Composition m) (hmn : m = n), 
(c.cast hmn).blocks = c.blocks
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma reverse_append (c₁ : Composition m) (c₂ : Composition n) :
    reverse (append c₁ c₂) = (append c₂.reverse c₁.reverse).cast (add_comm _ _) :=
  Composition.ext <| by simp

/-- Induction (recursion) principle on `c : Composition _`
that corresponds to the usual induction on the list of blocks of `c`. -/
@[elab_as_elim]
/-
**Composition.recOnSingleAppend** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：recOnSingleAppend {motive : forall n, Composition n -> Sort*} {n : Nat} (c
 : Composition n) (zero : motive 0 (ones 0)) (single_append : forall k n c, moti
ve n c -> motive (k + 1 + n) (append (single (k + 1) k.succ_pos) c)) : motive n 
c
参数：c : Composition n；zero : motive 0 (ones 0)；single_append : forall k n c, moti
ve n c -> motive (k + 1 + n) (append (single (k + 1) k.succ_pos) c)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
Induction (recursion) principle on `c : Composition _`
that corresponds to the usual induction on the list of blocks of `c`.
-/
def recOnSingleAppend {motive : ∀ n, Composition n → Sort*} {n : ℕ} (c : Composition n)
    (zero : motive 0 (ones 0))
    (single_append : ∀ k n c, motive n c →
      motive (k + 1 + n) (append (single (k + 1) k.succ_pos) c)) :
    motive n c :=
  match n, c with
  | _, ⟨blocks, blocks_pos, rfl⟩ =>
    match blocks with
    | [] => zero
    | 0 :: _ => by simp at blocks_pos
    | (k + 1) :: l =>
      single_append k l.sum ⟨l, fun hi ↦ blocks_pos <| mem_cons_of_mem _ hi, rfl⟩ <|
        recOnSingleAppend _ zero single_append

/-- Induction (recursion) principle on `c : Composition _`
that corresponds to the reverse induction on the list of blocks of `c`. -/
@[elab_as_elim]
/-
**Composition.recOnAppendSingle** 是 Mathlib 中的一个定义，位于命名空间 `Composition`。
形式化陈述：recOnAppendSingle {motive : forall n, Composition n -> Sort*} {n : Nat} (c
 : Composition n) (zero : motive 0 (ones 0)) (append_single : forall k n c, moti
ve n c -> motive (n + (k + 1)) (append c (single (k + 1) k.succ_pos))) : motive 
n c
参数：c : Composition n；zero : motive 0 (ones 0)；append_single : forall k n c, moti
ve n c -> motive (n + (k + 1)) (append c (single (k + 1) k.succ_pos))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用引理 `Composition.reverse_reverse`：reverse_reverse (c : Composition n) : c.rev
erse.reverse = c

--- 原说明 ---
Induction (recursion) principle on `c : Composition _`
that corresponds to the reverse induction on the list of blocks of `c`.
-/
def recOnAppendSingle {motive : ∀ n, Composition n → Sort*} {n : ℕ} (c : Composition n)
    (zero : motive 0 (ones 0))
    (append_single : ∀ k n c, motive n c →
      motive (n + (k + 1)) (append c (single (k + 1) k.succ_pos))) :
    motive n c :=
  reverse_reverse c ▸ c.reverse.recOnSingleAppend zero fun k n c ih ↦ by
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

/-- Auxiliary for `List.splitWrtComposition`. -/
/-
**List.splitWrtCompositionAux** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：splitWrtCompositionAux : List α -> List Nat -> List (List α) | _, [] => []
 | l, n::ns => let (l₁, l₂)
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary for `List.splitWrtComposition`.
-/
def splitWrtCompositionAux : List α → List ℕ → List (List α)
  | _, [] => []
  | l, n::ns =>
    let (l₁, l₂) := l.splitAt n
    l₁::splitWrtCompositionAux l₂ ns

/-- Given a list of length `n` and a composition `[i₁, ..., iₖ]` of `n`, split `l` into a list of
`k` lists corresponding to the blocks of the composition, of respective lengths `i₁`, ..., `iₖ`.
This makes sense mostly when `n = l.length`, but this is not necessary for the definition. -/
/-
**List.splitWrtComposition** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：splitWrtComposition (l : List α) (c : Composition n) : List (List α)
参数：l : List α；c : Composition n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a list of length `n` and a composition `[i₁, ..., iₖ]` of `n`, split `l` i
nto a list of
`k` lists corresponding to the blocks of the composition, of respective lengths 
`i₁`, ..., `iₖ`.
This makes sense mostly when `n = l.length`, but this is not necessary for the d
efinition.
-/
def splitWrtComposition (l : List α) (c : Composition n) : List (List α) :=
  splitWrtCompositionAux l c.blocks

@[local simp]
/-
**List.splitWrtCompositionAux_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitWrtCompositionAux_cons (l : List α) (n ns) : l.splitWrtCompositionAux
 (n::ns) = take n l::(drop n l).splitWrtCompositionAux ns
参数：l : List α；n ns。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.splitAt_eq`：∀ {α : Type u_1} {i : ℕ} {l : List α}, List.splitAt i l
 = (List.take i l, List.drop i l)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem splitWrtCompositionAux_cons (l : List α) (n ns) :
    l.splitWrtCompositionAux (n::ns) = take n l::(drop n l).splitWrtCompositionAux ns := by
  simp [splitWrtCompositionAux]
/-
**List.length_splitWrtCompositionAux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_splitWrtCompositionAux (l : List α) (ns) : length (l.splitWrtCompos
itionAux ns) = ns.length
参数：l : List α；ns。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.splitWrtCompositionAux_cons`：splitWrtCompositionAux_cons (l : List 
α) (n ns) : l.splitWrtCompositionAux (n::ns) = take n l::(drop n l).splitWrtComp
ositionAux ns
-/
theorem length_splitWrtCompositionAux (l : List α) (ns) :
    length (l.splitWrtCompositionAux ns) = ns.length := by
    induction ns generalizing l
    · simp [splitWrtCompositionAux, *]
    · simp [*]

/-- When one splits a list along a composition `c`, the number of sublists thus created is
`c.length`. -/
@[simp]
/-
**List.length_splitWrtComposition** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_splitWrtComposition (l : List α) (c : Composition n) : length (l.sp
litWrtComposition c) = c.length
参数：l : List α；c : Composition n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_splitWrtCompositionAux`：length_splitWrtCompositionAux (l : L
ist α) (ns) : length (l.splitWrtCompositionAux ns) = ns.length

--- 原说明 ---
When one splits a list along a composition `c`, the number of sublists thus crea
ted is
`c.length`.
-/
theorem length_splitWrtComposition (l : List α) (c : Composition n) :
    length (l.splitWrtComposition c) = c.length :=
  length_splitWrtCompositionAux _ _
/-
**List.map_length_splitWrtCompositionAux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_length_splitWrtCompositionAux {ns : List Nat} : forall {l : List α}, n
s.sum <= l.length -> map length (l.splitWrtCompositionAux ns) = ns
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem map_length_splitWrtCompositionAux {ns : List ℕ} :
    ∀ {l : List α}, ns.sum ≤ l.length → map length (l.splitWrtCompositionAux ns) = ns := by
  induction ns with
  | nil => simp [splitWrtCompositionAux]
  | cons n ns IH => grind [splitWrtCompositionAux_cons]

/-- When one splits a list along a composition `c`, the lengths of the sublists thus created are
given by the block sizes in `c`. -/
/-
**List.map_length_splitWrtComposition** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_length_splitWrtComposition (l : List α) (c : Composition l.length) : m
ap length (l.splitWrtComposition c) = c.blocks
参数：l : List α；c : Composition l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.map_length_splitWrtCompositionAux`：map_length_splitWrtCompositionAu
x {ns : List Nat} : forall {l : List α}, ns.sum <= l.length -> map length (l.spl
itWrtCompositionAux ns) = ns
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n

--- 原说明 ---
When one splits a list along a composition `c`, the lengths of the sublists thus
 created are
given by the block sizes in `c`.
-/
theorem map_length_splitWrtComposition (l : List α) (c : Composition l.length) :
    map length (l.splitWrtComposition c) = c.blocks :=
  map_length_splitWrtCompositionAux (le_of_eq c.blocks_sum)
/-
**List.length_pos_of_mem_splitWrtComposition** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_pos_of_mem_splitWrtComposition {l l' : List α} {c : Composition l.l
ength} (h : l' in l.splitWrtComposition c) : 0 < length l'
参数：h : l' in l.splitWrtComposition c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_map_of_mem`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {a : α
} {f : α → β}, a ∈ l → f a ∈ List.map f l
· 使用定理 `Composition.blocks_pos`：∀ {n : ℕ} (self : Composition n) {i : ℕ}, i ∈ se
lf.blocks → 0 < i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_length_splitWrtComposition`：map_length_splitWrtComposition (l :
 List α) (c : Composition l.length) : map length (l.splitWrtComposition c) = c.b
locks
-/
theorem length_pos_of_mem_splitWrtComposition {l l' : List α} {c : Composition l.length}
    (h : l' ∈ l.splitWrtComposition c) : 0 < length l' := by
  have : l'.length ∈ (l.splitWrtComposition c).map List.length :=
    List.mem_map_of_mem h
  rw [map_length_splitWrtComposition] at this
  exact c.blocks_pos this
/-
**List.sum_take_map_length_splitWrtComposition** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sum_take_map_length_splitWrtComposition (l : List α) (c : Composition l.le
ngth) (i : Nat) : (((l.splitWrtComposition c).map length).take i).sum = c.sizeUp
To i
参数：l : List α；c : Composition l.length；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.map_length_splitWrtComposition`：map_length_splitWrtComposition (l :
 List α) (c : Composition l.length) : map length (l.splitWrtComposition c) = c.b
locks
-/
theorem sum_take_map_length_splitWrtComposition (l : List α) (c : Composition l.length) (i : ℕ) :
    (((l.splitWrtComposition c).map length).take i).sum = c.sizeUpTo i := by
  congr
  exact map_length_splitWrtComposition l c
/-
**List.getElem_splitWrtCompositionAux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_splitWrtCompositionAux (l : List α) (ns : List Nat) {i : Nat} (hi 
: i < (l.splitWrtCompositionAux ns).length) : (l.splitWrtCompositionAux ns)[i] =
 (l.take (ns.take (i + 1)).sum).drop (ns.take i).sum
参数：l : List α；ns : List Nat；hi : i < (l.splitWrtCompositionAux ns).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.splitWrtCompositionAux_cons`：splitWrtCompositionAux_cons (l : List 
α) (n ns) : l.splitWrtCompositionAux (n::ns) = take n l::(drop n l).splitWrtComp
ositionAux ns
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `List.drop_zero`：∀ {α : Type u} {l : List α}, List.drop 0 l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.splitAt_eq`：∀ {α : Type u_1} {i : ℕ} {l : List α}, List.splitAt i l
 = (List.take i l, List.drop i l)
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `List.drop_take`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.take j l) = List.take (j - i) (List.drop i l)
· 使用定理 `List.drop_drop`：∀ {α : Type u_1} {i j : ℕ} {l : List α}, List.drop i (Li
st.drop j l) = List.drop (j + i) l
· 使用定理 `Nat.add_sub_add_left`：∀ (k n m : ℕ), k + n - (k + m) = n - m
-/
theorem getElem_splitWrtCompositionAux (l : List α) (ns : List ℕ) {i : ℕ}
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

/-- The `i`-th sublist in the splitting of a list `l` along a composition `c`, is the slice of `l`
between the indices `c.sizeUpTo i` and `c.sizeUpTo (i+1)`, i.e., the indices in the `i`-th
block of the composition. -/
/-
**List.getElem_splitWrtComposition'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_splitWrtComposition' (l : List α) (c : Composition n) {i : Nat} (h
i : i < (l.splitWrtComposition c).length) : (l.splitWrtComposition c)[i] = (l.ta
ke (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i)
参数：l : List α；c : Composition n；hi : i < (l.splitWrtComposition c).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getElem_splitWrtCompositionAux`：getElem_splitWrtCompositionAux (l :
 List α) (ns : List Nat) {i : Nat} (hi : i < (l.splitWrtCompositionAux ns).lengt
h) : (l.splitWrtCompositi…

--- 原说明 ---
The `i`-th sublist in the splitting of a list `l` along a composition `c`, is th
e slice of `l`
between the indices `c.sizeUpTo i` and `c.sizeUpTo (i+1)`, i.e., the indices in 
the `i`-th
block of the composition.
-/
theorem getElem_splitWrtComposition' (l : List α) (c : Composition n) {i : ℕ}
    (hi : i < (l.splitWrtComposition c).length) :
    (l.splitWrtComposition c)[i] = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  getElem_splitWrtCompositionAux _ _ hi
/-
**List.getElem_splitWrtComposition** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_splitWrtComposition (l : List α) (c : Composition n) (i : Nat) (h 
: i < (l.splitWrtComposition c).length) : (l.splitWrtComposition c)[i] = (l.take
 (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i)
参数：l : List α；c : Composition n；i : Nat；h : i < (l.splitWrtComposition c).length
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getElem_splitWrtComposition'`：getElem_splitWrtComposition' (l : Lis
t α) (c : Composition n) {i : Nat} (hi : i < (l.splitWrtComposition c).length) :
 (l.splitWrtComposition…
-/
theorem getElem_splitWrtComposition (l : List α) (c : Composition n)
    (i : Nat) (h : i < (l.splitWrtComposition c).length) :
    (l.splitWrtComposition c)[i] = (l.take (c.sizeUpTo (i + 1))).drop (c.sizeUpTo i) :=
  getElem_splitWrtComposition' _ _ h
/-
**List.flatten_splitWrtCompositionAux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：flatten_splitWrtCompositionAux {ns : List Nat} : forall {l : List α}, ns.s
um = l.length -> (l.splitWrtCompositionAux ns).flatten = l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.length_eq_zero_iff`：∀ {α : Type u_1} {l : List α}, l.length = 0 ↔ l
 = []
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.splitWrtCompositionAux_cons`：splitWrtCompositionAux_cons (l : List 
α) (n ns) : l.splitWrtCompositionAux (n::ns) = take n l::(drop n l).splitWrtComp
ositionAux ns
· 使用定理 `List.length_drop`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.drop i l)
.length = l.length - i
· 使用定理 `List.sum_cons`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α] {a : α} {
l : List α}, (a :: l).sum = a + l.sum
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem flatten_splitWrtCompositionAux {ns : List ℕ} :
    ∀ {l : List α}, ns.sum = l.length → (l.splitWrtCompositionAux ns).flatten = l := by
  induction ns with
  | nil => exact fun h ↦ (length_eq_zero_iff.1 h.symm).symm
  | cons n ns IH =>
    intro l h; rw [sum_cons] at h
    simp only [splitWrtCompositionAux_cons]; dsimp
    rw [IH]
    · simp
    · rw [length_drop, ← h, add_tsub_cancel_left]

/-- If one splits a list along a composition, and then flattens the sublists, one gets back the
original list. -/
@[simp]
/-
**List.flatten_splitWrtComposition** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：flatten_splitWrtComposition (l : List α) (c : Composition l.length) : (l.s
plitWrtComposition c).flatten = l
参数：l : List α；c : Composition l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.flatten_splitWrtCompositionAux`：flatten_splitWrtCompositionAux {ns 
: List Nat} : forall {l : List α}, ns.sum = l.length -> (l.splitWrtCompositionAu
x ns).flatten = l
· 使用定理 `Composition.blocks_sum`：∀ {n : ℕ} (self : Composition n), self.blocks.su
m = n

--- 原说明 ---
If one splits a list along a composition, and then flattens the sublists, one ge
ts back the
original list.
-/
theorem flatten_splitWrtComposition (l : List α) (c : Composition l.length) :
    (l.splitWrtComposition c).flatten = l :=
  flatten_splitWrtCompositionAux c.blocks_sum

/-- If one joins a list of lists and then splits the flattening along the right composition,
one gets back the original list of lists. -/
@[simp]
/-
**List.splitWrtComposition_flatten** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitWrtComposition_flatten (L : List (List α)) (c : Composition L.flatten
.length) (h : map length L = c.blocks) : splitWrtComposition (flatten L) c = L
参数：L : List (List α)；c : Composition L.flatten.length；h : map length L = c.block
s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.flatten_splitWrtComposition`：flatten_splitWrtComposition (l : List 
α) (c : Composition l.length) : (l.splitWrtComposition c).flatten = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_length_splitWrtComposition`：map_length_splitWrtComposition (l :
 List α) (c : Composition l.length) : map length (l.splitWrtComposition c) = c.b
locks

--- 原说明 ---
If one joins a list of lists and then splits the flattening along the right comp
osition,
one gets back the original list of lists.
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
/-- Bijection between compositions of `n` and subsets of `{0, ..., n-2}`, defined by
considering the restriction of the subset to `{1, ..., n-1}` and shifting to the left by one. -/
/-
**compositionAsSetEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：compositionAsSetEquiv (n : Nat) : CompositionAsSet n ≃ Finset (Fin (n - 1)
) where toFun c
参数：n : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
Bijection between compositions of `n` and subsets of `{0, ..., n-2}`, defined by
considering the restriction of the subset to `{1, ..., n-1}` and shifting to the
 left by one.
-/
def compositionAsSetEquiv (n : ℕ) : CompositionAsSet n ≃ Finset (Fin (n - 1)) where
  toFun c :=
    { i : Fin (n - 1) |
        (⟨1 + (i : ℕ), by lia⟩ : Fin n.succ) ∈ c.boundaries }.toFinset
  invFun s :=
    { boundaries :=
        { i : Fin n.succ |
            i = 0 ∨ i = Fin.last n ∨ ∃ (j : Fin (n - 1)) (_hj : j ∈ s), (i : ℕ) = j + 1 }.toFinset
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
      obtain ⟨k, rfl⟩ : ∃ k : Fin n, k.castSucc = j := by
        simpa [Fin.exists_castSucc_eq] using! i_ne_last
      use k
      simpa using! i_mem
  right_inv := by
    intro s
    ext i
    have : (i : ℕ) + 1 ≠ n := by lia
    simp_rw [add_comm, Fin.ext_iff, Fin.val_zero, Fin.val_last, exists_prop, Set.toFinset_ofPred,
      Finset.mem_filter_univ, reduceCtorEq, this, false_or, add_left_inj, ← Fin.ext_iff,
      exists_eq_right']
/-
**compositionAsSetFintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：compositionAsSetFintype (n : Nat) : Fintype (CompositionAsSet n)
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance compositionAsSetFintype (n : ℕ) : Fintype (CompositionAsSet n) :=
  Fintype.ofEquiv _ (compositionAsSetEquiv n).symm
/-
**compositionAsSet_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compositionAsSet_card (n : Nat) : Fintype.card (CompositionAsSet n) = 2 ^ 
(n - 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_finset`：Fintype.card_finset [Fintype α] : Fintype.card (Fin
set α) = 2 ^ Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem compositionAsSet_card (n : ℕ) : Fintype.card (CompositionAsSet n) = 2 ^ (n - 1) := by
  have : Fintype.card (Finset (Fin (n - 1))) = 2 ^ (n - 1) := by simp
  rw [← this]
  exact Fintype.card_congr (compositionAsSetEquiv n)

namespace CompositionAsSet

variable (c : CompositionAsSet n)

/-
**CompositionAsSet.boundaries_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `CompositionAsS
et`。
形式化陈述：boundaries_nonempty : c.boundaries.Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CompositionAsSet.zero_mem`：∀ {n : ℕ} (self : CompositionAsSet n), 0 ∈ se
lf.boundaries
-/
theorem boundaries_nonempty : c.boundaries.Nonempty :=
  ⟨0, c.zero_mem⟩
/-
**CompositionAsSet.card_boundaries_pos** 是 Mathlib 中的一个定理，位于命名空间 `CompositionAsS
et`。
形式化陈述：card_boundaries_pos : 0 < Finset.card c.boundaries
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `CompositionAsSet.boundaries_nonempty`：boundaries_nonempty : c.boundaries
.Nonempty
-/
theorem card_boundaries_pos : 0 < Finset.card c.boundaries :=
  Finset.card_pos.mpr c.boundaries_nonempty

/-- Number of blocks in a `CompositionAsSet`. -/
/-
**CompositionAsSet.length** 是 Mathlib 中的一个定义，位于命名空间 `CompositionAsSet`。
形式化陈述：length : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Number of blocks in a `CompositionAsSet`.
-/
def length : ℕ :=
  Finset.card c.boundaries - 1
/-
**CompositionAsSet.card_boundaries_eq_succ_length** 是 Mathlib 中的一个定理，位于命名空间 `Com
positionAsSet`。
形式化陈述：card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_eq_iff_eq_add_of_le`：tsub_eq_iff_eq_add_of_le (h : b <= a) : a - b 
= c ↔ a = c + b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `CompositionAsSet.card_boundaries_pos`：card_boundaries_pos : 0 < Finset.c
ard c.boundaries
-/
theorem card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 :=
  (tsub_eq_iff_eq_add_of_le (Nat.succ_le_of_lt c.card_boundaries_pos)).mp rfl
/-
**CompositionAsSet.length_lt_card_boundaries** 是 Mathlib 中的一个定理，位于命名空间 `Composit
ionAsSet`。
形式化陈述：length_lt_card_boundaries : c.length < c.boundaries.card
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompositionAsSet.card_boundaries_eq_succ_length`：card_boundaries_eq_succ
_length : c.boundaries.card = c.length + 1
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
-/
theorem length_lt_card_boundaries : c.length < c.boundaries.card := by
  rw [c.card_boundaries_eq_succ_length]
  exact Nat.lt_add_one _
/-
**CompositionAsSet.lt_length** 是 Mathlib 中的一个定理，位于命名空间 `CompositionAsSet`。
形式化陈述：lt_length (i : Fin c.length) : (i : Nat) + 1 < c.boundaries.card
参数：i : Fin c.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_tsub_iff_right`：lt_tsub_iff_right : a < b - c ↔ a + c < b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem lt_length (i : Fin c.length) : (i : ℕ) + 1 < c.boundaries.card :=
  lt_tsub_iff_right.mp i.2
/-
**CompositionAsSet.lt_length'** 是 Mathlib 中的一个定理，位于命名空间 `CompositionAsSet`。
形式化陈述：lt_length' (i : Fin c.length) : (i : Nat) < c.boundaries.card
参数：i : Fin c.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `CompositionAsSet.lt_length`：lt_length (i : Fin c.length) : (i : Nat) + 1
 < c.boundaries.card
-/
theorem lt_length' (i : Fin c.length) : (i : ℕ) < c.boundaries.card :=
  lt_of_le_of_lt (Nat.le_succ i) (c.lt_length i)

/-- Canonical increasing bijection from `Fin c.boundaries.card` to `c.boundaries`. -/
/-
**CompositionAsSet.boundary** 是 Mathlib 中的一个定义，位于命名空间 `CompositionAsSet`。
形式化陈述：boundary : Fin c.boundaries.card ↪o Fin (n + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical increasing bijection from `Fin c.boundaries.card` to `c.boundaries`.
-/
def boundary : Fin c.boundaries.card ↪o Fin (n + 1) :=
  c.boundaries.orderEmbOfFin rfl

@[simp]
/-
**CompositionAsSet.boundary_zero** 是 Mathlib 中的一个定理，位于命名空间 `CompositionAsSet`。
形式化陈述：boundary_zero : (c.boundary ⟨0, c.card_boundaries_pos⟩ : Fin (n + 1)) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompositionAsSet.card_boundaries_pos`：card_boundaries_pos : 0 < Finset.c
ard c.boundaries
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompositionAsSet.boundary.eq_1`：∀ {n : ℕ} (c : CompositionAsSet n), c.bo
undary = c.boundaries.orderEmbOfFin ⋯
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.orderEmbOfFin_zero`：orderEmbOfFin_zero {s : Finset α} {k : Nat} (
h : s.card = k) (hz : 0 < k) : orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (
h.symm ▸ hz))
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用定理 `CompositionAsSet.zero_mem`：∀ {n : ℕ} (self : CompositionAsSet n), 0 ∈ se
lf.boundaries
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
-/
theorem boundary_zero : (c.boundary ⟨0, c.card_boundaries_pos⟩ : Fin (n + 1)) = 0 := by
  rw [boundary, Finset.orderEmbOfFin_zero rfl c.card_boundaries_pos]
  exact le_antisymm (Finset.min'_le _ _ c.zero_mem) (Fin.zero_le _)

@[simp]
/-
**CompositionAsSet.boundary_length** 是 Mathlib 中的一个定理，位于命名空间 `CompositionAsSet`。
形式化陈述：boundary_length : c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = Fin
.last n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompositionAsSet.length_lt_card_boundaries`：length_lt_card_boundaries : 
c.length < c.boundaries.card
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `CompositionAsSet.card_boundaries_pos`：card_boundaries_pos : 0 < Finset.c
ard c.boundaries
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `CompositionAsSet.getLast_mem`：∀ {n : ℕ} (self : CompositionAsSet n), Fin
.last n ∈ self.boundaries
· 使用定理 `Fin.le_last`：∀ {n : ℕ} (i : Fin (n + 1)), i ≤ Fin.last n
· 使用定理 `Finset.orderEmbOfFin_last`：orderEmbOfFin_last {s : Finset α} {k : Nat} (
h : s.card = k) (hz : 0 < k) : orderEmbOfFin s h ⟨k - 1, Nat.sub_lt hz (Nat.succ
_pos 0)⟩ = s.ma…
-/
theorem boundary_length : c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = Fin.last n := by
  convert! Finset.orderEmbOfFin_last rfl c.card_boundaries_pos
  exact le_antisymm (Finset.le_max' _ _ c.getLast_mem) (Fin.le_last _)

/-- Size of the `i`-th block in a `CompositionAsSet`, seen as a function on `Fin c.length`. -/
/-
**CompositionAsSet.blocksFun** 是 Mathlib 中的一个定义，位于命名空间 `CompositionAsSet`。
形式化陈述：blocksFun (i : Fin c.length) : Nat
参数：i : Fin c.length。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompositionAsSet.lt_length`：lt_length (i : Fin c.length) : (i : Nat) + 1
 < c.boundaries.card
· 使用定理 `CompositionAsSet.lt_length'`：lt_length' (i : Fin c.length) : (i : Nat) <
 c.boundaries.card

--- 原说明 ---
Size of the `i`-th block in a `CompositionAsSet`, seen as a function on `Fin c.l
ength`.
-/
def blocksFun (i : Fin c.length) : ℕ :=
  c.boundary ⟨(i : ℕ) + 1, c.lt_length i⟩ - c.boundary ⟨i, c.lt_length' i⟩
/-
**CompositionAsSet.blocksFun_pos** 是 Mathlib 中的一个定理，位于命名空间 `CompositionAsSet`。
形式化陈述：blocksFun_pos (i : Fin c.length) : 0 < c.blocksFun i
参数：i : Fin c.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CompositionAsSet.lt_length`：lt_length (i : Fin c.length) : (i : Nat) + 1
 < c.boundaries.card
· 使用定理 `CompositionAsSet.lt_length'`：lt_length' (i : Fin c.length) : (i : Nat) <
 c.boundaries.card
· 使用定理 `lt_tsub_iff_left`：lt_tsub_iff_left : a < b - c ↔ c + a < b
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
-/
theorem blocksFun_pos (i : Fin c.length) : 0 < c.blocksFun i :=
  haveI : (⟨i, c.lt_length' i⟩ : Fin c.boundaries.card) < ⟨i + 1, c.lt_length i⟩ :=
    Nat.lt_succ_self _
  lt_tsub_iff_left.mpr ((c.boundaries.orderEmbOfFin rfl).strictMono this)

/-- List of the sizes of the blocks in a `CompositionAsSet`. -/
/-
**CompositionAsSet.blocks** 是 Mathlib 中的一个定义，位于命名空间 `CompositionAsSet`。
形式化陈述：blocks (c : CompositionAsSet n) : List Nat
参数：c : CompositionAsSet n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
List of the sizes of the blocks in a `CompositionAsSet`.
-/
def blocks (c : CompositionAsSet n) : List ℕ :=
  ofFn c.blocksFun

@[simp]
/-
**CompositionAsSet.blocks_length** 是 Mathlib 中的一个定理，位于命名空间 `CompositionAsSet`。
形式化陈述：blocks_length : c.blocks.length = c.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
-/
theorem blocks_length : c.blocks.length = c.length :=
  length_ofFn

set_option backward.isDefEq.respectTransparency false in
/-
**CompositionAsSet.blocks_partial_sum** 是 Mathlib 中的一个定理，位于命名空间 `CompositionAsSe
t`。
形式化陈述：blocks_partial_sum {i : Nat} (h : i < c.boundaries.card) : (c.blocks.take 
i).sum = c.boundary ⟨i, h⟩
参数：h : i < c.boundaries.card。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CompositionAsSet.boundary_zero`：boundary_zero : (c.boundary ⟨0, c.card_b
oundaries_pos⟩ : Fin (n + 1)) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `CompositionAsSet.card_boundaries_eq_succ_length`：card_boundaries_eq_succ
_length : c.boundaries.card = c.length + 1
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `List.sum_take_succ`：∀ {M : Type u_4} [inst : AddMonoid M] (L : List M) (
i : ℕ) (p : i < L.length),   (List.take (i + 1) L).sum = (List.take i L).sum + L
[i]
· 使用定理 `CompositionAsSet.lt_length`：lt_length (i : Fin c.length) : (i : Nat) + 1
 < c.boundaries.card
· 使用定理 `CompositionAsSet.lt_length'`：lt_length' (i : Fin c.length) : (i : Nat) <
 c.boundaries.card
· 使用定理 `List.getElem_ofFn`：∀ {n : ℕ} {α : Type u_1} {i : ℕ} {f : Fin n → α} (h :
 i < (List.ofFn f).length), (List.ofFn f)[i] = f ⟨i, ⋯⟩
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
-/
theorem blocks_partial_sum {i : ℕ} (h : i < c.boundaries.card) :
    (c.blocks.take i).sum = c.boundary ⟨i, h⟩ := by
  induction i with
  | zero => simp
  | succ i IH =>
    have A : i < c.blocks.length := by
      rw [c.card_boundaries_eq_succ_length] at h
      simp [blocks, Nat.lt_of_succ_lt_succ h]
    have B : i < c.boundaries.card := lt_of_lt_of_le A (by simp [blocks, length])
    rw [sum_take_succ _ _ A, IH B]
    simp [blocks, blocksFun]
/-
**CompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq** 是 Mathlib 中的一个
定理，位于命名空间 `CompositionAsSet`。
形式化陈述：mem_boundaries_iff_exists_blocks_sum_take_eq {j : Fin (n + 1)} : j in c.bo
undaries ↔ exists i < c.boundaries.card, (c.blocks.take i).sum = j
参数：n + 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `CompositionAsSet.blocks_partial_sum`：blocks_partial_sum {i : Nat} (h : i
 < c.boundaries.card) : (c.blocks.take i).sum = c.boundary ⟨i, h⟩
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b
-/
theorem mem_boundaries_iff_exists_blocks_sum_take_eq {j : Fin (n + 1)} :
    j ∈ c.boundaries ↔ ∃ i < c.boundaries.card, (c.blocks.take i).sum = j := by
  constructor
  · intro hj
    rcases (c.boundaries.orderIsoOfFin rfl).surjective ⟨j, hj⟩ with ⟨i, hi⟩
    rw [Subtype.ext_iff, Subtype.coe_mk] at hi
    refine ⟨i.1, i.2, ?_⟩
    dsimp at hi
    rw [← hi, c.blocks_partial_sum i.2]
    rfl
  · rintro ⟨i, hi, H⟩
    convert! (c.boundaries.orderIsoOfFin rfl ⟨i, hi⟩).2
    have : c.boundary ⟨i, hi⟩ = j := by rwa [Fin.ext_iff, ← c.blocks_partial_sum hi]
    exact this.symm
/-
**CompositionAsSet.blocks_sum** 是 Mathlib 中的一个定理，位于命名空间 `CompositionAsSet`。
形式化陈述：blocks_sum : c.blocks.sum = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.take_of_length_le`：∀ {α : Type u_1} {i : ℕ} {l : List α}, l.length 
≤ i → List.take i l = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CompositionAsSet.length_lt_card_boundaries`：length_lt_card_boundaries : 
c.length < c.boundaries.card
· 使用定理 `CompositionAsSet.blocks_partial_sum`：blocks_partial_sum {i : Nat} (h : i
 < c.boundaries.card) : (c.blocks.take i).sum = c.boundary ⟨i, h⟩
· 使用定理 `CompositionAsSet.boundary_length`：boundary_length : c.boundary ⟨c.length
, c.length_lt_card_boundaries⟩ = Fin.last n
-/
theorem blocks_sum : c.blocks.sum = n := by
  have : c.blocks.take c.length = c.blocks := take_of_length_le (by simp [blocks])
  rw [← this, c.blocks_partial_sum c.length_lt_card_boundaries, c.boundary_length]
  rfl

/-- Associating a `Composition n` to a `CompositionAsSet n`, by registering the sizes of the
blocks as a list of positive integers. -/
/-
**CompositionAsSet.toComposition** 是 Mathlib 中的一个定义，位于命名空间 `CompositionAsSet`。
形式化陈述：toComposition : Composition n where blocks
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CompositionAsSet.blocks_sum`：blocks_sum : c.blocks.sum = n

--- 原说明 ---
Associating a `Composition n` to a `CompositionAsSet n`, by registering the size
s of the
blocks as a list of positive integers.
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
/-
**Composition.toCompositionAsSet_length** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Composition.toCompositionAsSet_length (c : Composition n) : c.toCompositio
nAsSet.length = c.length
参数：c : Composition n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Composition.card_boundaries_eq_succ_length`：card_boundaries_eq_succ_leng
th : c.boundaries.card = c.length + 1
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Equivalence between compositions and compositions as sets

In this section, we explain how to go back and forth between a `Composition` and
 a
`CompositionAsSet`, by showing that their `blocks` and `length` and `boundaries`
 correspond to
each other, and construct an equivalence between them called `compositionEquiv`.
-/
theorem Composition.toCompositionAsSet_length (c : Composition n) :
    c.toCompositionAsSet.length = c.length := by
  simp [Composition.toCompositionAsSet, CompositionAsSet.length, c.card_boundaries_eq_succ_length]

@[simp]
/-
**CompositionAsSet.toComposition_length** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompositionAsSet.toComposition_length (c : CompositionAsSet n) : c.toCompo
sition.length = c.length
参数：c : CompositionAsSet n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompositionAsSet.blocks_length`：blocks_length : c.blocks.length = c.leng
th
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem CompositionAsSet.toComposition_length (c : CompositionAsSet n) :
    c.toComposition.length = c.length := by
  simp [CompositionAsSet.toComposition, Composition.length]

@[simp]
/-
**Composition.toCompositionAsSet_blocks** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Composition.toCompositionAsSet_blocks (c : Composition n) : c.toCompositio
nAsSet.blocks = c.blocks
参数：c : Composition n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CompositionAsSet.blocks_length`：blocks_length : c.blocks.length = c.leng
th
· 使用定理 `Composition.toCompositionAsSet_length`：Composition.toCompositionAsSet_le
ngth (c : Composition n) : c.toCompositionAsSet.length = c.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CompositionAsSet.card_boundaries_eq_succ_length`：card_boundaries_eq_succ
_length : c.boundaries.card = c.length + 1
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Composition.card_boundaries_eq_succ_length`：card_boundaries_eq_succ_leng
th : c.boundaries.card = c.length + 1
· 使用定理 `CompositionAsSet.blocks_partial_sum`：blocks_partial_sum {i : Nat} (h : i
 < c.boundaries.card) : (c.blocks.take i).sum = c.boundary ⟨i, h⟩
· 使用定理 `CompositionAsSet.boundary.eq_1`：∀ {n : ℕ} (c : CompositionAsSet n), c.bo
undary = c.boundaries.orderEmbOfFin ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Composition.sizeUpTo.eq_1`：∀ {n : ℕ} (c : Composition n) (i : ℕ), c.size
UpTo i = (List.take i c.blocks).sum
· 使用定理 `Composition.orderEmbOfFin_boundaries`：orderEmbOfFin_boundaries : c.bound
aries.orderEmbOfFin c.card_boundaries_eq_succ_length = c.boundary
· 使用定理 `List.eq_of_sum_take_eq`：∀ {M : Type u_4} [inst : AddLeftCancelMonoid M] 
{L L' : List M},   L.length = L'.length → (∀ i ≤ L.length, (List.take i L).sum =
 (List.take …
-/
theorem Composition.toCompositionAsSet_blocks (c : Composition n) :
    c.toCompositionAsSet.blocks = c.blocks := by
  let d := c.toCompositionAsSet
  change d.blocks = c.blocks
  have length_eq : d.blocks.length = c.blocks.length := by simp [d, blocks_length]
  suffices H : ∀ i ≤ d.blocks.length, (d.blocks.take i).sum = (c.blocks.take i).sum from
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
  rw [d.blocks_partial_sum i_lt, CompositionAsSet.boundary, ← Composition.sizeUpTo, B, A,
    c.orderEmbOfFin_boundaries]

@[simp]
/-
**CompositionAsSet.toComposition_blocks** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompositionAsSet.toComposition_blocks (c : CompositionAsSet n) : c.toCompo
sition.blocks = c.blocks
参数：c : CompositionAsSet n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem CompositionAsSet.toComposition_blocks (c : CompositionAsSet n) :
    c.toComposition.blocks = c.blocks :=
  rfl

@[simp]
/-
**CompositionAsSet.toComposition_boundaries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompositionAsSet.toComposition_boundaries (c : CompositionAsSet n) : c.toC
omposition.boundaries = c.boundaries
参数：c : CompositionAsSet n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.mk.injEq`：∀ {n : ℕ} (val : ℕ) (isLt : val < n) (val_1 : ℕ) (isLt_1 :
 val_1 < n), (⟨val, isLt⟩ = ⟨val_1, isLt_1⟩) = (val = val_1)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CompositionAsSet.toComposition_length`：CompositionAsSet.toComposition_le
ngth (c : CompositionAsSet n) : c.toComposition.length = c.length
· 使用定理 `CompositionAsSet.mem_boundaries_iff_exists_blocks_sum_take_eq`：mem_bound
aries_iff_exists_blocks_sum_take_eq {j : Fin (n + 1)} : j in c.boundaries ↔ exis
ts i < c.boundaries.card, (c.blocks.take i).sum = j
· 使用定理 `CompositionAsSet.card_boundaries_eq_succ_length`：card_boundaries_eq_succ
_length : c.boundaries.card = c.length + 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem CompositionAsSet.toComposition_boundaries (c : CompositionAsSet n) :
    c.toComposition.boundaries = c.boundaries := by
  ext ⟨j, hj⟩
  simp [c.mem_boundaries_iff_exists_blocks_sum_take_eq, Composition.boundaries,
    c.card_boundaries_eq_succ_length, Composition.boundary, Composition.sizeUpTo, Fin.exists_iff]

@[simp]
/-
**Composition.toCompositionAsSet_boundaries** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Composition.toCompositionAsSet_boundaries (c : Composition n) : c.toCompos
itionAsSet.boundaries = c.boundaries
参数：c : Composition n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Composition.toCompositionAsSet_boundaries (c : Composition n) :
    c.toCompositionAsSet.boundaries = c.boundaries :=
  rfl

/-- Equivalence between `Composition n` and `CompositionAsSet n`. -/
/-
**compositionEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：compositionEquiv (n : Nat) : Composition n ≃ CompositionAsSet n where toFu
n c
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equivalence between `Composition n` and `CompositionAsSet n`.
-/
def compositionEquiv (n : ℕ) : Composition n ≃ CompositionAsSet n where
  toFun c := c.toCompositionAsSet
  invFun c := c.toComposition
  left_inv c := by
    ext1
    exact c.toCompositionAsSet_blocks
  right_inv c := by
    ext1
    exact c.toComposition_boundaries
/-
**compositionFintype** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：compositionFintype (n : Nat) : Fintype (Composition n)
参数：n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance compositionFintype (n : ℕ) : Fintype (Composition n) :=
  Fintype.ofEquiv _ (compositionEquiv n).symm
/-
**composition_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：composition_card (n : Nat) : Fintype.card (Composition n) = 2 ^ (n - 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `compositionAsSet_card`：compositionAsSet_card (n : Nat) : Fintype.card (C
ompositionAsSet n) = 2 ^ (n - 1)
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
-/
theorem composition_card (n : ℕ) : Fintype.card (Composition n) = 2 ^ (n - 1) := by
  rw [← compositionAsSet_card n]
  exact Fintype.card_congr (compositionEquiv n)
