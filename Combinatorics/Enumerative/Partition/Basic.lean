/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Tactic.ApplyFun

/-!
# Partitions

A partition of a natural number `n` is a way of writing `n` as a sum of positive integers, where the
order does not matter: two sums that differ only in the order of their summands are considered the
same partition. This notion is closely related to that of a composition of `n`, but in a composition
of `n` the order does matter.
A summand of the partition is called a part.

## Main functions

* `p : Partition n` is a structure, made of a multiset of integers which are all positive and
  add up to `n`.

## Implementation details

The main motivation for this structure and its API is to show Euler's partition theorem, and
related results.

The representation of a partition as a multiset is very handy as multisets are very flexible and
already have a well-developed API.

## TODO

Link this to Young diagrams.

## Tags

Partition

## References

<https://en.wikipedia.org/wiki/Partition_(number_theory)>
-/

@[expose] public section

assert_not_exists Field

open Multiset

namespace Nat

/-- A partition of `n` is a multiset of positive integers summing to `n`. -/
@[ext]
/--
Definition of `Partition` / `Partition` 的定义

English:
structure Partition
  parameters: (n : Nat)
  axioms and operations (3):
    - parts : Multiset Nat
    - parts_pos : forall {i}, i in parts -> 0 < i
    - parts_sum : parts.sum = n

中文:
结构 分拆
  参数: (n : 自然数)
  公理与运算 (3 个):
    - parts : Multiset 自然数
    - parts_pos : 对任意 {i}, i in parts -> 0 < i
    - parts_sum : parts.求和 = n
-/
structure Partition (n : Nat) where
  /-- positive integers summing to `n` -/
  parts : Multiset Nat
  /-- proof that the `parts` are positive -/
  parts_pos : forall {i}, i in parts -> 0 < i
  /-- proof that the `parts` sum to `n` -/
  parts_sum : parts.sum = n
deriving DecidableEq

namespace Partition

attribute [grind ->] parts_pos

@[grind ->]
/--
theorem `le_of_mem_parts` / 定理 `le_of_mem_parts`

English:
theorem le_of_mem_parts
  given: {n : Nat} {p : Partition n} {m : Nat} (h : m in p.parts)
  statement: m <= n
  proof: by
  simpa [p.parts_sum] using Multiset.le_sum_of_mem h

中文:
定理 le_of_mem_parts
  条件: {n : 自然数} {p : 分拆 n} {m : 自然数} (h : m in p.parts)
  结论: m <= n
  证明: by
  simpa [p.parts_sum] using Multiset.le_sum_of_mem h

Depends on / 依赖: Multiset, Multiset.le_sum_of_mem, le_sum_of_mem, p.parts_sum, parts_sum
-/
theorem le_of_mem_parts {n : Nat} {p : Partition n} {m : Nat} (h : m in p.parts) : m <= n := by
  simpa [p.parts_sum] using Multiset.le_sum_of_mem h

/-- A composition induces a partition (just convert the list to a multiset). -/
@[simps]
/--
Definition of `ofComposition` / `ofComposition` 的定义

English:
definition ofComposition
  signature: (n : Nat) (c : Composition n)
  body: c.blocks
  parts_pos hi := c.blocks_pos hi
  parts_sum := by rw [Multiset.sum_coe, c.blocks_sum]

中文:
定义 ofComposition
  签名: (n : 自然数) (c : 余mposition n)
  定义体: c.blocks
  parts_pos hi := c.blocks_pos hi
  parts_sum := by rw [Multiset.sum_coe, c.blocks_sum]

Depends on / 依赖: blocks, c.blocks
-/
def ofComposition (n : Nat) (c : Composition n) : Partition n where
  parts := c.blocks
  parts_pos hi := c.blocks_pos hi
  parts_sum := by rw [Multiset.sum_coe, c.blocks_sum]

/--
theorem `ofComposition_surj` / 定理 `ofComposition_surj`

English:
theorem ofComposition_surj
  given: {n : Nat}
  statement: Function.Surjective (ofComposition n)
  proof: by
  rintro ⟨b, hb₁, hb₂⟩
  induction b using Quotient.inductionOn with | _ b => ?_
  exact ⟨⟨b, hb₁, by simpa using hb₂⟩, Partition.ext rfl⟩

中文:
定理 ofComposition_surj
  条件: {n : 自然数}
  结论: 函数.满射 (ofComposition n)
  证明: by
  rintro ⟨b, hb₁, hb₂⟩
  induction b using Quotient.inductionOn with | _ b => ?_
  exact ⟨⟨b, hb₁, by simpa using hb₂⟩, Partition.ext rfl⟩

Depends on / 依赖: Partition, Partition.ext, Quotient, Quotient.inductionOn, inductionOn
-/
theorem ofComposition_surj {n : Nat} : Function.Surjective (ofComposition n) := by
  rintro ⟨b, hb₁, hb₂⟩
  induction b using Quotient.inductionOn with | _ b => ?_
  exact ⟨⟨b, hb₁, by simpa using hb₂⟩, Partition.ext rfl⟩

-- The argument `n` is kept explicit here since it is useful in tactic mode proofs to generate the
-- proof obligation `l.sum = n`.
/-- Given a multiset which sums to `n`, construct a partition of `n` with the same multiset, but
without the zeros.
-/
@[simps]
/--
Definition of `ofSums` / `ofSums` 的定义

English:
definition ofSums
  signature: (n : Nat) (l : Multiset Nat) (hl : l.sum = n)
  body: l.filter (· != 0)
  parts_pos hi := (of_mem_filter hi).bot_lt
  parts_sum := by
    have lz : (l.filter (· = 0)).sum = 0 := by simp [sum_eq_zero_iff]
    rwa [← filter_add_not (· = 0) l, sum_add, lz, zero_add] at hl

中文:
定义 ofSums
  签名: (n : 自然数) (l : Multiset 自然数) (hl : l.求和 = n)
  定义体: l.filter (· != 0)
  parts_pos hi := (of_mem_filter hi).bot_lt
  parts_sum := by
    have lz : (l.filter (· = 0)).sum = 0 := by simp [sum_eq_zero_iff]
    rwa [← filter_add_not (· = 0) l, sum_add, lz, zero_add] at hl

Depends on / 依赖: filter, l.filter
-/
def ofSums (n : Nat) (l : Multiset Nat) (hl : l.sum = n) : Partition n where
  parts := l.filter (· != 0)
  parts_pos hi := (of_mem_filter hi).bot_lt
  parts_sum := by
    have lz : (l.filter (· = 0)).sum = 0 := by simp [sum_eq_zero_iff]
    rwa [← filter_add_not (· = 0) l, sum_add, lz, zero_add] at hl

/-- A `Multiset ℕ` induces a partition on its sum. -/
@[simps!]
/--
Definition of `ofMultiset` / `ofMultiset` 的定义

English:
definition ofMultiset
  signature: (l : Multiset Nat)
  body: ofSums _ l rfl

中文:
定义 ofMultiset
  签名: (l : Multiset 自然数)
  定义体: ofSums _ l rfl

Depends on / 依赖: ofSums
-/
def ofMultiset (l : Multiset Nat) : Partition l.sum := ofSums _ l rfl

/--
Definition of `ofSym` / `ofSym` 的定义

English:
definition ofSym
  signature: {n : Nat} {σ : Type*} (s : Sym σ n) [DecidableEq σ]
  body: s.1.dedup.map s.1.count
  parts_pos := by simp [Multiset.count_pos]
  parts_sum := by
    change ∑ a in s.1.toFinset, count a s.1 = n
    rw [toFinset_sum_count_eq]
    exact s.2

中文:
定义 ofSym
  签名: {n : 自然数} {σ : 类型} (s : Sym σ n) [DecidableEq σ]
  定义体: s.1.dedup.map s.1.count
  parts_pos := by simp [Multiset.count_pos]
  parts_sum := by
    change ∑ a in s.1.toFinset, count a s.1 = n
    rw [toFinset_sum_count_eq]
    exact s.2

Depends on / 依赖: dedup.map
-/
def ofSym {n : Nat} {σ : Type*} (s : Sym σ n) [DecidableEq σ] : n.Partition where
  parts := s.1.dedup.map s.1.count
  parts_pos := by simp [Multiset.count_pos]
  parts_sum := by
    change ∑ a in s.1.toFinset, count a s.1 = n
    rw [toFinset_sum_count_eq]
    exact s.2

variable {n : Nat} {σ τ : Type*} [DecidableEq σ] [DecidableEq τ]

/--
lemma `ofSym_map` / 引理 `ofSym_map`

English:
lemma ofSym_map
  given: (e : σ ≃ τ) (s : Sym σ n)
  proof: by
  simp only [ofSym, Sym.val_eq_coe, Sym.coe_map, mk.injEq]
  rw [Multiset.dedup_map_of_injective e.injective]
  simp only [map_map, Function.comp_apply]
  congr; funext i
  rw [← Multiset.count_map_eq_count' e _ e.injective]

中文:
引理 ofSym_map
  条件: (e : σ ≃ τ) (s : Sym σ n)
  证明: by
  simp only [ofSym, Sym.val_eq_coe, Sym.coe_map, mk.injEq]
  rw [Multiset.dedup_map_of_injective e.injective]
  simp only [map_map, Function.comp_apply]
  congr; funext i
  rw [← Multiset.count_map_eq_count' e _ e.injective]
-/
@[simp] lemma ofSym_map (e : σ ≃ τ) (s : Sym σ n) :
    ofSym (s.map e) = ofSym s := by
  simp only [ofSym, Sym.val_eq_coe, Sym.coe_map, mk.injEq]
  rw [Multiset.dedup_map_of_injective e.injective]
  simp only [map_map, Function.comp_apply]
  congr; funext i
  rw [← Multiset.count_map_eq_count' e _ e.injective]

/--
Definition of `ofSymShapeEquiv` / `ofSymShapeEquiv` 的定义

English:
definition ofSymShapeEquiv
  signature: (μ : Partition n) (e : σ ≃ τ)
  body: fun x => ⟨Sym.equivCongr e x, by simp [ofSym_map, x.2]⟩
  invFun := fun x => ⟨Sym.equivCongr e.symm x, by simp [ofSym_map, x.2]⟩
  left_inv := by intro x; simp
  right_inv := by intro x; simp

中文:
定义 ofSymShapeEquiv
  签名: (μ : 分拆 n) (e : σ ≃ τ)
  定义体: fun x => ⟨Sym.equivCongr e x, by simp [ofSym_map, x.2]⟩
  invFun := fun x => ⟨Sym.equivCongr e.symm x, by simp [ofSym_map, x.2]⟩
  left_inv := by intro x; simp
  right_inv := by intro x; simp

Depends on / 依赖: Sym.equivCongr, equivCongr, ofSym_map
-/
def ofSymShapeEquiv (μ : Partition n) (e : σ ≃ τ) :
    {x : Sym σ n // ofSym x = μ} ≃ {x : Sym τ n // ofSym x = μ} where
  toFun := fun x => ⟨Sym.equivCongr e x, by simp [ofSym_map, x.2]⟩
  invFun := fun x => ⟨Sym.equivCongr e.symm x, by simp [ofSym_map, x.2]⟩
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/--
Definition of `toFinsuppAntidiag` / `toFinsuppAntidiag` 的定义

English:
definition toFinsuppAntidiag
  signature: {n : Nat} (p : Partition n)
  body: p.parts.count m * m
  support := p.parts.toFinset
  mem_support_toFun m := by
    suffices m in p.parts -> m != 0 by simpa
    grind

中文:
定义 toFinsuppAntidiag
  签名: {n : 自然数} (p : 分拆 n)
  定义体: p.parts.count m * m
  support := p.parts.toFinset
  mem_support_toFun m := by
    suffices m in p.parts -> m != 0 by simpa
    grind

Depends on / 依赖: p.parts.count
-/
def toFinsuppAntidiag {n : Nat} (p : Partition n) : Nat ->₀ Nat where
  toFun m := p.parts.count m * m
  support := p.parts.toFinset
  mem_support_toFun m := by
    suffices m in p.parts -> m != 0 by simpa
    grind

/--
theorem `toFinsuppAntidiag_injective` / 定理 `toFinsuppAntidiag_injective`

English:
theorem toFinsuppAntidiag_injective
  given: (n : Nat)
  statement: Function.Injective (toFinsuppAntidiag (n := n))
  proof: by
  unfold toFinsuppAntidiag
  intro p q h
  rw [Finsupp.mk.injEq] at h
  obtain ⟨hfinset, hcount⟩ := h
  rw [Nat.Partition.ext_iff]; rw [Multiset.ext]
  intro m
  obtain rfl | h0 := Nat.eq_zero_or_pos m
  · grind [Multiset.count_eq_zero]
· exact Nat.eq_of_mul_eq_mul_right h0 funext_iff.mp hcount m

中文:
定理 toFinsuppAntidiag_injective
  条件: (n : 自然数)
  结论: 函数.单射 (toFinsuppAntidiag (n := n))
  证明: by
  unfold toFinsuppAntidiag
  intro p q h
  rw [Finsupp.mk.injEq] at h
  obtain ⟨hfinset, hcount⟩ := h
  rw [Nat.Partition.ext_iff]; rw [Multiset.ext]
  intro m
  obtain rfl | h0 := Nat.eq_zero_or_pos m
  · grind [Multiset.count_eq_zero]
· exact Nat.eq_of_mul_eq_mul_right h0 funext_iff.mp hcount m

Depends on / 依赖: CompactSpace, Finsupp, Finsupp.mk.injEq, IsClosed, IsClosed.preimage, Multiset, Multiset.count_eq_zero, Multiset.ext, Nat.Partition.ext_iff, Nat.eq_of_mul_eq_mul_right, Nat.eq_zero_or_pos, OnePoint, Partition, Prod.snd, all_goals, count_eq_zero, eq_of_mul_eq_mul_right, eq_zero_or_pos, ext_iff, fun_prop
-/
theorem toFinsuppAntidiag_injective (n : Nat) : Function.Injective (toFinsuppAntidiag (n := n)) := by
  unfold toFinsuppAntidiag
  intro p q h
  rw [Finsupp.mk.injEq] at h
  obtain ⟨hfinset, hcount⟩ := h
  rw [Nat.Partition.ext_iff]; rw [Multiset.ext]
  intro m
  obtain rfl | h0 := Nat.eq_zero_or_pos m
  · grind [Multiset.count_eq_zero]
· exact Nat.eq_of_mul_eq_mul_right h0 funext_iff.mp hcount m

/--
theorem `toFinsuppAntidiag_mem_finsuppAntidiag` / 定理 `toFinsuppAntidiag_mem_finsuppAntidiag`

English:
theorem toFinsuppAntidiag_mem_finsuppAntidiag
  given: {n : Nat} (p : Partition n)
  proof: by
  have hp : p.parts.toFinset subseteq Finset.Icc 1 n := by
    grind
  suffices ∑ m in Finset.Icc 1 n, Multiset.count m p.parts * m = n by simpa [toFinsuppAntidiag, hp]
  convert! ← p.parts_sum
  rw [Finset.sum_multiset_count]
  apply Finset.sum_subset hp
  suffices forall (x : Nat), 1 <= x -> x 

中文:
定理 toFinsuppAntidiag_mem_finsuppAntidiag
  条件: {n : 自然数} (p : 分拆 n)
  证明: by
  have hp : p.parts.toFinset subseteq Finset.Icc 1 n := by
    grind
  suffices ∑ m in Finset.Icc 1 n, Multiset.count m p.parts * m = n by simpa [toFinsuppAntidiag, hp]
  convert! ← p.parts_sum
  rw [Finset.sum_multiset_count]
  apply Finset.sum_subset hp
  suffices forall (x : Nat), 1 <= x -> x 

Depends on / 依赖: Finset, Finset.Icc, Finset.sum_multiset_count, Finset.sum_subset, Multiset, Multiset.count, convert, p.parts, p.parts.toFinset, p.parts_sum, parts_sum, subseteq, sum_multiset_count, sum_subset, toFinset, toFinsuppAntidiag
-/
theorem toFinsuppAntidiag_mem_finsuppAntidiag {n : Nat} (p : Partition n) :
    p.toFinsuppAntidiag in (Finset.Icc 1 n).finsuppAntidiag n := by
  have hp : p.parts.toFinset subseteq Finset.Icc 1 n := by
    grind
  suffices ∑ m in Finset.Icc 1 n, Multiset.count m p.parts * m = n by simpa [toFinsuppAntidiag, hp]
  convert! ← p.parts_sum
  rw [Finset.sum_multiset_count]
  apply Finset.sum_subset hp
  suffices forall (x : Nat), 1 <= x -> x <= n -> x ∉ p.parts -> x ∉ p.parts ∨ x = 0 by simpa
  grind

/--
Definition of `indiscrete` / `indiscrete` 的定义

English:
definition indiscrete
  signature: (n : Nat)
  body: ofSums n {n} rfl

中文:
定义 indiscrete
  签名: (n : 自然数)
  定义体: ofSums n {n} rfl

Depends on / 依赖: ofSums
-/
def indiscrete (n : Nat) : Partition n := ofSums n {n} rfl

instance {n : Nat} : Inhabited (Partition n) := ⟨indiscrete n⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `indiscrete_parts` / 引理 `indiscrete_parts`

English:
lemma indiscrete_parts
  given: {n : Nat} (hn : n != 0)
  statement: (indiscrete n).parts = {n}
  proof: by
  simp [indiscrete, filter_eq_self, hn]

中文:
引理 indiscrete_parts
  条件: {n : 自然数} (hn : n != 0)
  结论: (indiscrete n).parts = {n}
  证明: by
  simp [indiscrete, filter_eq_self, hn]
-/
@[simp] lemma indiscrete_parts {n : Nat} (hn : n != 0) : (indiscrete n).parts = {n} := by
  simp [indiscrete, filter_eq_self, hn]

/--
lemma `partition_zero_parts` / 引理 `partition_zero_parts`

English:
lemma partition_zero_parts
  given: (p : Partition 0)
  statement: p.parts = 0
  proof: eq_zero_of_forall_notMem fun _ h => (p.parts_pos h).ne' sum_eq_zero_iff.1 p.parts_sum _ h

中文:
引理 partition_zero_parts
  条件: (p : 分拆 0)
  结论: p.parts = 0
  证明: eq_zero_of_forall_notMem fun _ h => (p.parts_pos h).ne' sum_eq_zero_iff.1 p.parts_sum _ h
-/
@[simp] lemma partition_zero_parts (p : Partition 0) : p.parts = 0 :=
eq_zero_of_forall_notMem fun _ h => (p.parts_pos h).ne' sum_eq_zero_iff.1 p.parts_sum _ h

/--
Instance `UniquePartitionZero` / 实例 `UniquePartitionZero`

English:
instance UniquePartitionZero
  signature: : Unique (Partition 0) where
  body: Partition.ext by simp

中文:
实例 UniquePartitionZero
  签名: : 唯一 (分拆 0) where
  定义体: Partition.ext by simp

Depends on / 依赖: Partition, Partition.ext, equivSmall, fullyFaithfulFunctor, fullyFaithfulFunctor.homEquiv, functor, functor.obj, homEquiv
-/
instance UniquePartitionZero : Unique (Partition 0) where
uniq _ := Partition.ext by simp

/--
lemma `partition_one_parts` / 引理 `partition_one_parts`

English:
lemma partition_one_parts
  given: (p : Partition 1)
  statement: p.parts = {1}
  proof: by
  have h : p.parts = replicate (card p.parts) 1 := eq_replicate_card.2 fun x hx =>
    ((le_sum_of_mem hx).trans_eq p.parts_sum).antisymm (p.parts_pos hx)
  have h' : card p.parts = 1 := by simpa using (congrArg sum h.symm).trans p.parts_sum
  rw [h]; rw [h']; rw [replicate_one]

中文:
引理 partition_one_parts
  条件: (p : 分拆 1)
  结论: p.parts = {1}
  证明: by
  have h : p.parts = replicate (card p.parts) 1 := eq_replicate_card.2 fun x hx =>
    ((le_sum_of_mem hx).trans_eq p.parts_sum).antisymm (p.parts_pos hx)
  have h' : card p.parts = 1 := by simpa using (congrArg sum h.symm).trans p.parts_sum
  rw [h]; rw [h']; rw [replicate_one]
-/
@[simp] lemma partition_one_parts (p : Partition 1) : p.parts = {1} := by
  have h : p.parts = replicate (card p.parts) 1 := eq_replicate_card.2 fun x hx =>
    ((le_sum_of_mem hx).trans_eq p.parts_sum).antisymm (p.parts_pos hx)
  have h' : card p.parts = 1 := by simpa using (congrArg sum h.symm).trans p.parts_sum
  rw [h]; rw [h']; rw [replicate_one]

/--
Instance `UniquePartitionOne` / 实例 `UniquePartitionOne`

English:
instance UniquePartitionOne
  signature: : Unique (Partition 1) where
  body: Partition.ext by simp

中文:
实例 UniquePartitionOne
  签名: : 唯一 (分拆 1) where
  定义体: Partition.ext by simp

Depends on / 依赖: Partition, Partition.ext
-/
instance UniquePartitionOne : Unique (Partition 1) where
uniq _ := Partition.ext by simp

/--
lemma `ofSym_one` / 引理 `ofSym_one`

English:
lemma ofSym_one
  given: (s : Sym σ 1)
  statement: ofSym s = indiscrete 1
  proof: by
  ext; simp

中文:
引理 ofSym_one
  条件: (s : Sym σ 1)
  结论: ofSym s = indiscrete 1
  证明: by
  ext; simp
-/
@[simp] lemma ofSym_one (s : Sym σ 1) : ofSym s = indiscrete 1 := by
  ext; simp

/--
theorem `count_ofSums_of_ne_zero` / 定理 `count_ofSums_of_ne_zero`

English:
theorem count_ofSums_of_ne_zero
  given: {n : Nat} {l : Multiset Nat} (hl : l.sum = n) {i : Nat} (hi : i != 0)
  proof: count_filter_of_pos hi

中文:
定理 count_ofSums_of_ne_zero
  条件: {n : 自然数} {l : Multiset 自然数} (hl : l.求和 = n) {i : 自然数} (hi : i != 0)
  证明: count_filter_of_pos hi

Depends on / 依赖: count_filter_of_pos
-/
theorem count_ofSums_of_ne_zero {n : Nat} {l : Multiset Nat} (hl : l.sum = n) {i : Nat} (hi : i != 0) :
    (ofSums n l hl).parts.count i = l.count i :=
  count_filter_of_pos hi

/--
theorem `count_ofSums_zero` / 定理 `count_ofSums_zero`

English:
theorem count_ofSums_zero
  given: {n : Nat} {l : Multiset Nat} (hl : l.sum = n)
  proof: count_filter_of_neg fun h => h rfl

中文:
定理 count_ofSums_zero
  条件: {n : 自然数} {l : Multiset 自然数} (hl : l.求和 = n)
  证明: count_filter_of_neg fun h => h rfl

Depends on / 依赖: count_filter_of_neg
-/
theorem count_ofSums_zero {n : Nat} {l : Multiset Nat} (hl : l.sum = n) :
    (ofSums n l hl).parts.count 0 = 0 :=
  count_filter_of_neg fun h => h rfl

/-- Show there are finitely many partitions by considering the surjection from compositions to
partitions.
-/
instance (n : Nat) : Fintype (Partition n) :=
  Fintype.ofSurjective (ofComposition n) ofComposition_surj

/--
Definition of `restricted` / `restricted` 的定义

English:
definition restricted
  signature: (n : Nat) (p : Nat -> Prop) [DecidablePred p]
  body: Finset.univ.filter fun x => forall i in x.parts, p i

中文:
定义 restricted
  签名: (n : 自然数) (p : 自然数 -> 命题) [DecidablePred p]
  定义体: Finset.univ.filter fun x => forall i in x.parts, p i

Depends on / 依赖: Finset, Finset.univ.filter, filter, x.parts
-/
def restricted (n : Nat) (p : Nat -> Prop) [DecidablePred p] : Finset n.Partition :=
  Finset.univ.filter fun x => forall i in x.parts, p i

/--
Definition of `countRestricted` / `countRestricted` 的定义

English:
definition countRestricted
  signature: (n : Nat) (m : Nat)
  body: Finset.univ.filter fun x => forall i in x.parts, x.parts.count i < m

中文:
定义 countRestricted
  签名: (n : 自然数) (m : 自然数)
  定义体: Finset.univ.filter fun x => forall i in x.parts, x.parts.count i < m

Depends on / 依赖: Finset, Finset.univ.filter, filter, x.parts, x.parts.count
-/
def countRestricted (n : Nat) (m : Nat) : Finset n.Partition :=
  Finset.univ.filter fun x => forall i in x.parts, x.parts.count i < m

/--
Definition of `odds` / `odds` 的定义

English:
definition odds
  signature: (n : Nat)
  body: restricted n (¬ Even ·)

中文:
定义 odds
  签名: (n : 自然数)
  定义体: restricted n (¬ Even ·)

Depends on / 依赖: restricted
-/
def odds (n : Nat) : Finset n.Partition := restricted n (¬ Even ·)

/--
Definition of `distincts` / `distincts` 的定义

English:
definition distincts
  signature: (n : Nat)
  body: Finset.univ.filter fun c => c.parts.Nodup

中文:
定义 distincts
  签名: (n : 自然数)
  定义体: Finset.univ.filter fun c => c.parts.Nodup

Depends on / 依赖: Finset, Finset.univ.filter, c.parts.Nodup, filter
-/
def distincts (n : Nat) : Finset n.Partition :=
  Finset.univ.filter fun c => c.parts.Nodup

/--
theorem `countRestricted_two` / 定理 `countRestricted_two`

English:
theorem countRestricted_two
  given: (n : Nat)
  statement: countRestricted n 2 = distincts n
  proof: by
  congrm Finset.univ.filter fun x => ?_
  rw [Multiset.nodup_iff_count_le_one]
  grind [Multiset.count_eq_zero]

中文:
定理 countRestricted_two
  条件: (n : 自然数)
  结论: countRestricted n 2 = distincts n
  证明: by
  congrm Finset.univ.filter fun x => ?_
  rw [Multiset.nodup_iff_count_le_one]
  grind [Multiset.count_eq_zero]

Depends on / 依赖: Finset, Finset.univ.filter, Multiset, Multiset.count_eq_zero, Multiset.nodup_iff_count_le_one, congrm, count_eq_zero, filter, nodup_iff_count_le_one
-/
theorem countRestricted_two (n : Nat) : countRestricted n 2 = distincts n := by
  congrm Finset.univ.filter fun x => ?_
  rw [Multiset.nodup_iff_count_le_one]
  grind [Multiset.count_eq_zero]

/--
Definition of `oddDistincts` / `oddDistincts` 的定义

English:
definition oddDistincts
  signature: (n : Nat)
  body: odds n inter distincts n

中文:
定义 oddDistincts
  签名: (n : 自然数)
  定义体: odds n inter distincts n

Depends on / 依赖: distincts
-/
def oddDistincts (n : Nat) : Finset n.Partition :=
  odds n inter distincts n

/--
Definition of `partitionWithPartEquiv` / `partitionWithPartEquiv` 的定义

English:
definition partitionWithPartEquiv
  signature: {n a : Nat} (ha1 : 1 <= a) (ha : a <= n)
  body: by
    refine ⟨p.1.parts.erase a, ?_, ?_⟩
    · intro _ hi
      exact p.1.parts_pos (p.1.parts.erase_subset a hi)
    · have hs : a + (p.1.parts.erase a).sum = n := by
        simpa [p.1.parts_sum] using congrArg Multiset.sum (Multiset.cons_erase p.2)
      lia
  invFun q := ⟨⟨a ::ₘ q.parts, by gri

中文:
定义 partitionWithPartEquiv
  签名: {n a : 自然数} (ha1 : 1 <= a) (ha : a <= n)
  定义体: by
    refine ⟨p.1.parts.erase a, ?_, ?_⟩
    · intro _ hi
      exact p.1.parts_pos (p.1.parts.erase_subset a hi)
    · have hs : a + (p.1.parts.erase a).sum = n := by
        simpa [p.1.parts_sum] using congrArg Multiset.sum (Multiset.cons_erase p.2)
      lia
  invFun q := ⟨⟨a ::ₘ q.parts, by gri

Depends on / 依赖: Multiset, Multiset.cons_erase, Multiset.sum, Partition, Partition.ext, Subtype, Subtype.ext, TopCat, TopCat.epi_iff_surjective, cons_erase, epi_iff_surjective, erase_cons_head, erase_subset, invFun, left_inv, p.property, parts.erase, parts.erase_subset, parts_pos, parts_sum
-/
def partitionWithPartEquiv {n a : Nat} (ha1 : 1 <= a) (ha : a <= n) :
    {p : n.Partition // a in p.parts} ≃ (n - a).Partition where
  toFun p := by
    refine ⟨p.1.parts.erase a, ?_, ?_⟩
    · intro _ hi
      exact p.1.parts_pos (p.1.parts.erase_subset a hi)
    · have hs : a + (p.1.parts.erase a).sum = n := by
        simpa [p.1.parts_sum] using congrArg Multiset.sum (Multiset.cons_erase p.2)
      lia
  invFun q := ⟨⟨a ::ₘ q.parts, by grind, by simp [q.parts_sum, ha]⟩, by simp⟩
left_inv p := Subtype.ext Partition.ext cons_erase p.property
right_inv q := Partition.ext erase_cons_head a q.parts

@[simp]
/--
theorem `partitionWithPartEquiv_apply_parts` / 定理 `partitionWithPartEquiv_apply_parts`

English:
theorem partitionWithPartEquiv_apply_parts
  statement: {n a : Nat} (ha1 : 1 <= a) (ha : a <= n)
  proof: by
  dsimp [partitionWithPartEquiv]

@[simp]

中文:
定理 partitionWithPartEquiv_apply_parts
  结论: {n a : 自然数} (ha1 : 1 <= a) (ha : a <= n)
  证明: by
  dsimp [partitionWithPartEquiv]

@[simp]

Depends on / 依赖: partitionWithPartEquiv
-/
theorem partitionWithPartEquiv_apply_parts {n a : Nat} (ha1 : 1 <= a) (ha : a <= n)
    (p : {p : n.Partition // a in p.parts}) :
    (partitionWithPartEquiv ha1 ha p).parts = p.1.parts.erase a := by
  dsimp [partitionWithPartEquiv]

@[simp]
/--
theorem `partitionWithPartEquiv_symm_apply_parts` / 定理 `partitionWithPartEquiv_symm_apply_parts`

English:
theorem partitionWithPartEquiv_symm_apply_parts
  statement: {n a : Nat} (ha1 : 1 <= a) (ha : a <= n)
  proof: by
  dsimp [partitionWithPartEquiv]

中文:
定理 partitionWithPartEquiv_symm_apply_parts
  结论: {n a : 自然数} (ha1 : 1 <= a) (ha : a <= n)
  证明: by
  dsimp [partitionWithPartEquiv]

Depends on / 依赖: SequentialSpace, SequentialSpace.coinduced, coinduced, partitionWithPartEquiv
-/
theorem partitionWithPartEquiv_symm_apply_parts {n a : Nat} (ha1 : 1 <= a) (ha : a <= n)
    (p : (n - a).Partition) : ((partitionWithPartEquiv ha1 ha).symm p).1.parts = a ::ₘ p.parts := by
  dsimp [partitionWithPartEquiv]

end Partition

end Nat
