/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.Basic

/-!
# Hahn decomposition

This file proves the Hahn decomposition theorem (signed version). The Hahn decomposition theorem
states that, given a signed measure `s`, there exist complementary, measurable sets `i` and `j`,
such that `i` is positive and `j` is negative with respect to `s`; that is, `s` restricted on `i`
is non-negative and `s` restricted on `j` is non-positive.

The Hahn decomposition theorem leads to many other results in measure theory, most notably,
the Jordan decomposition theorem, the Lebesgue decomposition theorem and the Radon-Nikodym theorem.

## Main results

* `MeasureTheory.SignedMeasure.exists_isCompl_positive_negative` : the Hahn decomposition
  theorem.
* `MeasureTheory.SignedMeasure.exists_subset_restrict_nonpos` : A measurable set of negative
  measure contains a negative subset.

## Notation

We use the notations `0 ≤[i] s` and `s ≤[i] 0` to denote the usual definitions of a set `i`
being positive/negative with respect to the signed measure `s`.

## Tags

Hahn decomposition theorem
-/

@[expose] public section


noncomputable section

open scoped NNReal ENNReal MeasureTheory

variable {α β : Type*} [MeasurableSpace α]

namespace MeasureTheory

namespace SignedMeasure

open Filter VectorMeasure

variable {s : SignedMeasure α} {i j : Set α}

section ExistsSubsetRestrictNonpos

/-! ### `exists_subset_restrict_nonpos`

In this section we will prove that a set `i` whose measure is negative contains a negative subset
`j` with respect to the signed measure `s` (i.e. `s ≤[j] 0`), whose measure is negative. This lemma
is used to prove the Hahn decomposition theorem.

To prove this lemma, we will construct a sequence of measurable sets $(A_n)_{n \in \mathbb{N}}$,
such that, for all $n$, $s(A_{n + 1})$ is close to maximal among subsets of
$i \setminus \bigcup_{k \le n} A_k$.

This sequence of sets does not necessarily exist. However, if this sequence terminates; that is,
there does not exist any set satisfying the property, the last $A_n$ will be a negative subset
of negative measure, hence proving our claim.

In the case that the sequence does not terminate, it is easy to see that
$i \setminus \bigcup_{k = 0}^\infty A_k$ is the required negative set.

To implement this in Lean, we define several auxiliary definitions.

- given the sets `i` and the natural number `n`, `ExistsOneDivLT s i n` is the property that
  there exists a measurable set `k ⊆ i` such that `1 / (n + 1) < s k`.
- given the sets `i` and that `i` is not negative, `findExistsOneDivLT s i` is the
  least natural number `n` such that `ExistsOneDivLT s i n`.
- given the sets `i` and that `i` is not negative, `someExistsOneDivLT` chooses the set
  `k` from `ExistsOneDivLT s i (findExistsOneDivLT s i)`.
- lastly, given the set `i`, `restrictNonposSeq s i` is the sequence of sets defined inductively
  where
  `restrictNonposSeq s i 0 = someExistsOneDivLT s (i \ ∅)` and
  `restrictNonposSeq s i (n + 1) = someExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonposSeq k)`.
  This definition represents the sequence $(A_n)$ in the proof as described above.

With these definitions, we are able to consider the case where the sequence terminates separately,
allowing us to prove `exists_subset_restrict_nonpos`.
-/


/--
Definition of `ExistsOneDivLT` / `ExistsOneDivLT` 的定义

English:
definition ExistsOneDivLT
  signature: (s : SignedMeasure α) (i : Set α) (n : Nat)
  body: exists k : Set α, k subseteq i ∧ MeasurableSet k ∧ (1 / (n + 1) : Real) < s k

中文:
定义 ExistsOneDivLT
  签名: (s : 符号测度 α) (i : 集合 α) (n : 自然数)
  定义体: exists k : Set α, k subseteq i ∧ MeasurableSet k ∧ (1 / (n + 1) : Real) < s k
-/
private def ExistsOneDivLT (s : SignedMeasure α) (i : Set α) (n : Nat) : Prop :=
  exists k : Set α, k subseteq i ∧ MeasurableSet k ∧ (1 / (n + 1) : Real) < s k

/--
theorem `existsNatOneDivLTMeasure_of_not_negative` / 定理 `existsNatOneDivLTMeasure_of_not_negative`

English:
theorem existsNatOneDivLTMeasure_of_not_negative
  given: (hi : ¬s <=[i] 0)
  proof: let ⟨k, hj₁, hj₂, hj⟩ := exists_pos_measure_of_not_restrict_le_zero s hi
  let ⟨n, hn⟩ := exists_nat_one_div_lt hj
  ⟨n, k, hj₂, hj₁, hn⟩

中文:
定理 存在自然数OneDivLTMeasure_of_not_negative
  条件: (hi : ¬s <=[i] 0)
  证明: let ⟨k, hj₁, hj₂, hj⟩ := exists_pos_measure_of_not_restrict_le_zero s hi
  let ⟨n, hn⟩ := exists_nat_one_div_lt hj
  ⟨n, k, hj₂, hj₁, hn⟩
-/
private theorem existsNatOneDivLTMeasure_of_not_negative (hi : ¬s <=[i] 0) :
    exists n : Nat, ExistsOneDivLT s i n :=
  let ⟨k, hj₁, hj₂, hj⟩ := exists_pos_measure_of_not_restrict_le_zero s hi
  let ⟨n, hn⟩ := exists_nat_one_div_lt hj
  ⟨n, k, hj₂, hj₁, hn⟩

open scoped Classical in
/--
Definition of `findExistsOneDivLT` / `findExistsOneDivLT` 的定义

English:
definition findExistsOneDivLT
  signature: (s : SignedMeasure α) (i : Set α)
  body: if hi : ¬s <=[i] 0 then Nat.find (existsNatOneDivLTMeasure_of_not_negative hi) else 0

中文:
定义 findExistsOneDivLT
  签名: (s : 符号测度 α) (i : 集合 α)
  定义体: if hi : ¬s <=[i] 0 then Nat.find (existsNatOneDivLTMeasure_of_not_negative hi) else 0
-/
private def findExistsOneDivLT (s : SignedMeasure α) (i : Set α) : Nat :=
  if hi : ¬s <=[i] 0 then Nat.find (existsNatOneDivLTMeasure_of_not_negative hi) else 0

/--
theorem `findExistsOneDivLT_spec` / 定理 `findExistsOneDivLT_spec`

English:
theorem findExistsOneDivLT_spec
  given: (hi : ¬s <=[i] 0)
  proof: by
  rw [findExistsOneDivLT]; rw [dif_pos hi]
  convert! Nat.find_spec (existsNatOneDivLTMeasure_of_not_negative hi)

中文:
定理 findExistsOneDivLT_spec
  条件: (hi : ¬s <=[i] 0)
  证明: by
  rw [findExistsOneDivLT]; rw [dif_pos hi]
  convert! Nat.find_spec (existsNatOneDivLTMeasure_of_not_negative hi)
-/
private theorem findExistsOneDivLT_spec (hi : ¬s <=[i] 0) :
    ExistsOneDivLT s i (findExistsOneDivLT s i) := by
  rw [findExistsOneDivLT]; rw [dif_pos hi]
  convert! Nat.find_spec (existsNatOneDivLTMeasure_of_not_negative hi)

/--
theorem `findExistsOneDivLT_min` / 定理 `findExistsOneDivLT_min`

English:
theorem findExistsOneDivLT_min
  statement: (hi : ¬s <=[i] 0) {m : Nat}
  proof: by
  classical
  rw [findExistsOneDivLT]; rw [dif_pos hi] at hm
  exact Nat.find_min _ hm

中文:
定理 findExistsOneDivLT_min
  结论: (hi : ¬s <=[i] 0) {m : 自然数}
  证明: by
  classical
  rw [findExistsOneDivLT]; rw [dif_pos hi] at hm
  exact Nat.find_min _ hm
-/
private theorem findExistsOneDivLT_min (hi : ¬s <=[i] 0) {m : Nat}
    (hm : m < findExistsOneDivLT s i) : ¬ExistsOneDivLT s i m := by
  classical
  rw [findExistsOneDivLT]; rw [dif_pos hi] at hm
  exact Nat.find_min _ hm

open scoped Classical in
/--
Definition of `someExistsOneDivLT` / `someExistsOneDivLT` 的定义

English:
definition someExistsOneDivLT
  signature: (s : SignedMeasure α) (i : Set α)
  body: if hi : ¬s <=[i] 0 then Classical.choose (findExistsOneDivLT_spec hi) else ∅

中文:
定义 someExistsOneDivLT
  签名: (s : 符号测度 α) (i : 集合 α)
  定义体: if hi : ¬s <=[i] 0 then Classical.choose (findExistsOneDivLT_spec hi) else ∅
-/
private def someExistsOneDivLT (s : SignedMeasure α) (i : Set α) : Set α :=
  if hi : ¬s <=[i] 0 then Classical.choose (findExistsOneDivLT_spec hi) else ∅

/--
theorem `someExistsOneDivLT_spec` / 定理 `someExistsOneDivLT_spec`

English:
theorem someExistsOneDivLT_spec
  given: (hi : ¬s <=[i] 0)
  proof: by
  rw [someExistsOneDivLT]; rw [dif_pos hi]
  exact Classical.choose_spec (findExistsOneDivLT_spec hi)

中文:
定理 someExistsOneDivLT_spec
  条件: (hi : ¬s <=[i] 0)
  证明: by
  rw [someExistsOneDivLT]; rw [dif_pos hi]
  exact Classical.choose_spec (findExistsOneDivLT_spec hi)
-/
private theorem someExistsOneDivLT_spec (hi : ¬s <=[i] 0) :
    someExistsOneDivLT s i subseteq i ∧
      MeasurableSet (someExistsOneDivLT s i) ∧
        (1 / (findExistsOneDivLT s i + 1) : Real) < s (someExistsOneDivLT s i) := by
  rw [someExistsOneDivLT]; rw [dif_pos hi]
  exact Classical.choose_spec (findExistsOneDivLT_spec hi)

/--
theorem `someExistsOneDivLT_subset` / 定理 `someExistsOneDivLT_subset`

English:
theorem someExistsOneDivLT_subset
  statement: someExistsOneDivLT s i subseteq i
  proof: by
  by_cases hi : ¬s <=[i] 0
  · exact
      let ⟨h, _⟩ := someExistsOneDivLT_spec hi
      h
  · rw [someExistsOneDivLT, dif_neg hi]
    exact Set.empty_subset _

中文:
定理 someExistsOneDivLT_subset
  结论: someExistsOneDivLT s i subseteq i
  证明: by
  by_cases hi : ¬s <=[i] 0
  · exact
      let ⟨h, _⟩ := someExistsOneDivLT_spec hi
      h
  · rw [someExistsOneDivLT, dif_neg hi]
    exact Set.empty_subset _
-/
private theorem someExistsOneDivLT_subset : someExistsOneDivLT s i subseteq i := by
  by_cases hi : ¬s <=[i] 0
  · exact
      let ⟨h, _⟩ := someExistsOneDivLT_spec hi
      h
  · rw [someExistsOneDivLT, dif_neg hi]
    exact Set.empty_subset _

/--
theorem `someExistsOneDivLT_subset'` / 定理 `someExistsOneDivLT_subset'`

English:
theorem someExistsOneDivLT_subset'
  statement: someExistsOneDivLT s (i \ j) subseteq i
  proof: someExistsOneDivLT_subset.trans Set.sdiff_subset

中文:
定理 someExistsOneDivLT_subset'
  结论: someExistsOneDivLT s (i \ j) subseteq i
  证明: someExistsOneDivLT_subset.trans Set.sdiff_subset
-/
private theorem someExistsOneDivLT_subset' : someExistsOneDivLT s (i \ j) subseteq i :=
  someExistsOneDivLT_subset.trans Set.sdiff_subset

/--
theorem `someExistsOneDivLT_measurableSet` / 定理 `someExistsOneDivLT_measurableSet`

English:
theorem someExistsOneDivLT_measurableSet
  statement: MeasurableSet (someExistsOneDivLT s i)
  proof: by
  by_cases hi : ¬s <=[i] 0
  · exact
      let ⟨_, h, _⟩ := someExistsOneDivLT_spec hi
      h
  · rw [someExistsOneDivLT, dif_neg hi]
    exact MeasurableSet.empty

中文:
定理 someExistsOneDivLT_measurableSet
  结论: 可测集 (someExistsOneDivLT s i)
  证明: by
  by_cases hi : ¬s <=[i] 0
  · exact
      let ⟨_, h, _⟩ := someExistsOneDivLT_spec hi
      h
  · rw [someExistsOneDivLT, dif_neg hi]
    exact MeasurableSet.empty
-/
private theorem someExistsOneDivLT_measurableSet : MeasurableSet (someExistsOneDivLT s i) := by
  by_cases hi : ¬s <=[i] 0
  · exact
      let ⟨_, h, _⟩ := someExistsOneDivLT_spec hi
      h
  · rw [someExistsOneDivLT, dif_neg hi]
    exact MeasurableSet.empty

/--
theorem `someExistsOneDivLT_lt` / 定理 `someExistsOneDivLT_lt`

English:
theorem someExistsOneDivLT_lt
  given: (hi : ¬s <=[i] 0)
  proof: let ⟨_, _, h⟩ := someExistsOneDivLT_spec hi
  h

中文:
定理 someExistsOneDivLT_lt
  条件: (hi : ¬s <=[i] 0)
  证明: let ⟨_, _, h⟩ := someExistsOneDivLT_spec hi
  h
-/
private theorem someExistsOneDivLT_lt (hi : ¬s <=[i] 0) :
    (1 / (findExistsOneDivLT s i + 1) : Real) < s (someExistsOneDivLT s i) :=
  let ⟨_, _, h⟩ := someExistsOneDivLT_spec hi
  h

/--
Definition of `restrictNonposSeq` / `restrictNonposSeq` 的定义

English:
definition restrictNonposSeq
  signature: (s : SignedMeasure α) (i : Set α)

中文:
定义 restrictNonposSeq
  签名: (s : 符号测度 α) (i : 集合 α)
-/
private def restrictNonposSeq (s : SignedMeasure α) (i : Set α) : Nat -> Set α
  | 0 => someExistsOneDivLT s (i \ ∅) -- I used `i \ ∅` instead of `i` to simplify some proofs
  | n + 1 =>
    someExistsOneDivLT s
      (i \
        ⋃ (k) (H : k <= n),
          have : k < n + 1 := Nat.lt_succ_iff.mpr H
          restrictNonposSeq s i k)

/--
theorem `restrictNonposSeq_succ` / 定理 `restrictNonposSeq_succ`

English:
theorem restrictNonposSeq_succ
  given: (n : Nat)
  proof: by
  rw [restrictNonposSeq]

中文:
定理 restrictNonposSeq_succ
  条件: (n : 自然数)
  证明: by
  rw [restrictNonposSeq]
-/
private theorem restrictNonposSeq_succ (n : Nat) :
    restrictNonposSeq s i n.succ = someExistsOneDivLT s (i \ ⋃ k <= n, restrictNonposSeq s i k) := by
  rw [restrictNonposSeq]

/--
theorem `restrictNonposSeq_subset` / 定理 `restrictNonposSeq_subset`

English:
theorem restrictNonposSeq_subset
  given: (n : Nat)
  statement: restrictNonposSeq s i n subseteq i
  proof: by
  cases n <;> · rw [restrictNonposSeq]; exact someExistsOneDivLT_subset'

中文:
定理 restrictNonposSeq_subset
  条件: (n : 自然数)
  结论: restrictNonposSeq s i n subseteq i
  证明: by
  cases n <;> · rw [restrictNonposSeq]; exact someExistsOneDivLT_subset'
-/
private theorem restrictNonposSeq_subset (n : Nat) : restrictNonposSeq s i n subseteq i := by
  cases n <;> · rw [restrictNonposSeq]; exact someExistsOneDivLT_subset'

/--
theorem `restrictNonposSeq_lt` / 定理 `restrictNonposSeq_lt`

English:
theorem restrictNonposSeq_lt
  given: (n : Nat) (hn : ¬s <=[i \ ⋃ k <= n, restrictNonposSeq s i k] 0)
  proof: by
  rw [restrictNonposSeq_succ]
  apply someExistsOneDivLT_lt hn

中文:
定理 restrictNonposSeq_lt
  条件: (n : 自然数) (hn : ¬s <=[i \ ⋃ k <= n, restrictNonposSeq s i k] 0)
  证明: by
  rw [restrictNonposSeq_succ]
  apply someExistsOneDivLT_lt hn
-/
private theorem restrictNonposSeq_lt (n : Nat) (hn : ¬s <=[i \ ⋃ k <= n, restrictNonposSeq s i k] 0) :
    (1 / (findExistsOneDivLT s (i \ ⋃ k <= n, restrictNonposSeq s i k) + 1) : Real) <
      s (restrictNonposSeq s i n.succ) := by
  rw [restrictNonposSeq_succ]
  apply someExistsOneDivLT_lt hn

/--
theorem `measure_of_restrictNonposSeq` / 定理 `measure_of_restrictNonposSeq`

English:
theorem measure_of_restrictNonposSeq
  statement: (hi₂ : ¬s <=[i] 0) (n : Nat)
  proof: by
  cases n with
  | zero =>
    rw [restrictNonposSeq]; rw [← @Set.sdiff_empty _ i] at hi₂
    rcases someExistsOneDivLT_spec hi₂ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h
  | succ n =>
    rw [restrictNonposSeq_succ]
    have h₁ : ¬s <=[i \ ⋃ (k : Nat) (_ : k <= n), restrictNonposSeq s i k] 0 := by
      refine mt (restrict_le_zero_subset _ ?_ (by simp)) hn
      convert! measurable_of_not_restrict_le_zero _ hn using 3
      exact funext fun x => by rw [Nat.lt_succ_iff]
    rcases someExistsOneDivLT_spec h₁ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h

中文:
定理 measure_of_restrictNonposSeq
  结论: (hi₂ : ¬s <=[i] 0) (n : 自然数)
  证明: by
  cases n with
  | zero =>
    rw [restrictNonposSeq]; rw [← @Set.sdiff_empty _ i] at hi₂
    rcases someExistsOneDivLT_spec hi₂ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h
  | succ n =>
    rw [restrictNonposSeq_succ]
    have h₁ : ¬s <=[i \ ⋃ (k : Nat) (_ : k <= n), restrictNonposSeq s i k] 0 := by
      refine mt (restrict_le_zero_subset _ ?_ (by simp)) hn
      convert! measurable_of_not_restrict_le_zero _ hn using 3
      exact funext fun x => by rw [Nat.lt_succ_iff]
    rcases someExistsOneDivLT_spec h₁ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h
-/
private theorem measure_of_restrictNonposSeq (hi₂ : ¬s <=[i] 0) (n : Nat)
    (hn : ¬s <=[i \ ⋃ k < n, restrictNonposSeq s i k] 0) : 0 < s (restrictNonposSeq s i n) := by
  cases n with
  | zero =>
    rw [restrictNonposSeq]; rw [← @Set.sdiff_empty _ i] at hi₂
    rcases someExistsOneDivLT_spec hi₂ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h
  | succ n =>
    rw [restrictNonposSeq_succ]
    have h₁ : ¬s <=[i \ ⋃ (k : Nat) (_ : k <= n), restrictNonposSeq s i k] 0 := by
      refine mt (restrict_le_zero_subset _ ?_ (by simp)) hn
      convert! measurable_of_not_restrict_le_zero _ hn using 3
      exact funext fun x => by rw [Nat.lt_succ_iff]
    rcases someExistsOneDivLT_spec h₁ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h

/--
theorem `restrictNonposSeq_measurableSet` / 定理 `restrictNonposSeq_measurableSet`

English:
theorem restrictNonposSeq_measurableSet
  given: (n : Nat)
  proof: by
  cases n <;>
    · rw [restrictNonposSeq]
      exact someExistsOneDivLT_measurableSet

中文:
定理 restrictNonposSeq_measurableSet
  条件: (n : 自然数)
  证明: by
  cases n <;>
    · rw [restrictNonposSeq]
      exact someExistsOneDivLT_measurableSet
-/
private theorem restrictNonposSeq_measurableSet (n : Nat) :
    MeasurableSet (restrictNonposSeq s i n) := by
  cases n <;>
    · rw [restrictNonposSeq]
      exact someExistsOneDivLT_measurableSet

/--
theorem `restrictNonposSeq_disjoint'` / 定理 `restrictNonposSeq_disjoint'`

English:
theorem restrictNonposSeq_disjoint'
  given: {n m : Nat} (h : n < m)
  proof: by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx₁, hx₂⟩
  cases m; · lia
  · rw [restrictNonposSeq] at hx₂
    exact
      (someExistsOneDivLT_subset hx₂).2
        (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Nat.lt_succ_iff.mp h, hx₁⟩⟩)

中文:
定理 restrictNonposSeq_disjoint'
  条件: {n m : 自然数} (h : n < m)
  证明: by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx₁, hx₂⟩
  cases m; · lia
  · rw [restrictNonposSeq] at hx₂
    exact
      (someExistsOneDivLT_subset hx₂).2
        (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Nat.lt_succ_iff.mp h, hx₁⟩⟩)
-/
private theorem restrictNonposSeq_disjoint' {n m : Nat} (h : n < m) :
    restrictNonposSeq s i n inter restrictNonposSeq s i m = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx₁, hx₂⟩
  cases m; · lia
  · rw [restrictNonposSeq] at hx₂
    exact
      (someExistsOneDivLT_subset hx₂).2
        (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Nat.lt_succ_iff.mp h, hx₁⟩⟩)

open scoped Function in -- required for scoped `on` notation
/--
theorem `restrictNonposSeq_disjoint` / 定理 `restrictNonposSeq_disjoint`

English:
theorem restrictNonposSeq_disjoint
  statement: Pairwise (Disjoint on restrictNonposSeq s i)
  proof: by
  intro n m h
  rw [Function.onFun]; rw [Set.disjoint_iff_inter_eq_empty]
  rcases lt_or_gt_of_ne h with (h | h)
  · rw [restrictNonposSeq_disjoint' h]
  · rw [Set.inter_comm, restrictNonposSeq_disjoint' h]

中文:
定理 restrictNonposSeq_disjoint
  结论: 两两 (Disjoint on restrictNonposSeq s i)
  证明: by
  intro n m h
  rw [Function.onFun]; rw [Set.disjoint_iff_inter_eq_empty]
  rcases lt_or_gt_of_ne h with (h | h)
  · rw [restrictNonposSeq_disjoint' h]
  · rw [Set.inter_comm, restrictNonposSeq_disjoint' h]
-/
private theorem restrictNonposSeq_disjoint : Pairwise (Disjoint on restrictNonposSeq s i) := by
  intro n m h
  rw [Function.onFun]; rw [Set.disjoint_iff_inter_eq_empty]
  rcases lt_or_gt_of_ne h with (h | h)
  · rw [restrictNonposSeq_disjoint' h]
  · rw [Set.inter_comm, restrictNonposSeq_disjoint' h]

/--
theorem `exists_subset_restrict_nonpos'` / 定理 `exists_subset_restrict_nonpos'`

English:
theorem exists_subset_restrict_nonpos'
  statement: (hi₁ : MeasurableSet i) (hi₂ : s i < 0)
  proof: by
  classical
  by_cases h : s <=[i] 0
  · exact ⟨i, hi₁, Set.Subset.refl _, h, hi₂⟩
  push Not at hn
  set k := Nat.find hn
  have hk₂ : s <=[i \ ⋃ l < k, restrictNonposSeq s i l] 0 := Nat.find_spec hn
  have hmeas : MeasurableSet (⋃ (l : Nat) (_ : l < k), restrictNonposSeq s i l) :=
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
  refine ⟨i \ ⋃ l < k, restrictNonposSeq s i l, hi₁.diff hmeas, Set.sdiff_subset, hk₂, ?_⟩
  rw [of_sdiff hmeas hi₁]; rw [s.of_disjoint_iUnion]
  · have h₁ : forall l < k, 0 <= s (restrictNonposSeq s i l) := by
      intro l hl
      refine le_of_lt (measure_of_restrictNonposSeq h _ ?_)
      refine mt (restrict_le_zero_subset _ (hi₁.diff ?_) (Set.Subset.refl _)) (Nat.find_min hn hl)
      exact
        MeasurableSet.iUnion fun _ =>
          MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    suffices 0 <= ∑' l : Nat, s (⋃ _ : l < k, restrictNonposSeq s i l) by
      rw [sub_neg]
      exact lt_of_lt_of_le hi₂ this
    refine tsum_nonneg ?_
    intro l; by_cases h : l < k
    · convert! h₁ _ h
      ext x
      rw [Set.mem_iUnion]; rw [exists_prop]; rw [and_iff_right_iff_imp]
      exact fun _ => h
    · convert! le_of_eq s.empty.symm
      ext; simp only [exists_prop, Set.mem_empty_iff_false, Set.mem_iUnion, not_and, iff_false]
      exact fun h' => False.elim (h h')
  · intro; exact MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
  · intro a b hab
    refine Set.disjoint_iUnion_left.mpr fun _ => ?_
    refine Set.disjoint_iUnion_right.mpr fun _ => ?_
    exact restrictNonposSeq_disjoint hab
  · apply Set.iUnion_subset
    intro a x
    simp only [and_imp, exists_prop, Set.mem_iUnion]
    intro _ hx
    exact restrictNonposSeq_subset _ hx

中文:
定理 存在_subset_restrict_nonpos'
  结论: (hi₁ : 可测集 i) (hi₂ : s i < 0)
  证明: by
  classical
  by_cases h : s <=[i] 0
  · exact ⟨i, hi₁, Set.Subset.refl _, h, hi₂⟩
  push Not at hn
  set k := Nat.find hn
  have hk₂ : s <=[i \ ⋃ l < k, restrictNonposSeq s i l] 0 := Nat.find_spec hn
  have hmeas : MeasurableSet (⋃ (l : Nat) (_ : l < k), restrictNonposSeq s i l) :=
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
  refine ⟨i \ ⋃ l < k, restrictNonposSeq s i l, hi₁.diff hmeas, Set.sdiff_subset, hk₂, ?_⟩
  rw [of_sdiff hmeas hi₁]; rw [s.of_disjoint_iUnion]
  · have h₁ : forall l < k, 0 <= s (restrictNonposSeq s i l) := by
      intro l hl
      refine le_of_lt (measure_of_restrictNonposSeq h _ ?_)
      refine mt (restrict_le_zero_subset _ (hi₁.diff ?_) (Set.Subset.refl _)) (Nat.find_min hn hl)
      exact
        MeasurableSet.iUnion fun _ =>
          MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    suffices 0 <= ∑' l : Nat, s (⋃ _ : l < k, restrictNonposSeq s i l) by
      rw [sub_neg]
      exact lt_of_lt_of_le hi₂ this
    refine tsum_nonneg ?_
    intro l; by_cases h : l < k
    · convert! h₁ _ h
      ext x
      rw [Set.mem_iUnion]; rw [exists_prop]; rw [and_iff_right_iff_imp]
      exact fun _ => h
    · convert! le_of_eq s.empty.symm
      ext; simp only [exists_prop, Set.mem_empty_iff_false, Set.mem_iUnion, not_and, iff_false]
      exact fun h' => False.elim (h h')
  · intro; exact MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
  · intro a b hab
    refine Set.disjoint_iUnion_left.mpr fun _ => ?_
    refine Set.disjoint_iUnion_right.mpr fun _ => ?_
    exact restrictNonposSeq_disjoint hab
  · apply Set.iUnion_subset
    intro a x
    simp only [and_imp, exists_prop, Set.mem_iUnion]
    intro _ hx
    exact restrictNonposSeq_subset _ hx
-/
private theorem exists_subset_restrict_nonpos' (hi₁ : MeasurableSet i) (hi₂ : s i < 0)
    (hn : ¬forall n : Nat, ¬s <=[i \ ⋃ l < n, restrictNonposSeq s i l] 0) :
    exists j : Set α, MeasurableSet j ∧ j subseteq i ∧ s <=[j] 0 ∧ s j < 0 := by
  classical
  by_cases h : s <=[i] 0
  · exact ⟨i, hi₁, Set.Subset.refl _, h, hi₂⟩
  push Not at hn
  set k := Nat.find hn
  have hk₂ : s <=[i \ ⋃ l < k, restrictNonposSeq s i l] 0 := Nat.find_spec hn
  have hmeas : MeasurableSet (⋃ (l : Nat) (_ : l < k), restrictNonposSeq s i l) :=
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
  refine ⟨i \ ⋃ l < k, restrictNonposSeq s i l, hi₁.diff hmeas, Set.sdiff_subset, hk₂, ?_⟩
  rw [of_sdiff hmeas hi₁]; rw [s.of_disjoint_iUnion]
  · have h₁ : forall l < k, 0 <= s (restrictNonposSeq s i l) := by
      intro l hl
      refine le_of_lt (measure_of_restrictNonposSeq h _ ?_)
      refine mt (restrict_le_zero_subset _ (hi₁.diff ?_) (Set.Subset.refl _)) (Nat.find_min hn hl)
      exact
        MeasurableSet.iUnion fun _ =>
          MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    suffices 0 <= ∑' l : Nat, s (⋃ _ : l < k, restrictNonposSeq s i l) by
      rw [sub_neg]
      exact lt_of_lt_of_le hi₂ this
    refine tsum_nonneg ?_
    intro l; by_cases h : l < k
    · convert! h₁ _ h
      ext x
      rw [Set.mem_iUnion]; rw [exists_prop]; rw [and_iff_right_iff_imp]
      exact fun _ => h
    · convert! le_of_eq s.empty.symm
      ext; simp only [exists_prop, Set.mem_empty_iff_false, Set.mem_iUnion, not_and, iff_false]
      exact fun h' => False.elim (h h')
  · intro; exact MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
  · intro a b hab
    refine Set.disjoint_iUnion_left.mpr fun _ => ?_
    refine Set.disjoint_iUnion_right.mpr fun _ => ?_
    exact restrictNonposSeq_disjoint hab
  · apply Set.iUnion_subset
    intro a x
    simp only [and_imp, exists_prop, Set.mem_iUnion]
    intro _ hx
    exact restrictNonposSeq_subset _ hx

/--
theorem `exists_subset_restrict_nonpos` / 定理 `exists_subset_restrict_nonpos`

English:
theorem exists_subset_restrict_nonpos
  given: (hi : s i < 0)
  proof: by
have hi₁ : MeasurableSet i := by_contradiction fun h => ne_of_lt hi s.not_measurable h
  by_cases h : s <=[i] 0; · exact ⟨i, hi₁, Set.Subset.refl _, h, hi⟩
  by_cases hn : forall n : Nat, ¬s <=[i \ ⋃ l < n, restrictNonposSeq s i l] 0
  swap; · exact exists_subset_restrict_nonpos' hi₁ hi hn
  set A := i \ ⋃ l, restrictNonposSeq s i l with hA
  set bdd : Nat -> Nat := fun n => findExistsOneDivLT s (i \ ⋃ k <= n, restrictNonposSeq s i k)
  have hn' : forall n : Nat, ¬s <=[i \ ⋃ l <= n, restrictNonposSeq s i l] 0 := by
    intro n
    convert! hn (n + 1) using 5 <;>
      · ext l
        simp only [exists_prop, Set.mem_iUnion, and_congr_left_iff]
        exact fun _ => Nat.lt_succ_iff.symm
  have h₁ : s i = s A + ∑' l, s (restrictNonposSeq s i l) := by
    rw [hA]; rw [← s.of_disjoint_iUnion]; rw [add_comm]; rw [of_add_of_sdiff]
    · exact MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    exacts [hi₁, Set.iUnion_subset fun _ => restrictNonposSeq_subset _, fun _ =>
      restrictNonposSeq_measurableSet _, restrictNonposSeq_disjoint]
  have h₂ : s A <= s i := by
    rw [h₁]
    apply le_add_of_nonneg_right
    exact tsum_nonneg fun n => le_of_lt (measure_of_restrictNonposSeq h _ (hn n))
  have h₃' : Summable fun n => (1 / (bdd n + 1) : Real) := by
    have : Summable fun l => s (restrictNonposSeq s i l) :=
      HasSum.summable
        (s.m_iUnion (fun _ => restrictNonposSeq_measurableSet _) restrictNonposSeq_disjoint)
    refine .of_nonneg_of_le (fun n => ?_) (fun n => ?_)
        (this.comp_injective Nat.succ_injective)
    · exact le_of_lt Nat.one_div_pos_of_nat
    · exact le_of_lt (restrictNonposSeq_lt n (hn' n))
  have h₃ : Tendsto (fun n => (bdd n : Real) + 1) atTop atTop := by
    simp only [one_div] at h₃'
    exact Summable.tendsto_atTop_of_pos h₃' fun n => Nat.cast_add_one_pos (bdd n)
  have h₄ : Tendsto (fun n => (bdd n : Real)) atTop atTop := by
    convert! atTop.tendsto_atTop_add_const_right (-1) h₃; simp
  have A_meas : MeasurableSet A :=
    hi₁.diff (MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _)
  refine ⟨A, A_meas, Set.sdiff_subset, ?_, h₂.trans_lt hi⟩
  by_contra hnn
  rw [restrict_le_restrict_iff _ _ A_meas] at hnn; push Not at hnn
  obtain ⟨E, hE₁, hE₂, hE₃⟩ := hnn
  have : exists k, 1 <= bdd k ∧ 1 / (bdd k : Real) < s E := by
    rw [tendsto_atTop_atTop] at h₄
    obtain ⟨k, hk⟩ := h₄ (max (1 / s E + 1) 1)
    refine ⟨k, ?_, ?_⟩
    · have hle := le_of_max_le_right (hk k le_rfl)
      norm_cast at hle
    · have : 1 / s E < bdd k := by
        linarith only [le_of_max_le_left (hk k le_rfl)]
      rw [one_div] at this ⊢
      exact inv_lt_of_inv_lt₀ hE₃ this
  obtain ⟨k, hk₁, hk₂⟩ := this
  have hA' : A subseteq i \ ⋃ l <= k, restrictNonposSeq s i l :=
    Set.sdiff_subset_sdiff_right (Set.iUnion₂_subset_iUnion _ _)
  refine
    findExistsOneDivLT_min (hn' k) (Nat.sub_lt hk₁ Nat.zero_lt_one)
      ⟨E, Set.Subset.trans hE₂ hA', hE₁, ?_⟩
  convert! hk₂; norm_cast
  exact tsub_add_cancel_of_le hk₁

中文:
定理 存在_subset_restrict_nonpos
  条件: (hi : s i < 0)
  证明: by
have hi₁ : MeasurableSet i := by_contradiction fun h => ne_of_lt hi s.not_measurable h
  by_cases h : s <=[i] 0; · exact ⟨i, hi₁, Set.Subset.refl _, h, hi⟩
  by_cases hn : forall n : Nat, ¬s <=[i \ ⋃ l < n, restrictNonposSeq s i l] 0
  swap; · exact exists_subset_restrict_nonpos' hi₁ hi hn
  set A := i \ ⋃ l, restrictNonposSeq s i l with hA
  set bdd : Nat -> Nat := fun n => findExistsOneDivLT s (i \ ⋃ k <= n, restrictNonposSeq s i k)
  have hn' : forall n : Nat, ¬s <=[i \ ⋃ l <= n, restrictNonposSeq s i l] 0 := by
    intro n
    convert! hn (n + 1) using 5 <;>
      · ext l
        simp only [exists_prop, Set.mem_iUnion, and_congr_left_iff]
        exact fun _ => Nat.lt_succ_iff.symm
  have h₁ : s i = s A + ∑' l, s (restrictNonposSeq s i l) := by
    rw [hA]; rw [← s.of_disjoint_iUnion]; rw [add_comm]; rw [of_add_of_sdiff]
    · exact MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    exacts [hi₁, Set.iUnion_subset fun _ => restrictNonposSeq_subset _, fun _ =>
      restrictNonposSeq_measurableSet _, restrictNonposSeq_disjoint]
  have h₂ : s A <= s i := by
    rw [h₁]
    apply le_add_of_nonneg_right
    exact tsum_nonneg fun n => le_of_lt (measure_of_restrictNonposSeq h _ (hn n))
  have h₃' : Summable fun n => (1 / (bdd n + 1) : Real) := by
    have : Summable fun l => s (restrictNonposSeq s i l) :=
      HasSum.summable
        (s.m_iUnion (fun _ => restrictNonposSeq_measurableSet _) restrictNonposSeq_disjoint)
    refine .of_nonneg_of_le (fun n => ?_) (fun n => ?_)
        (this.comp_injective Nat.succ_injective)
    · exact le_of_lt Nat.one_div_pos_of_nat
    · exact le_of_lt (restrictNonposSeq_lt n (hn' n))
  have h₃ : Tendsto (fun n => (bdd n : Real) + 1) atTop atTop := by
    simp only [one_div] at h₃'
    exact Summable.tendsto_atTop_of_pos h₃' fun n => Nat.cast_add_one_pos (bdd n)
  have h₄ : Tendsto (fun n => (bdd n : Real)) atTop atTop := by
    convert! atTop.tendsto_atTop_add_const_right (-1) h₃; simp
  have A_meas : MeasurableSet A :=
    hi₁.diff (MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _)
  refine ⟨A, A_meas, Set.sdiff_subset, ?_, h₂.trans_lt hi⟩
  by_contra hnn
  rw [restrict_le_restrict_iff _ _ A_meas] at hnn; push Not at hnn
  obtain ⟨E, hE₁, hE₂, hE₃⟩ := hnn
  have : exists k, 1 <= bdd k ∧ 1 / (bdd k : Real) < s E := by
    rw [tendsto_atTop_atTop] at h₄
    obtain ⟨k, hk⟩ := h₄ (max (1 / s E + 1) 1)
    refine ⟨k, ?_, ?_⟩
    · have hle := le_of_max_le_right (hk k le_rfl)
      norm_cast at hle
    · have : 1 / s E < bdd k := by
        linarith only [le_of_max_le_left (hk k le_rfl)]
      rw [one_div] at this ⊢
      exact inv_lt_of_inv_lt₀ hE₃ this
  obtain ⟨k, hk₁, hk₂⟩ := this
  have hA' : A subseteq i \ ⋃ l <= k, restrictNonposSeq s i l :=
    Set.sdiff_subset_sdiff_right (Set.iUnion₂_subset_iUnion _ _)
  refine
    findExistsOneDivLT_min (hn' k) (Nat.sub_lt hk₁ Nat.zero_lt_one)
      ⟨E, Set.Subset.trans hE₂ hA', hE₁, ?_⟩
  convert! hk₂; norm_cast
  exact tsub_add_cancel_of_le hk₁

Depends on / 依赖: MeasurableSet, Set.Subset.refl, Subset, by_contradiction, exists_subset_restrict_nonpos, findExistsOneDivLT, ne_of_lt, not_measurable, restrictNonposSeq, s.not_measurable
-/
theorem exists_subset_restrict_nonpos (hi : s i < 0) :
    exists j : Set α, MeasurableSet j ∧ j subseteq i ∧ s <=[j] 0 ∧ s j < 0 := by
have hi₁ : MeasurableSet i := by_contradiction fun h => ne_of_lt hi s.not_measurable h
  by_cases h : s <=[i] 0; · exact ⟨i, hi₁, Set.Subset.refl _, h, hi⟩
  by_cases hn : forall n : Nat, ¬s <=[i \ ⋃ l < n, restrictNonposSeq s i l] 0
  swap; · exact exists_subset_restrict_nonpos' hi₁ hi hn
  set A := i \ ⋃ l, restrictNonposSeq s i l with hA
  set bdd : Nat -> Nat := fun n => findExistsOneDivLT s (i \ ⋃ k <= n, restrictNonposSeq s i k)
  have hn' : forall n : Nat, ¬s <=[i \ ⋃ l <= n, restrictNonposSeq s i l] 0 := by
    intro n
    convert! hn (n + 1) using 5 <;>
      · ext l
        simp only [exists_prop, Set.mem_iUnion, and_congr_left_iff]
        exact fun _ => Nat.lt_succ_iff.symm
  have h₁ : s i = s A + ∑' l, s (restrictNonposSeq s i l) := by
    rw [hA]; rw [← s.of_disjoint_iUnion]; rw [add_comm]; rw [of_add_of_sdiff]
    · exact MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    exacts [hi₁, Set.iUnion_subset fun _ => restrictNonposSeq_subset _, fun _ =>
      restrictNonposSeq_measurableSet _, restrictNonposSeq_disjoint]
  have h₂ : s A <= s i := by
    rw [h₁]
    apply le_add_of_nonneg_right
    exact tsum_nonneg fun n => le_of_lt (measure_of_restrictNonposSeq h _ (hn n))
  have h₃' : Summable fun n => (1 / (bdd n + 1) : Real) := by
    have : Summable fun l => s (restrictNonposSeq s i l) :=
      HasSum.summable
        (s.m_iUnion (fun _ => restrictNonposSeq_measurableSet _) restrictNonposSeq_disjoint)
    refine .of_nonneg_of_le (fun n => ?_) (fun n => ?_)
        (this.comp_injective Nat.succ_injective)
    · exact le_of_lt Nat.one_div_pos_of_nat
    · exact le_of_lt (restrictNonposSeq_lt n (hn' n))
  have h₃ : Tendsto (fun n => (bdd n : Real) + 1) atTop atTop := by
    simp only [one_div] at h₃'
    exact Summable.tendsto_atTop_of_pos h₃' fun n => Nat.cast_add_one_pos (bdd n)
  have h₄ : Tendsto (fun n => (bdd n : Real)) atTop atTop := by
    convert! atTop.tendsto_atTop_add_const_right (-1) h₃; simp
  have A_meas : MeasurableSet A :=
    hi₁.diff (MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _)
  refine ⟨A, A_meas, Set.sdiff_subset, ?_, h₂.trans_lt hi⟩
  by_contra hnn
  rw [restrict_le_restrict_iff _ _ A_meas] at hnn; push Not at hnn
  obtain ⟨E, hE₁, hE₂, hE₃⟩ := hnn
  have : exists k, 1 <= bdd k ∧ 1 / (bdd k : Real) < s E := by
    rw [tendsto_atTop_atTop] at h₄
    obtain ⟨k, hk⟩ := h₄ (max (1 / s E + 1) 1)
    refine ⟨k, ?_, ?_⟩
    · have hle := le_of_max_le_right (hk k le_rfl)
      norm_cast at hle
    · have : 1 / s E < bdd k := by
        linarith only [le_of_max_le_left (hk k le_rfl)]
      rw [one_div] at this ⊢
      exact inv_lt_of_inv_lt₀ hE₃ this
  obtain ⟨k, hk₁, hk₂⟩ := this
  have hA' : A subseteq i \ ⋃ l <= k, restrictNonposSeq s i l :=
    Set.sdiff_subset_sdiff_right (Set.iUnion₂_subset_iUnion _ _)
  refine
    findExistsOneDivLT_min (hn' k) (Nat.sub_lt hk₁ Nat.zero_lt_one)
      ⟨E, Set.Subset.trans hE₂ hA', hE₁, ?_⟩
  convert! hk₂; norm_cast
  exact tsub_add_cancel_of_le hk₁

end ExistsSubsetRestrictNonpos

/--
Definition of `measureOfNegatives` / `measureOfNegatives` 的定义

English:
definition measureOfNegatives
  signature: (s : SignedMeasure α)
  body: s '' { B | MeasurableSet B ∧ s <=[B] 0 }

中文:
定义 measureOfNegatives
  签名: (s : 符号测度 α)
  定义体: s '' { B | MeasurableSet B ∧ s <=[B] 0 }

Depends on / 依赖: MeasurableSet
-/
def measureOfNegatives (s : SignedMeasure α) : Set Real :=
  s '' { B | MeasurableSet B ∧ s <=[B] 0 }

/--
theorem `zero_mem_measureOfNegatives` / 定理 `zero_mem_measureOfNegatives`

English:
theorem zero_mem_measureOfNegatives
  statement: (0 : Real) in s.measureOfNegatives
  proof: ⟨∅, ⟨MeasurableSet.empty, le_restrict_empty _ _⟩, s.empty⟩

中文:
定理 zero_mem_measureOfNegatives
  结论: (0 : 实数) in s.measureOfNegatives
  证明: ⟨∅, ⟨MeasurableSet.empty, le_restrict_empty _ _⟩, s.empty⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, le_restrict_empty, s.empty
-/
theorem zero_mem_measureOfNegatives : (0 : Real) in s.measureOfNegatives :=
  ⟨∅, ⟨MeasurableSet.empty, le_restrict_empty _ _⟩, s.empty⟩

/--
theorem `bddBelow_measureOfNegatives` / 定理 `bddBelow_measureOfNegatives`

English:
theorem bddBelow_measureOfNegatives
  statement: BddBelow s.measureOfNegatives
  proof: by
  simp_rw [BddBelow, Set.Nonempty, mem_lowerBounds]
  by_contra! h
  have h' : forall n : Nat, exists y : Real, y in s.measureOfNegatives ∧ y < -n := fun n => h (-n)
  choose f hf using h'
  have hf' : forall n : Nat, exists B, MeasurableSet B ∧ s <=[B] 0 ∧ s B < -n := by
    intro n
    rcases hf n with ⟨⟨B, ⟨hB₁, hBr⟩, hB₂⟩, hlt⟩
    exact ⟨B, hB₁, hBr, hB₂.symm ▸ hlt⟩
  choose B hmeas hr h_lt using hf'
  set A := ⋃ n, B n with hA
  have hfalse : forall n : Nat, s A <= -n := by
    intro n
    refine le_trans ?_ (le_of_lt (h_lt _))
    rw [hA]; rw [← Set.sdiff_union_of_subset (Set.subset_iUnion _ n)]; rw [of_union Set.disjoint_sdiff_left _ (hmeas n)]
    · refine add_le_of_nonpos_left ?_
      have : s <=[A] 0 := restrict_le_restrict_iUnion _ _ hmeas hr
      refine nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ ?_ Set.sdiff_subset this)
      exact MeasurableSet.iUnion hmeas
    · exact (MeasurableSet.iUnion hmeas).diff (hmeas n)
  rcases exists_nat_gt (-s A) with ⟨n, hn⟩
  exact lt_irrefl _ ((neg_lt.1 hn).trans_le (hfalse n))

中文:
定理 bddBelow_measureOfNegatives
  结论: BddBelow s.measureOfNegatives
  证明: by
  simp_rw [BddBelow, Set.Nonempty, mem_lowerBounds]
  by_contra! h
  have h' : forall n : Nat, exists y : Real, y in s.measureOfNegatives ∧ y < -n := fun n => h (-n)
  choose f hf using h'
  have hf' : forall n : Nat, exists B, MeasurableSet B ∧ s <=[B] 0 ∧ s B < -n := by
    intro n
    rcases hf n with ⟨⟨B, ⟨hB₁, hBr⟩, hB₂⟩, hlt⟩
    exact ⟨B, hB₁, hBr, hB₂.symm ▸ hlt⟩
  choose B hmeas hr h_lt using hf'
  set A := ⋃ n, B n with hA
  have hfalse : forall n : Nat, s A <= -n := by
    intro n
    refine le_trans ?_ (le_of_lt (h_lt _))
    rw [hA]; rw [← Set.sdiff_union_of_subset (Set.subset_iUnion _ n)]; rw [of_union Set.disjoint_sdiff_left _ (hmeas n)]
    · refine add_le_of_nonpos_left ?_
      have : s <=[A] 0 := restrict_le_restrict_iUnion _ _ hmeas hr
      refine nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ ?_ Set.sdiff_subset this)
      exact MeasurableSet.iUnion hmeas
    · exact (MeasurableSet.iUnion hmeas).diff (hmeas n)
  rcases exists_nat_gt (-s A) with ⟨n, hn⟩
  exact lt_irrefl _ ((neg_lt.1 hn).trans_le (hfalse n))

Depends on / 依赖: BddBelow, MeasurableSet, Nonempty, Set.Nonempty, h_lt, hfalse, le_of_lt, le_trans, measureOfNegatives, mem_lowerBounds, s.measureOfNegatives, simp_rw
-/
theorem bddBelow_measureOfNegatives : BddBelow s.measureOfNegatives := by
  simp_rw [BddBelow, Set.Nonempty, mem_lowerBounds]
  by_contra! h
  have h' : forall n : Nat, exists y : Real, y in s.measureOfNegatives ∧ y < -n := fun n => h (-n)
  choose f hf using h'
  have hf' : forall n : Nat, exists B, MeasurableSet B ∧ s <=[B] 0 ∧ s B < -n := by
    intro n
    rcases hf n with ⟨⟨B, ⟨hB₁, hBr⟩, hB₂⟩, hlt⟩
    exact ⟨B, hB₁, hBr, hB₂.symm ▸ hlt⟩
  choose B hmeas hr h_lt using hf'
  set A := ⋃ n, B n with hA
  have hfalse : forall n : Nat, s A <= -n := by
    intro n
    refine le_trans ?_ (le_of_lt (h_lt _))
    rw [hA]; rw [← Set.sdiff_union_of_subset (Set.subset_iUnion _ n)]; rw [of_union Set.disjoint_sdiff_left _ (hmeas n)]
    · refine add_le_of_nonpos_left ?_
      have : s <=[A] 0 := restrict_le_restrict_iUnion _ _ hmeas hr
      refine nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ ?_ Set.sdiff_subset this)
      exact MeasurableSet.iUnion hmeas
    · exact (MeasurableSet.iUnion hmeas).diff (hmeas n)
  rcases exists_nat_gt (-s A) with ⟨n, hn⟩
  exact lt_irrefl _ ((neg_lt.1 hn).trans_le (hfalse n))

/--
theorem `exists_compl_positive_negative` / 定理 `exists_compl_positive_negative`

English:
theorem exists_compl_positive_negative
  given: (s : SignedMeasure α)
  proof: by
  obtain ⟨f, _, hf₂, hf₁⟩ :=
    exists_seq_tendsto_sInf ⟨0, @zero_mem_measureOfNegatives _ _ s⟩ bddBelow_measureOfNegatives
  choose B hB using hf₁
  have hB₁ : forall n, MeasurableSet (B n) := fun n => (hB n).1.1
  have hB₂ : forall n, s <=[B n] 0 := fun n => (hB n).1.2
  set A := ⋃ n, B n with hA
  have hA₁ : MeasurableSet A := MeasurableSet.iUnion hB₁
  have hA₂ : s <=[A] 0 := restrict_le_restrict_iUnion _ _ hB₁ hB₂
  have hA₃ : s A = sInf s.measureOfNegatives := by
    apply le_antisymm
    · refine le_of_tendsto_of_tendsto tendsto_const_nhds hf₂ (Eventually.of_forall fun n => ?_)
      rw [← (hB n).2]; rw [hA]; rw [← Set.sdiff_union_of_subset (Set.subset_iUnion _ n)]; rw [of_union Set.disjoint_sdiff_left _ (hB₁ n)]
      · refine add_le_of_nonpos_left ?_
        have : s <=[A] 0 :=
          restrict_le_restrict_iUnion _ _ hB₁ fun m =>
            let ⟨_, h⟩ := (hB m).1
            h
        refine
          nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ ?_ Set.sdiff_subset this)
        exact MeasurableSet.iUnion hB₁
      · exact (MeasurableSet.iUnion hB₁).diff (hB₁ n)
    · exact csInf_le bddBelow_measureOfNegatives ⟨A, ⟨hA₁, hA₂⟩, rfl⟩
  refine ⟨Aᶜ, hA₁.compl, ?_, (compl_compl A).symm ▸ hA₂⟩
  rw [restrict_le_restrict_iff _ _ hA₁.compl]
  intro C _ hC₁
  by_contra! hC₂
  rcases exists_subset_restrict_nonpos hC₂ with ⟨D, hD₁, hD, hD₂, hD₃⟩
  have : s (A union D) < sInf s.measureOfNegatives := by
    rw [← hA₃]; rw [of_union (Set.disjoint_of_subset_right (Set.Subset.trans hD hC₁) disjoint_compl_right) hA₁
        hD₁]
    linarith
  refine not_le.2 this ?_
  refine csInf_le bddBelow_measureOfNegatives ⟨A union D, ⟨?_, ?_⟩, rfl⟩
  · exact hA₁.union hD₁
  · exact restrict_le_restrict_union _ _ hA₁ hA₂ hD₁ hD₂

中文:
定理 存在_compl_positive_negative
  条件: (s : 符号测度 α)
  证明: by
  obtain ⟨f, _, hf₂, hf₁⟩ :=
    exists_seq_tendsto_sInf ⟨0, @zero_mem_measureOfNegatives _ _ s⟩ bddBelow_measureOfNegatives
  choose B hB using hf₁
  have hB₁ : forall n, MeasurableSet (B n) := fun n => (hB n).1.1
  have hB₂ : forall n, s <=[B n] 0 := fun n => (hB n).1.2
  set A := ⋃ n, B n with hA
  have hA₁ : MeasurableSet A := MeasurableSet.iUnion hB₁
  have hA₂ : s <=[A] 0 := restrict_le_restrict_iUnion _ _ hB₁ hB₂
  have hA₃ : s A = sInf s.measureOfNegatives := by
    apply le_antisymm
    · refine le_of_tendsto_of_tendsto tendsto_const_nhds hf₂ (Eventually.of_forall fun n => ?_)
      rw [← (hB n).2]; rw [hA]; rw [← Set.sdiff_union_of_subset (Set.subset_iUnion _ n)]; rw [of_union Set.disjoint_sdiff_left _ (hB₁ n)]
      · refine add_le_of_nonpos_left ?_
        have : s <=[A] 0 :=
          restrict_le_restrict_iUnion _ _ hB₁ fun m =>
            let ⟨_, h⟩ := (hB m).1
            h
        refine
          nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ ?_ Set.sdiff_subset this)
        exact MeasurableSet.iUnion hB₁
      · exact (MeasurableSet.iUnion hB₁).diff (hB₁ n)
    · exact csInf_le bddBelow_measureOfNegatives ⟨A, ⟨hA₁, hA₂⟩, rfl⟩
  refine ⟨Aᶜ, hA₁.compl, ?_, (compl_compl A).symm ▸ hA₂⟩
  rw [restrict_le_restrict_iff _ _ hA₁.compl]
  intro C _ hC₁
  by_contra! hC₂
  rcases exists_subset_restrict_nonpos hC₂ with ⟨D, hD₁, hD, hD₂, hD₃⟩
  have : s (A union D) < sInf s.measureOfNegatives := by
    rw [← hA₃]; rw [of_union (Set.disjoint_of_subset_right (Set.Subset.trans hD hC₁) disjoint_compl_right) hA₁
        hD₁]
    linarith
  refine not_le.2 this ?_
  refine csInf_le bddBelow_measureOfNegatives ⟨A union D, ⟨?_, ?_⟩, rfl⟩
  · exact hA₁.union hD₁
  · exact restrict_le_restrict_union _ _ hA₁ hA₂ hD₁ hD₂

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, bddBelow_measureOfNegatives, exists_seq_tendsto_sInf, iUnion, le_antisymm, le_of_tendsto_o, measureOfNegatives, restrict_le_restrict_iUnion, s.measureOfNegatives, zero_mem_measureOfNegatives
-/
theorem exists_compl_positive_negative (s : SignedMeasure α) :
    exists i : Set α, MeasurableSet i ∧ 0 <=[i] s ∧ s <=[iᶜ] 0 := by
  obtain ⟨f, _, hf₂, hf₁⟩ :=
    exists_seq_tendsto_sInf ⟨0, @zero_mem_measureOfNegatives _ _ s⟩ bddBelow_measureOfNegatives
  choose B hB using hf₁
  have hB₁ : forall n, MeasurableSet (B n) := fun n => (hB n).1.1
  have hB₂ : forall n, s <=[B n] 0 := fun n => (hB n).1.2
  set A := ⋃ n, B n with hA
  have hA₁ : MeasurableSet A := MeasurableSet.iUnion hB₁
  have hA₂ : s <=[A] 0 := restrict_le_restrict_iUnion _ _ hB₁ hB₂
  have hA₃ : s A = sInf s.measureOfNegatives := by
    apply le_antisymm
    · refine le_of_tendsto_of_tendsto tendsto_const_nhds hf₂ (Eventually.of_forall fun n => ?_)
      rw [← (hB n).2]; rw [hA]; rw [← Set.sdiff_union_of_subset (Set.subset_iUnion _ n)]; rw [of_union Set.disjoint_sdiff_left _ (hB₁ n)]
      · refine add_le_of_nonpos_left ?_
        have : s <=[A] 0 :=
          restrict_le_restrict_iUnion _ _ hB₁ fun m =>
            let ⟨_, h⟩ := (hB m).1
            h
        refine
          nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ ?_ Set.sdiff_subset this)
        exact MeasurableSet.iUnion hB₁
      · exact (MeasurableSet.iUnion hB₁).diff (hB₁ n)
    · exact csInf_le bddBelow_measureOfNegatives ⟨A, ⟨hA₁, hA₂⟩, rfl⟩
  refine ⟨Aᶜ, hA₁.compl, ?_, (compl_compl A).symm ▸ hA₂⟩
  rw [restrict_le_restrict_iff _ _ hA₁.compl]
  intro C _ hC₁
  by_contra! hC₂
  rcases exists_subset_restrict_nonpos hC₂ with ⟨D, hD₁, hD, hD₂, hD₃⟩
  have : s (A union D) < sInf s.measureOfNegatives := by
    rw [← hA₃]; rw [of_union (Set.disjoint_of_subset_right (Set.Subset.trans hD hC₁) disjoint_compl_right) hA₁
        hD₁]
    linarith
  refine not_le.2 this ?_
  refine csInf_le bddBelow_measureOfNegatives ⟨A union D, ⟨?_, ?_⟩, rfl⟩
  · exact hA₁.union hD₁
  · exact restrict_le_restrict_union _ _ hA₁ hA₂ hD₁ hD₂

/--
theorem `exists_isCompl_positive_negative` / 定理 `exists_isCompl_positive_negative`

English:
theorem exists_isCompl_positive_negative
  given: (s : SignedMeasure α)
  proof: let ⟨i, hi₁, hi₂, hi₃⟩ := exists_compl_positive_negative s
  ⟨i, iᶜ, hi₁, hi₂, hi₁.compl, hi₃, isCompl_compl⟩

中文:
定理 存在_isCompl_positive_negative
  条件: (s : 符号测度 α)
  证明: let ⟨i, hi₁, hi₂, hi₃⟩ := exists_compl_positive_negative s
  ⟨i, iᶜ, hi₁, hi₂, hi₁.compl, hi₃, isCompl_compl⟩

Depends on / 依赖: exists_compl_positive_negative, isCompl_compl
-/
theorem exists_isCompl_positive_negative (s : SignedMeasure α) :
    exists i j : Set α, MeasurableSet i ∧ 0 <=[i] s ∧ MeasurableSet j ∧ s <=[j] 0 ∧ IsCompl i j :=
  let ⟨i, hi₁, hi₂, hi₃⟩ := exists_compl_positive_negative s
  ⟨i, iᶜ, hi₁, hi₂, hi₁.compl, hi₃, isCompl_compl⟩

open scoped symmDiff in
/--
theorem `of_symmDiff_compl_positive_negative` / 定理 `of_symmDiff_compl_positive_negative`

English:
theorem of_symmDiff_compl_positive_negative
  statement: {s : SignedMeasure α} {i j : Set α}
  proof: by
  rw [restrict_le_restrict_iff s 0]; rw [restrict_le_restrict_iff 0 s] at hi' hj'
  constructor
  · rw [Set.symmDiff_def, Set.sdiff_eq_compl_inter, Set.sdiff_eq_compl_inter, of_union,
      le_antisymm (hi'.2 (hi.compl.inter hj) Set.inter_subset_left)
        (hj'.1 (hi.compl.inter hj) Set.inter_subset_right),
      le_antisymm (hj'.2 (hj.compl.inter hi) Set.inter_subset_left)
        (hi'.1 (hj.compl.inter hi) Set.inter_subset_right), zero_apply, zero_apply, zero_add]
    · exact
        Set.disjoint_of_subset_left Set.inter_subset_left
          (Set.disjoint_of_subset_right Set.inter_subset_right
            (disjoint_comm.1 (IsCompl.disjoint isCompl_compl)))
    · exact hj.compl.inter hi
    · exact hi.compl.inter hj
  · rw [Set.symmDiff_def, Set.sdiff_eq_compl_inter, Set.sdiff_eq_compl_inter, compl_compl,
      compl_compl, of_union,
      le_antisymm (hi'.2 (hj.inter hi.compl) Set.inter_subset_right)
        (hj'.1 (hj.inter hi.compl) Set.inter_subset_left),
      le_antisymm (hj'.2 (hi.inter hj.compl) Set.inter_subset_right)
        (hi'.1 (hi.inter hj.compl) Set.inter_subset_left), zero_apply, zero_apply, zero_add]
    · exact
        Set.disjoint_of_subset_left Set.inter_subset_left
          (Set.disjoint_of_subset_right Set.inter_subset_right
            (IsCompl.disjoint isCompl_compl))
    · exact hj.inter hi.compl
    · exact hi.inter hj.compl
  all_goals measurability

中文:
定理 of_symmDiff_compl_positive_negative
  结论: {s : 符号测度 α} {i j : 集合 α}
  证明: by
  rw [restrict_le_restrict_iff s 0]; rw [restrict_le_restrict_iff 0 s] at hi' hj'
  constructor
  · rw [Set.symmDiff_def, Set.sdiff_eq_compl_inter, Set.sdiff_eq_compl_inter, of_union,
      le_antisymm (hi'.2 (hi.compl.inter hj) Set.inter_subset_left)
        (hj'.1 (hi.compl.inter hj) Set.inter_subset_right),
      le_antisymm (hj'.2 (hj.compl.inter hi) Set.inter_subset_left)
        (hi'.1 (hj.compl.inter hi) Set.inter_subset_right), zero_apply, zero_apply, zero_add]
    · exact
        Set.disjoint_of_subset_left Set.inter_subset_left
          (Set.disjoint_of_subset_right Set.inter_subset_right
            (disjoint_comm.1 (IsCompl.disjoint isCompl_compl)))
    · exact hj.compl.inter hi
    · exact hi.compl.inter hj
  · rw [Set.symmDiff_def, Set.sdiff_eq_compl_inter, Set.sdiff_eq_compl_inter, compl_compl,
      compl_compl, of_union,
      le_antisymm (hi'.2 (hj.inter hi.compl) Set.inter_subset_right)
        (hj'.1 (hj.inter hi.compl) Set.inter_subset_left),
      le_antisymm (hj'.2 (hi.inter hj.compl) Set.inter_subset_right)
        (hi'.1 (hi.inter hj.compl) Set.inter_subset_left), zero_apply, zero_apply, zero_add]
    · exact
        Set.disjoint_of_subset_left Set.inter_subset_left
          (Set.disjoint_of_subset_right Set.inter_subset_right
            (IsCompl.disjoint isCompl_compl))
    · exact hj.inter hi.compl
    · exact hi.inter hj.compl
  all_goals measurability

Depends on / 依赖: Set.disjoint_of_subset_left, Set.inter_subset_left, Set.inter_subset_right, Set.sdiff_eq_compl_inter, Set.symmDiff_def, disjoint_of_subset_left, hi.compl.inter, hj.compl.inter, inter_subset_left, inter_subset_right, le_antisymm, of_union, restrict_le_restrict_iff, sdiff_eq_compl_inter, symmDiff_def, zero_add, zero_apply
-/
theorem of_symmDiff_compl_positive_negative {s : SignedMeasure α} {i j : Set α}
    (hi : MeasurableSet i) (hj : MeasurableSet j) (hi' : 0 <=[i] s ∧ s <=[iᶜ] 0)
    (hj' : 0 <=[j] s ∧ s <=[jᶜ] 0) : s (i ∆ j) = 0 ∧ s (iᶜ ∆ jᶜ) = 0 := by
  rw [restrict_le_restrict_iff s 0]; rw [restrict_le_restrict_iff 0 s] at hi' hj'
  constructor
  · rw [Set.symmDiff_def, Set.sdiff_eq_compl_inter, Set.sdiff_eq_compl_inter, of_union,
      le_antisymm (hi'.2 (hi.compl.inter hj) Set.inter_subset_left)
        (hj'.1 (hi.compl.inter hj) Set.inter_subset_right),
      le_antisymm (hj'.2 (hj.compl.inter hi) Set.inter_subset_left)
        (hi'.1 (hj.compl.inter hi) Set.inter_subset_right), zero_apply, zero_apply, zero_add]
    · exact
        Set.disjoint_of_subset_left Set.inter_subset_left
          (Set.disjoint_of_subset_right Set.inter_subset_right
            (disjoint_comm.1 (IsCompl.disjoint isCompl_compl)))
    · exact hj.compl.inter hi
    · exact hi.compl.inter hj
  · rw [Set.symmDiff_def, Set.sdiff_eq_compl_inter, Set.sdiff_eq_compl_inter, compl_compl,
      compl_compl, of_union,
      le_antisymm (hi'.2 (hj.inter hi.compl) Set.inter_subset_right)
        (hj'.1 (hj.inter hi.compl) Set.inter_subset_left),
      le_antisymm (hj'.2 (hi.inter hj.compl) Set.inter_subset_right)
        (hi'.1 (hi.inter hj.compl) Set.inter_subset_left), zero_apply, zero_apply, zero_add]
    · exact
        Set.disjoint_of_subset_left Set.inter_subset_left
          (Set.disjoint_of_subset_right Set.inter_subset_right
            (IsCompl.disjoint isCompl_compl))
    · exact hj.inter hi.compl
    · exact hi.inter hj.compl
  all_goals measurability

end SignedMeasure

end MeasureTheory
