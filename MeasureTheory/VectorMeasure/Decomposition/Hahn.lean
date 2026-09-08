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


/-- Given the set `i` and the natural number `n`, `ExistsOneDivLT s i j` is the property that
there exists a measurable set `k ⊆ i` such that `1 / (n + 1) < s k`. -/
/-
**MeasureTheory.SignedMeasure.ExistsOneDivLT** 是 Mathlib 中的一个定义，位于命名空间 `MeasureT
heory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the set `i` and the natural number `n`, `ExistsOneDivLT s i j` is the prop
erty that
there exists a measurable set `k ⊆ i` such that `1 / (n + 1) < s k`.
-/
private def ExistsOneDivLT (s : SignedMeasure α) (i : Set α) (n : ℕ) : Prop :=
  ∃ k : Set α, k ⊆ i ∧ MeasurableSet k ∧ (1 / (n + 1) : ℝ) < s k
/-
**MeasureTheory.SignedMeasure.existsNatOneDivLTMeasure_of_not_negative** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem existsNatOneDivLTMeasure_of_not_negative (hi : ¬s ≤[i] 0) :
    ∃ n : ℕ, ExistsOneDivLT s i n :=
  let ⟨k, hj₁, hj₂, hj⟩ := exists_pos_measure_of_not_restrict_le_zero s hi
  let ⟨n, hn⟩ := exists_nat_one_div_lt hj
  ⟨n, k, hj₂, hj₁, hn⟩

open scoped Classical in
/-- Given the set `i`, if `i` is not negative, `findExistsOneDivLT s i` is the
least natural number `n` such that `ExistsOneDivLT s i n`, otherwise, it returns 0. -/
/-
**MeasureTheory.SignedMeasure.findExistsOneDivLT** 是 Mathlib 中的一个定义，位于命名空间 `Meas
ureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the set `i`, if `i` is not negative, `findExistsOneDivLT s i` is the
least natural number `n` such that `ExistsOneDivLT s i n`, otherwise, it returns
 0.
-/
private def findExistsOneDivLT (s : SignedMeasure α) (i : Set α) : ℕ :=
  if hi : ¬s ≤[i] 0 then Nat.find (existsNatOneDivLTMeasure_of_not_negative hi) else 0
/-
**MeasureTheory.SignedMeasure.findExistsOneDivLT_spec** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem findExistsOneDivLT_spec (hi : ¬s ≤[i] 0) :
    ExistsOneDivLT s i (findExistsOneDivLT s i) := by
  rw [findExistsOneDivLT, dif_pos hi]
  convert! Nat.find_spec (existsNatOneDivLTMeasure_of_not_negative hi)
/-
**MeasureTheory.SignedMeasure.findExistsOneDivLT_min** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem findExistsOneDivLT_min (hi : ¬s ≤[i] 0) {m : ℕ}
    (hm : m < findExistsOneDivLT s i) : ¬ExistsOneDivLT s i m := by
  classical
  rw [findExistsOneDivLT, dif_pos hi] at hm
  exact Nat.find_min _ hm

open scoped Classical in
/-- Given the set `i`, if `i` is not negative, `someExistsOneDivLT` chooses the set
`k` from `ExistsOneDivLT s i (findExistsOneDivLT s i)`, otherwise, it returns the
empty set. -/
/-
**MeasureTheory.SignedMeasure.someExistsOneDivLT** 是 Mathlib 中的一个定义，位于命名空间 `Meas
ureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the set `i`, if `i` is not negative, `someExistsOneDivLT` chooses the set
`k` from `ExistsOneDivLT s i (findExistsOneDivLT s i)`, otherwise, it returns th
e
empty set.
-/
private def someExistsOneDivLT (s : SignedMeasure α) (i : Set α) : Set α :=
  if hi : ¬s ≤[i] 0 then Classical.choose (findExistsOneDivLT_spec hi) else ∅
/-
**MeasureTheory.SignedMeasure.someExistsOneDivLT_spec** 是 Mathlib 中的一个定理，位于命名空间 
`MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem someExistsOneDivLT_spec (hi : ¬s ≤[i] 0) :
    someExistsOneDivLT s i ⊆ i ∧
      MeasurableSet (someExistsOneDivLT s i) ∧
        (1 / (findExistsOneDivLT s i + 1) : ℝ) < s (someExistsOneDivLT s i) := by
  rw [someExistsOneDivLT, dif_pos hi]
  exact Classical.choose_spec (findExistsOneDivLT_spec hi)
/-
**MeasureTheory.SignedMeasure.someExistsOneDivLT_subset** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem someExistsOneDivLT_subset : someExistsOneDivLT s i ⊆ i := by
  by_cases hi : ¬s ≤[i] 0
  · exact
      let ⟨h, _⟩ := someExistsOneDivLT_spec hi
      h
  · rw [someExistsOneDivLT, dif_neg hi]
    exact Set.empty_subset _
/-
**MeasureTheory.SignedMeasure.someExistsOneDivLT_subset'** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem someExistsOneDivLT_subset' : someExistsOneDivLT s (i \ j) ⊆ i :=
  someExistsOneDivLT_subset.trans Set.sdiff_subset
/-
**MeasureTheory.SignedMeasure.someExistsOneDivLT_measurableSet** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem someExistsOneDivLT_measurableSet : MeasurableSet (someExistsOneDivLT s i) := by
  by_cases hi : ¬s ≤[i] 0
  · exact
      let ⟨_, h, _⟩ := someExistsOneDivLT_spec hi
      h
  · rw [someExistsOneDivLT, dif_neg hi]
    exact MeasurableSet.empty
/-
**MeasureTheory.SignedMeasure.someExistsOneDivLT_lt** 是 Mathlib 中的一个定理，位于命名空间 `M
easureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem someExistsOneDivLT_lt (hi : ¬s ≤[i] 0) :
    (1 / (findExistsOneDivLT s i + 1) : ℝ) < s (someExistsOneDivLT s i) :=
  let ⟨_, _, h⟩ := someExistsOneDivLT_spec hi
  h

/-- Given the set `i`, `restrictNonposSeq s i` is the sequence of sets defined inductively where
`restrictNonposSeq s i 0 = someExistsOneDivLT s (i \ ∅)` and
`restrictNonposSeq s i (n + 1) = someExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonposSeq k)`.

For each `n : ℕ`,`s (restrictNonposSeq s i n)` is close to maximal among all subsets of
`i \ ⋃ k ≤ n, restrictNonposSeq s i k`. -/
/-
**MeasureTheory.SignedMeasure.restrictNonposSeq** 是 Mathlib 中的一个定义，位于命名空间 `Measu
reTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the set `i`, `restrictNonposSeq s i` is the sequence of sets defined induc
tively where
`restrictNonposSeq s i 0 = someExistsOneDivLT s (i \ ∅)` and
`restrictNonposSeq s i (n + 1) = someExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonp
osSeq k)`.

For each `n : ℕ`,`s (restrictNonposSeq s i n)` is close to maximal among all sub
sets of
`i \ ⋃ k ≤ n, restrictNonposSeq s i k`.
-/
private def restrictNonposSeq (s : SignedMeasure α) (i : Set α) : ℕ → Set α
  | 0 => someExistsOneDivLT s (i \ ∅) -- I used `i \ ∅` instead of `i` to simplify some proofs
  | n + 1 =>
    someExistsOneDivLT s
      (i \
        ⋃ (k) (H : k ≤ n),
          have : k < n + 1 := Nat.lt_succ_iff.mpr H
          restrictNonposSeq s i k)
/-
**MeasureTheory.SignedMeasure.restrictNonposSeq_succ** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem restrictNonposSeq_succ (n : ℕ) :
    restrictNonposSeq s i n.succ = someExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonposSeq s i k) := by
  rw [restrictNonposSeq]
/-
**MeasureTheory.SignedMeasure.restrictNonposSeq_subset** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem restrictNonposSeq_subset (n : ℕ) : restrictNonposSeq s i n ⊆ i := by
  cases n <;> · rw [restrictNonposSeq]; exact someExistsOneDivLT_subset'
/-
**MeasureTheory.SignedMeasure.restrictNonposSeq_lt** 是 Mathlib 中的一个定理，位于命名空间 `Me
asureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem restrictNonposSeq_lt (n : ℕ) (hn : ¬s ≤[i \ ⋃ k ≤ n, restrictNonposSeq s i k] 0) :
    (1 / (findExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonposSeq s i k) + 1) : ℝ) <
      s (restrictNonposSeq s i n.succ) := by
  rw [restrictNonposSeq_succ]
  apply someExistsOneDivLT_lt hn
/-
**MeasureTheory.SignedMeasure.measure_of_restrictNonposSeq** 是 Mathlib 中的一个定理，位于
命名空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem measure_of_restrictNonposSeq (hi₂ : ¬s ≤[i] 0) (n : ℕ)
    (hn : ¬s ≤[i \ ⋃ k < n, restrictNonposSeq s i k] 0) : 0 < s (restrictNonposSeq s i n) := by
  cases n with
  | zero =>
    rw [restrictNonposSeq]; rw [← @Set.sdiff_empty _ i] at hi₂
    rcases someExistsOneDivLT_spec hi₂ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h
  | succ n =>
    rw [restrictNonposSeq_succ]
    have h₁ : ¬s ≤[i \ ⋃ (k : ℕ) (_ : k ≤ n), restrictNonposSeq s i k] 0 := by
      refine mt (restrict_le_zero_subset _ ?_ (by simp)) hn
      convert! measurable_of_not_restrict_le_zero _ hn using 3
      exact funext fun x => by rw [Nat.lt_succ_iff]
    rcases someExistsOneDivLT_spec h₁ with ⟨_, _, h⟩
    exact lt_trans Nat.one_div_pos_of_nat h
/-
**MeasureTheory.SignedMeasure.restrictNonposSeq_measurableSet** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem restrictNonposSeq_measurableSet (n : ℕ) :
    MeasurableSet (restrictNonposSeq s i n) := by
  cases n <;>
    · rw [restrictNonposSeq]
      exact someExistsOneDivLT_measurableSet
/-
**MeasureTheory.SignedMeasure.restrictNonposSeq_disjoint'** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem restrictNonposSeq_disjoint' {n m : ℕ} (h : n < m) :
    restrictNonposSeq s i n ∩ restrictNonposSeq s i m = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx₁, hx₂⟩
  cases m; · lia
  · rw [restrictNonposSeq] at hx₂
    exact
      (someExistsOneDivLT_subset hx₂).2
        (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion.2 ⟨Nat.lt_succ_iff.mp h, hx₁⟩⟩)

open scoped Function in -- required for scoped `on` notation
/-
**MeasureTheory.SignedMeasure.restrictNonposSeq_disjoint** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem restrictNonposSeq_disjoint : Pairwise (Disjoint on restrictNonposSeq s i) := by
  intro n m h
  rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
  rcases lt_or_gt_of_ne h with (h | h)
  · rw [restrictNonposSeq_disjoint' h]
  · rw [Set.inter_comm, restrictNonposSeq_disjoint' h]
/-
**MeasureTheory.SignedMeasure.exists_subset_restrict_nonpos'** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.SignedMeasure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exists_subset_restrict_nonpos' (hi₁ : MeasurableSet i) (hi₂ : s i < 0)
    (hn : ¬∀ n : ℕ, ¬s ≤[i \ ⋃ l < n, restrictNonposSeq s i l] 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ s ≤[j] 0 ∧ s j < 0 := by
  classical
  by_cases h : s ≤[i] 0
  · exact ⟨i, hi₁, Set.Subset.refl _, h, hi₂⟩
  push Not at hn
  set k := Nat.find hn
  have hk₂ : s ≤[i \ ⋃ l < k, restrictNonposSeq s i l] 0 := Nat.find_spec hn
  have hmeas : MeasurableSet (⋃ (l : ℕ) (_ : l < k), restrictNonposSeq s i l) :=
    MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
  refine ⟨i \ ⋃ l < k, restrictNonposSeq s i l, hi₁.diff hmeas, Set.sdiff_subset, hk₂, ?_⟩
  rw [of_sdiff hmeas hi₁, s.of_disjoint_iUnion]
  · have h₁ : ∀ l < k, 0 ≤ s (restrictNonposSeq s i l) := by
      intro l hl
      refine le_of_lt (measure_of_restrictNonposSeq h _ ?_)
      refine mt (restrict_le_zero_subset _ (hi₁.diff ?_) (Set.Subset.refl _)) (Nat.find_min hn hl)
      exact
        MeasurableSet.iUnion fun _ =>
          MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    suffices 0 ≤ ∑' l : ℕ, s (⋃ _ : l < k, restrictNonposSeq s i l) by
      rw [sub_neg]
      exact lt_of_lt_of_le hi₂ this
    refine tsum_nonneg ?_
    intro l; by_cases h : l < k
    · convert! h₁ _ h
      ext x
      rw [Set.mem_iUnion, exists_prop, and_iff_right_iff_imp]
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

/-- A measurable set of negative measure has a negative subset of negative measure. -/
/-
**MeasureTheory.SignedMeasure.exists_subset_restrict_nonpos** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：exists_subset_restrict_nonpos (hi : s i < 0) : exists j : Set α, Measurabl
eSet j ∧ j subseteq i ∧ s <=[j] 0 ∧ s j < 0
参数：hi : s i < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `MeasureTheory.VectorMeasure.not_measurable`：not_measurable (v : VectorMe
asure α M) {i : Set α} (hi : ¬MeasurableSet i) : v i = 0
· 使用定理 `Set.Subset.refl`：∀ {α : Type u} (a : Set α), a ⊆ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `MeasureTheory.VectorMeasure.of_disjoint_iUnion`：of_disjoint_iUnion (hm :
 forall i, MeasurableSet (f i)) (hd : Pairwise (Disjoint on f)) : v (⋃ i, f i) =
 ∑' i, v (f i)
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn.0.Measur
eTheory.SignedMeasure.restrictNonposSeq_measurableSet`：∀ {α : Type u_1} [inst : 
MeasurableSpace α] {s : MeasureTheory.SignedMeasure α} {i : Set α} (n : ℕ),   Me
asurableSet (MeasureTheory.SignedMe…
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn.0.Measur
eTheory.SignedMeasure.restrictNonposSeq_disjoint`：∀ {α : Type u_1} [inst : Measu
rableSpace α] {s : MeasureTheory.SignedMeasure α} {i : Set α},   Pairwise (Funct
ion.onFun Disjoint (MeasureThe…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `MeasureTheory.VectorMeasure.of_add_of_sdiff`：of_add_of_sdiff {A B : Set 
α} (hA : MeasurableSet A) (hB : MeasurableSet B) (h : A subseteq B) : v A + v (B
 \ A) = v B
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `Set.iUnion_subset`：iUnion_subset {s : ι -> Set α} {t : Set α} (h : foral
l i, s i subseteq t) : ⋃ i, s i subseteq t
· 使用定理 `_private.Mathlib.MeasureTheory.VectorMeasure.Decomposition.Hahn.0.Measur
eTheory.SignedMeasure.restrictNonposSeq_subset`：∀ {α : Type u_1} [inst : Measura
bleSpace α] {s : MeasureTheory.SignedMeasure α} {i : Set α} (n : ℕ),   MeasureTh
eory.SignedMeasure.restrictN…
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `tsum_nonneg`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilter ι} [in
st : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [inst_3 : T
o…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 129 条，此处仅展示前 30 条）

--- 原说明 ---
A measurable set of negative measure has a negative subset of negative measure.
-/
theorem exists_subset_restrict_nonpos (hi : s i < 0) :
    ∃ j : Set α, MeasurableSet j ∧ j ⊆ i ∧ s ≤[j] 0 ∧ s j < 0 := by
  have hi₁ : MeasurableSet i := by_contradiction fun h => ne_of_lt hi <| s.not_measurable h
  by_cases h : s ≤[i] 0; · exact ⟨i, hi₁, Set.Subset.refl _, h, hi⟩
  by_cases hn : ∀ n : ℕ, ¬s ≤[i \ ⋃ l < n, restrictNonposSeq s i l] 0
  swap; · exact exists_subset_restrict_nonpos' hi₁ hi hn
  set A := i \ ⋃ l, restrictNonposSeq s i l with hA
  set bdd : ℕ → ℕ := fun n => findExistsOneDivLT s (i \ ⋃ k ≤ n, restrictNonposSeq s i k)
  have hn' : ∀ n : ℕ, ¬s ≤[i \ ⋃ l ≤ n, restrictNonposSeq s i l] 0 := by
    intro n
    convert! hn (n + 1) using 5 <;>
      · ext l
        simp only [exists_prop, Set.mem_iUnion, and_congr_left_iff]
        exact fun _ => Nat.lt_succ_iff.symm
  have h₁ : s i = s A + ∑' l, s (restrictNonposSeq s i l) := by
    rw [hA, ← s.of_disjoint_iUnion, add_comm, of_add_of_sdiff]
    · exact MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _
    exacts [hi₁, Set.iUnion_subset fun _ => restrictNonposSeq_subset _, fun _ =>
      restrictNonposSeq_measurableSet _, restrictNonposSeq_disjoint]
  have h₂ : s A ≤ s i := by
    rw [h₁]
    apply le_add_of_nonneg_right
    exact tsum_nonneg fun n => le_of_lt (measure_of_restrictNonposSeq h _ (hn n))
  have h₃' : Summable fun n => (1 / (bdd n + 1) : ℝ) := by
    have : Summable fun l => s (restrictNonposSeq s i l) :=
      HasSum.summable
        (s.m_iUnion (fun _ => restrictNonposSeq_measurableSet _) restrictNonposSeq_disjoint)
    refine .of_nonneg_of_le (fun n => ?_) (fun n => ?_)
        (this.comp_injective Nat.succ_injective)
    · exact le_of_lt Nat.one_div_pos_of_nat
    · exact le_of_lt (restrictNonposSeq_lt n (hn' n))
  have h₃ : Tendsto (fun n => (bdd n : ℝ) + 1) atTop atTop := by
    simp only [one_div] at h₃'
    exact Summable.tendsto_atTop_of_pos h₃' fun n => Nat.cast_add_one_pos (bdd n)
  have h₄ : Tendsto (fun n => (bdd n : ℝ)) atTop atTop := by
    convert! atTop.tendsto_atTop_add_const_right (-1) h₃; simp
  have A_meas : MeasurableSet A :=
    hi₁.diff (MeasurableSet.iUnion fun _ => restrictNonposSeq_measurableSet _)
  refine ⟨A, A_meas, Set.sdiff_subset, ?_, h₂.trans_lt hi⟩
  by_contra hnn
  rw [restrict_le_restrict_iff _ _ A_meas] at hnn; push Not at hnn
  obtain ⟨E, hE₁, hE₂, hE₃⟩ := hnn
  have : ∃ k, 1 ≤ bdd k ∧ 1 / (bdd k : ℝ) < s E := by
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
  have hA' : A ⊆ i \ ⋃ l ≤ k, restrictNonposSeq s i l :=
    Set.sdiff_subset_sdiff_right (Set.iUnion₂_subset_iUnion _ _)
  refine
    findExistsOneDivLT_min (hn' k) (Nat.sub_lt hk₁ Nat.zero_lt_one)
      ⟨E, Set.Subset.trans hE₂ hA', hE₁, ?_⟩
  convert! hk₂; norm_cast
  exact tsub_add_cancel_of_le hk₁

end ExistsSubsetRestrictNonpos

/-- The set of measures of the set of measurable negative sets. -/
/-
**MeasureTheory.SignedMeasure.measureOfNegatives** 是 Mathlib 中的一个定义，位于命名空间 `Meas
ureTheory.SignedMeasure`。
形式化陈述：measureOfNegatives (s : SignedMeasure α) : Set Real
参数：s : SignedMeasure α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of measures of the set of measurable negative sets.
-/
def measureOfNegatives (s : SignedMeasure α) : Set ℝ :=
  s '' { B | MeasurableSet B ∧ s ≤[B] 0 }
/-
**MeasureTheory.SignedMeasure.zero_mem_measureOfNegatives** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：zero_mem_measureOfNegatives : (0 : Real) in s.measureOfNegatives
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.empty`：MeasurableSet.empty [MeasurableSpace α] : Measurabl
eSet (∅ : Set α)
· 使用定理 `MeasureTheory.VectorMeasure.le_restrict_empty`：le_restrict_empty : v <=[
∅] w
· 使用定理 `MeasureTheory.VectorMeasure.empty`：empty (v : VectorMeasure α M) : v ∅ =
 0
-/
theorem zero_mem_measureOfNegatives : (0 : ℝ) ∈ s.measureOfNegatives :=
  ⟨∅, ⟨MeasurableSet.empty, le_restrict_empty _ _⟩, s.empty⟩
/-
**MeasureTheory.SignedMeasure.bddBelow_measureOfNegatives** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：bddBelow_measureOfNegatives : BddBelow s.measureOfNegatives
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_le_of_nonpos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, b ≤ 0 → b + a ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iUnion`：restrict_le_res
trict_iUnion {f : Nat -> Set α} (hf₁ : forall n, MeasurableSet (f n)) (hf₂ : for
all n, v <=[f n] w) : v <=[⋃ n, f n] w
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.VectorMeasure.nonpos_of_restrict_le_zero`：nonpos_of_restri
ct_le_zero (hi₂ : v <=[i] 0) : v i <= 0
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_zero_subset`：restrict_le_zero_su
bset (hi₁ : MeasurableSet i) (hij : j subseteq i) (hi₂ : v <=[i] 0) : v <=[j] 0
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
（共 43 条，此处仅展示前 30 条）
-/
theorem bddBelow_measureOfNegatives : BddBelow s.measureOfNegatives := by
  simp_rw [BddBelow, Set.Nonempty, mem_lowerBounds]
  by_contra! h
  have h' : ∀ n : ℕ, ∃ y : ℝ, y ∈ s.measureOfNegatives ∧ y < -n := fun n => h (-n)
  choose f hf using h'
  have hf' : ∀ n : ℕ, ∃ B, MeasurableSet B ∧ s ≤[B] 0 ∧ s B < -n := by
    intro n
    rcases hf n with ⟨⟨B, ⟨hB₁, hBr⟩, hB₂⟩, hlt⟩
    exact ⟨B, hB₁, hBr, hB₂.symm ▸ hlt⟩
  choose B hmeas hr h_lt using hf'
  set A := ⋃ n, B n with hA
  have hfalse : ∀ n : ℕ, s A ≤ -n := by
    intro n
    refine le_trans ?_ (le_of_lt (h_lt _))
    rw [hA, ← Set.sdiff_union_of_subset (Set.subset_iUnion _ n),
      of_union Set.disjoint_sdiff_left _ (hmeas n)]
    · refine add_le_of_nonpos_left ?_
      have : s ≤[A] 0 := restrict_le_restrict_iUnion _ _ hmeas hr
      refine nonpos_of_restrict_le_zero _ (restrict_le_zero_subset _ ?_ Set.sdiff_subset this)
      exact MeasurableSet.iUnion hmeas
    · exact (MeasurableSet.iUnion hmeas).diff (hmeas n)
  rcases exists_nat_gt (-s A) with ⟨n, hn⟩
  exact lt_irrefl _ ((neg_lt.1 hn).trans_le (hfalse n))

/-- Alternative formulation of `MeasureTheory.SignedMeasure.exists_isCompl_positive_negative`
(the Hahn decomposition theorem) using set complements. -/
/-
**MeasureTheory.SignedMeasure.exists_compl_positive_negative** 是 Mathlib 中的一个定理，
位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：exists_compl_positive_negative (s : SignedMeasure α) : exists i : Set α, M
easurableSet i ∧ 0 <=[i] s ∧ s <=[iᶜ] 0
参数：s : SignedMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_tendsto_sInf`：exists_seq_tendsto_sInf {α : Type*} [Conditiona
llyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [FirstCountable
Topology α] {…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `MeasureTheory.SignedMeasure.zero_mem_measureOfNegatives`：zero_mem_measur
eOfNegatives : (0 : Real) in s.measureOfNegatives
· 使用定理 `MeasureTheory.SignedMeasure.bddBelow_measureOfNegatives`：bddBelow_measur
eOfNegatives : BddBelow s.measureOfNegatives
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iUnion`：restrict_le_res
trict_iUnion {f : Nat -> Set α} (hf₁ : forall n, MeasurableSet (f n)) (hf₂ : for
all n, v <=[f n] w) : v <=[⋃ n, f n] w
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_tendsto_of_tendsto`：le_of_tendsto_of_tendsto {f g : β -> α} {b : F
ilter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b 
(𝓝 a₂)) (h : f…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sdiff_union_of_subset`：sdiff_union_of_subset {s t : Set α} (h : t su
bseteq s) : s \ t union t = s
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `MeasurableSet.diff`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : Se
t α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ \ s₂)
· 使用定理 `add_le_of_nonpos_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, b ≤ 0 → b + a ≤ a
（共 77 条，此处仅展示前 30 条）

--- 原说明 ---
Alternative formulation of `MeasureTheory.SignedMeasure.exists_isCompl_positive_
negative`
(the Hahn decomposition theorem) using set complements.
-/
theorem exists_compl_positive_negative (s : SignedMeasure α) :
    ∃ i : Set α, MeasurableSet i ∧ 0 ≤[i] s ∧ s ≤[iᶜ] 0 := by
  obtain ⟨f, _, hf₂, hf₁⟩ :=
    exists_seq_tendsto_sInf ⟨0, @zero_mem_measureOfNegatives _ _ s⟩ bddBelow_measureOfNegatives
  choose B hB using hf₁
  have hB₁ : ∀ n, MeasurableSet (B n) := fun n => (hB n).1.1
  have hB₂ : ∀ n, s ≤[B n] 0 := fun n => (hB n).1.2
  set A := ⋃ n, B n with hA
  have hA₁ : MeasurableSet A := MeasurableSet.iUnion hB₁
  have hA₂ : s ≤[A] 0 := restrict_le_restrict_iUnion _ _ hB₁ hB₂
  have hA₃ : s A = sInf s.measureOfNegatives := by
    apply le_antisymm
    · refine le_of_tendsto_of_tendsto tendsto_const_nhds hf₂ (Eventually.of_forall fun n => ?_)
      rw [← (hB n).2, hA, ← Set.sdiff_union_of_subset (Set.subset_iUnion _ n),
        of_union Set.disjoint_sdiff_left _ (hB₁ n)]
      · refine add_le_of_nonpos_left ?_
        have : s ≤[A] 0 :=
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
  have : s (A ∪ D) < sInf s.measureOfNegatives := by
    rw [← hA₃,
      of_union (Set.disjoint_of_subset_right (Set.Subset.trans hD hC₁) disjoint_compl_right) hA₁
        hD₁]
    linarith
  refine not_le.2 this ?_
  refine csInf_le bddBelow_measureOfNegatives ⟨A ∪ D, ⟨?_, ?_⟩, rfl⟩
  · exact hA₁.union hD₁
  · exact restrict_le_restrict_union _ _ hA₁ hA₂ hD₁ hD₂

/-- **The Hahn decomposition theorem**: Given a signed measure `s`, there exist
complement measurable sets `i` and `j` such that `i` is positive, `j` is negative. -/
/-
**MeasureTheory.SignedMeasure.exists_isCompl_positive_negative** 是 Mathlib 中的一个定
理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：exists_isCompl_positive_negative (s : SignedMeasure α) : exists i j : Set 
α, MeasurableSet i ∧ 0 <=[i] s ∧ MeasurableSet j ∧ s <=[j] 0 ∧ IsCompl i j
参数：s : SignedMeasure α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SignedMeasure.exists_compl_positive_negative`：exists_compl
_positive_negative (s : SignedMeasure α) : exists i : Set α, MeasurableSet i ∧ 0
 <=[i] s ∧ s <=[iᶜ] 0
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ

--- 原说明 ---
**The Hahn decomposition theorem**: Given a signed measure `s`, there exist
complement measurable sets `i` and `j` such that `i` is positive, `j` is negativ
e.
-/
theorem exists_isCompl_positive_negative (s : SignedMeasure α) :
    ∃ i j : Set α, MeasurableSet i ∧ 0 ≤[i] s ∧ MeasurableSet j ∧ s ≤[j] 0 ∧ IsCompl i j :=
  let ⟨i, hi₁, hi₂, hi₃⟩ := exists_compl_positive_negative s
  ⟨i, iᶜ, hi₁, hi₂, hi₁.compl, hi₃, isCompl_compl⟩

open scoped symmDiff in
/-- The symmetric difference of two Hahn decompositions has measure zero. -/
/-
**MeasureTheory.SignedMeasure.of_symmDiff_compl_positive_negative** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory.SignedMeasure`。
形式化陈述：of_symmDiff_compl_positive_negative {s : SignedMeasure α} {i j : Set α} (h
i : MeasurableSet i) (hj : MeasurableSet j) (hi' : 0 <=[i] s ∧ s <=[iᶜ] 0) (hj' 
: 0 <=[j] s ∧ s <=[jᶜ] 0) : s (i ∆ j) = 0 ∧ s (iᶜ ∆ jᶜ) = 0
参数：hi : MeasurableSet i；hj : MeasurableSet j；hi' : 0 <=[i] s ∧ s <=[iᶜ] 0；hj' : 
0 <=[j] s ∧ s <=[jᶜ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.symmDiff_def`：∀ {α : Type u} (s t : Set α), symmDiff s t = s \ t ∪ t
 \ s
· 使用定理 `Set.sdiff_eq_compl_inter`：sdiff_eq_compl_inter {s t : Set α} : s \ t = t
ᶜ inter s
· 使用定理 `MeasureTheory.VectorMeasure.of_union`：of_union {A B : Set α} (h : Disjoi
nt A B) (hA : MeasurableSet A) (hB : MeasurableSet B) : v (A union B) = v A + v 
B
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Set.disjoint_of_subset_left`：disjoint_of_subset_left (h : s subseteq u) 
(d : Disjoint u t) : Disjoint s t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用引理 `Set.disjoint_of_subset_right`：disjoint_of_subset_right (h : t subseteq u
) (d : Disjoint s u) : Disjoint s t
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.VectorMeasure.restrict_le_restrict_iff`：restrict_le_restri
ct_iff {i : Set α} (hi : MeasurableSet i) : v <=[i] w ↔ forall ⦃j⦄, MeasurableSe
t j -> j subseteq i -> v j <= w j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `MeasureTheory.VectorMeasure.instIsZeroApplySet`：∀ {α : Type u_1} {m : Me
asurableSpace α} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : TopologicalSp
ace M],   IsZeroApply (MeasureTheory…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x

--- 原说明 ---
The symmetric difference of two Hahn decompositions has measure zero.
-/
theorem of_symmDiff_compl_positive_negative {s : SignedMeasure α} {i j : Set α}
    (hi : MeasurableSet i) (hj : MeasurableSet j) (hi' : 0 ≤[i] s ∧ s ≤[iᶜ] 0)
    (hj' : 0 ≤[j] s ∧ s ≤[jᶜ] 0) : s (i ∆ j) = 0 ∧ s (iᶜ ∆ jᶜ) = 0 := by
  rw [restrict_le_restrict_iff s 0, restrict_le_restrict_iff 0 s] at hi' hj'
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

