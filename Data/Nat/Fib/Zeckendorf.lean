/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Nat.Fib.Basic

/-!
# Zeckendorf's Theorem

This file proves Zeckendorf's theorem: Every natural number can be written uniquely as a sum of
distinct non-consecutive Fibonacci numbers.

## Main declarations

* `List.IsZeckendorfRep`: Predicate for a list to be an increasing sequence of non-consecutive
  natural numbers greater than or equal to `2`, namely a Zeckendorf representation.
* `Nat.greatestFib`: Greatest index of a Fibonacci number less than or equal to some natural.
* `Nat.zeckendorf`: Send a natural number to its Zeckendorf representation.
* `Nat.zeckendorfEquiv`: Zeckendorf's theorem, in the form of an equivalence between natural numbers
  and Zeckendorf representations.

## TODO

We could prove that the order induced by `zeckendorfEquiv` on Zeckendorf representations is exactly
the lexicographic order.

## Tags

fibonacci, zeckendorf, digit
-/

@[expose] public section

open List Nat

-- TODO: The `local` attribute makes this not considered as an instance by linters
@[nolint docBlame]
local instance : IsTrans Nat fun a b => b + 2 <= a where
trans _a _b _c hba hcb := hcb.trans le_self_add.trans hba

namespace List

/--
Definition of `IsZeckendorfRep` / `IsZeckendorfRep` 的定义

English:
definition IsZeckendorfRep
  signature: (l : List Nat)
  body: (l ++ [0]).IsChain (fun a b => b + 2 <= a)

@[simp]

中文:
定义 IsZeckendorfRep
  签名: (l : 列表 自然数)
  定义体: (l ++ [0]).IsChain (fun a b => b + 2 <= a)

@[simp]

Depends on / 依赖: IsChain
-/
def IsZeckendorfRep (l : List Nat) : Prop := (l ++ [0]).IsChain (fun a b => b + 2 <= a)

@[simp]
/--
lemma `IsZeckendorfRep_nil` / 引理 `IsZeckendorfRep_nil`

English:
lemma IsZeckendorfRep_nil
  statement: IsZeckendorfRep []
  proof: by simp [IsZeckendorfRep]

中文:
引理 IsZeckendorfRep_nil
  结论: IsZeckendorfRep []
  证明: by simp [IsZeckendorfRep]

Depends on / 依赖: IsZeckendorfRep
-/
lemma IsZeckendorfRep_nil : IsZeckendorfRep [] := by simp [IsZeckendorfRep]

/--
lemma `IsZeckendorfRep.sum_fib_lt` / 引理 `IsZeckendorfRep.sum_fib_lt`

English:
lemma IsZeckendorfRep.sum_fib_lt
  statement: forall {n l}, IsZeckendorfRep l -> (forall a in (l ++ [0]).head?, a < n) ->
  proof: fun b hb => lt_tsub_iff_right.2 hl.1 _ mem_of_mem_head? hb
    simp only [mem_append, mem_singleton, ← isChain_iff_pairwise, or_imp, forall_and, forall_eq,
      zero_add] at hl
    calc
      fib a + (map fib l).sum < fib a + fib (a - 1) := by gcongr; exact sum_fib_lt hl.2 this
      _ <= fib n := by
        rw [add_comm]; rw [← fib_add_one (hl.1.2.trans_lt' zero_lt_two).ne']; exact fib_mono (hn _ rfl)

中文:
引理 IsZeckendorfRep.sum_fib_lt
  结论: 对任意 {n l}, IsZeckendorfRep l -> (对任意 a in (l ++ [0]).head?, a < n) ->
  证明: fun b hb => lt_tsub_iff_right.2 hl.1 _ mem_of_mem_head? hb
    simp only [mem_append, mem_singleton, ← isChain_iff_pairwise, or_imp, forall_and, forall_eq,
      zero_add] at hl
    calc
      fib a + (map fib l).sum < fib a + fib (a - 1) := by gcongr; exact sum_fib_lt hl.2 this
      _ <= fib n := by
        rw [add_comm]; rw [← fib_add_one (hl.1.2.trans_lt' zero_lt_two).ne']; exact fib_mono (hn _ rfl)

Depends on / 依赖: add_comm, fib_add_one, fib_mono, forall_and, forall_eq, isChain_iff_pairwise, lt_tsub_iff_right, mem_append, mem_of_mem_head, mem_singleton, or_imp, sum_fib_lt, trans_lt, zero_add, zero_lt_two
-/
lemma IsZeckendorfRep.sum_fib_lt : forall {n l}, IsZeckendorfRep l -> (forall a in (l ++ [0]).head?, a < n) ->
    (l.map fib).sum < fib n
| _, [], _, hn => fib_pos.2 hn _ rfl
  | n, a :: l, hl, hn => by
    simp only [IsZeckendorfRep, cons_append, isChain_iff_pairwise, pairwise_cons] at hl
    have : forall b, b in head? (l ++ [0]) -> b < a - 1 :=
fun b hb => lt_tsub_iff_right.2 hl.1 _ mem_of_mem_head? hb
    simp only [mem_append, mem_singleton, ← isChain_iff_pairwise, or_imp, forall_and, forall_eq,
      zero_add] at hl
    calc
      fib a + (map fib l).sum < fib a + fib (a - 1) := by gcongr; exact sum_fib_lt hl.2 this
      _ <= fib n := by
        rw [add_comm]; rw [← fib_add_one (hl.1.2.trans_lt' zero_lt_two).ne']; exact fib_mono (hn _ rfl)

end List

namespace Nat
variable {m n : Nat}

/--
Definition of `greatestFib` / `greatestFib` 的定义

English:
definition greatestFib
  signature: (n : Nat)
  body: (n + 1).findGreatest (fun k => fib k <= n)

中文:
定义 greatestFib
  签名: (n : 自然数)
  定义体: (n + 1).findGreatest (fun k => fib k <= n)

Depends on / 依赖: findGreatest
-/
def greatestFib (n : Nat) : Nat := (n + 1).findGreatest (fun k => fib k <= n)

/--
lemma `fib_greatestFib_le` / 引理 `fib_greatestFib_le`

English:
lemma fib_greatestFib_le
  given: (n : Nat)
  statement: fib (greatestFib n) <= n
  proof: findGreatest_spec (P := (fun k => fib k <= n)) (zero_le _) zero_le _

中文:
引理 fib_greatestFib_le
  条件: (n : 自然数)
  结论: fib (greatestFib n) <= n
  证明: findGreatest_spec (P := (fun k => fib k <= n)) (zero_le _) zero_le _

Depends on / 依赖: findGreatest_spec, zero_le
-/
lemma fib_greatestFib_le (n : Nat) : fib (greatestFib n) <= n :=
findGreatest_spec (P := (fun k => fib k <= n)) (zero_le _) zero_le _

/--
lemma `greatestFib_mono` / 引理 `greatestFib_mono`

English:
lemma greatestFib_mono
  statement: Monotone greatestFib
  proof: fun _a _b hab => findGreatest_mono (fun _k => hab.trans') by gcongr

中文:
引理 greatestFib_mono
  结论: 递增 greatestFib
  证明: fun _a _b hab => findGreatest_mono (fun _k => hab.trans') by gcongr

Depends on / 依赖: findGreatest_mono, hab.trans
-/
lemma greatestFib_mono : Monotone greatestFib :=
fun _a _b hab => findGreatest_mono (fun _k => hab.trans') by gcongr

/--
lemma `le_greatestFib` / 引理 `le_greatestFib`

English:
lemma le_greatestFib
  statement: m <= greatestFib n ↔ fib m <= n
  proof: ⟨fun h => (fib_mono h).trans fib_greatestFib_le _,
    fun h => le_findGreatest (m.le_fib_add_one.trans <| by gcongr) h⟩

中文:
引理 le_greatestFib
  结论: m <= greatestFib n ↔ fib m <= n
  证明: ⟨fun h => (fib_mono h).trans fib_greatestFib_le _,
    fun h => le_findGreatest (m.le_fib_add_one.trans <| by gcongr) h⟩
-/
@[simp] lemma le_greatestFib : m <= greatestFib n ↔ fib m <= n :=
⟨fun h => (fib_mono h).trans fib_greatestFib_le _,
    fun h => le_findGreatest (m.le_fib_add_one.trans <| by gcongr) h⟩

/--
lemma `greatestFib_lt` / 引理 `greatestFib_lt`

English:
lemma greatestFib_lt
  statement: greatestFib m < n ↔ m < fib n
  proof: lt_iff_lt_of_le_iff_le le_greatestFib

中文:
引理 greatestFib_lt
  结论: greatestFib m < n ↔ m < fib n
  证明: lt_iff_lt_of_le_iff_le le_greatestFib
-/
@[simp] lemma greatestFib_lt : greatestFib m < n ↔ m < fib n :=
  lt_iff_lt_of_le_iff_le le_greatestFib

/--
lemma `lt_fib_greatestFib_add_one` / 引理 `lt_fib_greatestFib_add_one`

English:
lemma lt_fib_greatestFib_add_one
  given: (n : Nat)
  statement: n < fib (greatestFib n + 1)
  proof: greatestFib_lt.1 lt_succ_self _

中文:
引理 lt_fib_greatestFib_add_one
  条件: (n : 自然数)
  结论: n < fib (greatestFib n + 1)
  证明: greatestFib_lt.1 lt_succ_self _

Depends on / 依赖: greatestFib_lt, lt_succ_self
-/
lemma lt_fib_greatestFib_add_one (n : Nat) : n < fib (greatestFib n + 1) :=
greatestFib_lt.1 lt_succ_self _

/--
lemma `greatestFib_fib` / 引理 `greatestFib_fib`

English:
lemma greatestFib_fib
  statement: forall {n}, n != 1 -> greatestFib (fib n) = n

中文:
引理 greatestFib_fib
  结论: 对任意 {n}, n != 1 -> greatestFib (fib n) = n
-/
@[simp] lemma greatestFib_fib : forall {n}, n != 1 -> greatestFib (fib n) = n
  | 0, _ => rfl
  | _n + 2, _ => findGreatest_eq_iff.2
    ⟨le_fib_add_one _, fun _ => le_rfl, fun _m hnm _ => ((fib_lt_fib le_add_self).2 hnm).not_ge⟩

/--
lemma `greatestFib_eq_zero` / 引理 `greatestFib_eq_zero`

English:
lemma greatestFib_eq_zero
  statement: greatestFib n = 0 ↔ n = 0
  proof: ⟨fun h => by simpa using findGreatest_eq_zero_iff.1 h zero_lt_one le_add_self, by rintro rfl; rfl⟩

中文:
引理 greatestFib_eq_zero
  结论: greatestFib n = 0 ↔ n = 0
  证明: ⟨fun h => by simpa using findGreatest_eq_zero_iff.1 h zero_lt_one le_add_self, by rintro rfl; rfl⟩
-/
@[simp] lemma greatestFib_eq_zero : greatestFib n = 0 ↔ n = 0 :=
  ⟨fun h => by simpa using findGreatest_eq_zero_iff.1 h zero_lt_one le_add_self, by rintro rfl; rfl⟩

/--
lemma `greatestFib_ne_zero` / 引理 `greatestFib_ne_zero`

English:
lemma greatestFib_ne_zero
  statement: greatestFib n != 0 ↔ n != 0
  proof: greatestFib_eq_zero.not

中文:
引理 greatestFib_ne_zero
  结论: greatestFib n != 0 ↔ n != 0
  证明: greatestFib_eq_zero.not

Depends on / 依赖: greatestFib_eq_zero, greatestFib_eq_zero.not
-/
lemma greatestFib_ne_zero : greatestFib n != 0 ↔ n != 0 := greatestFib_eq_zero.not

/--
lemma `greatestFib_pos` / 引理 `greatestFib_pos`

English:
lemma greatestFib_pos
  statement: 0 < greatestFib n ↔ 0 < n
  proof: by simp [pos_iff_ne_zero]

中文:
引理 greatestFib_pos
  结论: 0 < greatestFib n ↔ 0 < n
  证明: by simp [pos_iff_ne_zero]
-/
@[simp] lemma greatestFib_pos : 0 < greatestFib n ↔ 0 < n := by simp [pos_iff_ne_zero]

/--
lemma `greatestFib_sub_fib_greatestFib_le_greatestFib` / 引理 `greatestFib_sub_fib_greatestFib_le_greatestFib`

English:
lemma greatestFib_sub_fib_greatestFib_le_greatestFib
  given: (hn : n != 0)
  proof: by
  rw [← Nat.lt_succ_iff]; rw [greatestFib_lt]; rw [tsub_lt_iff_right n.fib_greatestFib_le]; rw [Nat.sub_succ]; rw [succ_pred]; rw [← fib_add_one]
  · exact n.lt_fib_greatestFib_add_one
  · simpa
  · simpa [← succ_le_iff, tsub_eq_zero_iff_le] using hn.bot_lt

中文:
引理 greatestFib_sub_fib_greatestFib_le_greatestFib
  条件: (hn : n != 0)
  证明: by
  rw [← Nat.lt_succ_iff]; rw [greatestFib_lt]; rw [tsub_lt_iff_right n.fib_greatestFib_le]; rw [Nat.sub_succ]; rw [succ_pred]; rw [← fib_add_one]
  · exact n.lt_fib_greatestFib_add_one
  · simpa
  · simpa [← succ_le_iff, tsub_eq_zero_iff_le] using hn.bot_lt

Depends on / 依赖: Nat.lt_succ_iff, Nat.sub_succ, bot_lt, fib_add_one, fib_greatestFib_le, greatestFib_lt, hn.bot_lt, lt_fib_greatestFib_add_one, lt_succ_iff, n.fib_greatestFib_le, n.lt_fib_greatestFib_add_one, sub_succ, succ_le_iff, succ_pred, tsub_eq_zero_iff_le, tsub_lt_iff_right
-/
lemma greatestFib_sub_fib_greatestFib_le_greatestFib (hn : n != 0) :
    greatestFib (n - fib (greatestFib n)) <= greatestFib n - 2 := by
  rw [← Nat.lt_succ_iff]; rw [greatestFib_lt]; rw [tsub_lt_iff_right n.fib_greatestFib_le]; rw [Nat.sub_succ]; rw [succ_pred]; rw [← fib_add_one]
  · exact n.lt_fib_greatestFib_add_one
  · simpa
  · simpa [← succ_le_iff, tsub_eq_zero_iff_le] using hn.bot_lt

/--
lemma `zeckendorf_aux` / 引理 `zeckendorf_aux`

English:
lemma zeckendorf_aux
  given: (hm : 0 < m)
  statement: m - fib (greatestFib m) < m
  proof: tsub_lt_self hm fib_pos.2 findGreatest_pos.2 ⟨1, zero_lt_one, le_add_self, hm⟩

中文:
引理 zeckendorf_aux
  条件: (hm : 0 < m)
  结论: m - fib (greatestFib m) < m
  证明: tsub_lt_self hm fib_pos.2 findGreatest_pos.2 ⟨1, zero_lt_one, le_add_self, hm⟩
-/
private lemma zeckendorf_aux (hm : 0 < m) : m - fib (greatestFib m) < m :=
tsub_lt_self hm fib_pos.2 findGreatest_pos.2 ⟨1, zero_lt_one, le_add_self, hm⟩

/--
Definition of `zeckendorf` / `zeckendorf` 的定义

English:
definition zeckendorf
  signature: : Nat -> List Nat
  body: greatestFib m
    a :: zeckendorf (m - fib a)

中文:
定义 zeckendorf
  签名: : 自然数 -> 列表 自然数
  定义体: greatestFib m
    a :: zeckendorf (m - fib a)

Depends on / 依赖: greatestFib
-/
def zeckendorf : Nat -> List Nat
  | 0 => []
  | m@(_ + 1) =>
    letI a := greatestFib m
    a :: zeckendorf (m - fib a)

/--
lemma `zeckendorf_zero` / 引理 `zeckendorf_zero`

English:
lemma zeckendorf_zero
  statement: zeckendorf 0 = []
  proof: zeckendorf.eq_1 ..

中文:
引理 zeckendorf_zero
  结论: zeckendorf 0 = []
  证明: zeckendorf.eq_1 ..
-/
@[simp] lemma zeckendorf_zero : zeckendorf 0 = [] := zeckendorf.eq_1 ..

/--
lemma `zeckendorf_succ` / 引理 `zeckendorf_succ`

English:
lemma zeckendorf_succ
  given: (n : Nat)
  proof: zeckendorf.eq_2 ..

中文:
引理 zeckendorf_succ
  条件: (n : 自然数)
  证明: zeckendorf.eq_2 ..
-/
@[simp] lemma zeckendorf_succ (n : Nat) :
    zeckendorf (n + 1) = greatestFib (n + 1) :: zeckendorf (n + 1 - fib (greatestFib (n + 1))) :=
  zeckendorf.eq_2 ..

/--
lemma `zeckendorf_of_pos` / 引理 `zeckendorf_of_pos`

English:
lemma zeckendorf_of_pos
  statement: forall {n}, 0 < n ->

中文:
引理 zeckendorf_of_pos
  结论: 对任意 {n}, 0 < n ->
-/
@[simp] lemma zeckendorf_of_pos : forall {n}, 0 < n ->
    zeckendorf n = greatestFib n :: zeckendorf (n - fib (greatestFib n))
  | _n + 1, _ => zeckendorf_succ _

/--
lemma `isZeckendorfRep_zeckendorf` / 引理 `isZeckendorfRep_zeckendorf`

English:
lemma isZeckendorfRep_zeckendorf
  statement: forall n, (zeckendorf n).IsZeckendorfRep
  proof: eq_zero_or_pos (n + 1 - fib (greatestFib (n + 1)))
    · simp only [h, zeckendorf_zero, nil_append, head?_cons, Option.mem_some_iff] at ha
      subst ha
      exact le_greatestFib.2 le_add_self
    rw [zeckendorf_of_pos h]; rw [cons_append]; rw [head?_cons]; rw [Option.mem_some_iff] at ha
    subst a
    exact add_le_of_le_tsub_right_of_le (le_greatestFib.2 le_add_self)
      (greatestFib_sub_fib_greatestFib_le_greatestFib n.succ_ne_zero)

中文:
引理 isZeckendorfRep_zeckendorf
  结论: 对任意 n, (zeckendorf n).IsZeckendorfRep
  证明: eq_zero_or_pos (n + 1 - fib (greatestFib (n + 1)))
    · simp only [h, zeckendorf_zero, nil_append, head?_cons, Option.mem_some_iff] at ha
      subst ha
      exact le_greatestFib.2 le_add_self
    rw [zeckendorf_of_pos h]; rw [cons_append]; rw [head?_cons]; rw [Option.mem_some_iff] at ha
    subst a
    exact add_le_of_le_tsub_right_of_le (le_greatestFib.2 le_add_self)
      (greatestFib_sub_fib_greatestFib_le_greatestFib n.succ_ne_zero)

Depends on / 依赖: eq_zero_or_pos, greatestFib
-/
lemma isZeckendorfRep_zeckendorf : forall n, (zeckendorf n).IsZeckendorfRep
  | 0 => by simp only [zeckendorf_zero, IsZeckendorfRep_nil]
  | n + 1 => by
    rw [zeckendorf_succ]; rw [IsZeckendorfRep]; rw [List.cons_append]
    refine (isZeckendorfRep_zeckendorf _).cons (fun a ha => ?_)
    obtain h | h := eq_zero_or_pos (n + 1 - fib (greatestFib (n + 1)))
    · simp only [h, zeckendorf_zero, nil_append, head?_cons, Option.mem_some_iff] at ha
      subst ha
      exact le_greatestFib.2 le_add_self
    rw [zeckendorf_of_pos h]; rw [cons_append]; rw [head?_cons]; rw [Option.mem_some_iff] at ha
    subst a
    exact add_le_of_le_tsub_right_of_le (le_greatestFib.2 le_add_self)
      (greatestFib_sub_fib_greatestFib_le_greatestFib n.succ_ne_zero)

/--
lemma `zeckendorf_sum_fib` / 引理 `zeckendorf_sum_fib`

English:
lemma zeckendorf_sum_fib
  statement: forall {l}, IsZeckendorfRep l -> zeckendorf (l.map fib).sum = l
  proof: hl
    simp only [IsZeckendorfRep, cons_append, isChain_iff_pairwise, pairwise_cons, mem_append,
      mem_singleton, or_imp, forall_and, forall_eq, zero_add] at hl
    rw [← isChain_iff_pairwise] at hl
    have ha : 0 < a := hl.1.2.trans_lt' zero_lt_two
    suffices h : greatestFib (fib a + sum (map fib l)) = a by
      simp only [map, List.sum_cons, add_pos_iff, fib_pos.2 ha, true_or, zeckendorf_of_pos, h,
      add_tsub_cancel_left, zeckendorf_sum_fib hl.2]
    simp only [add_comm, add_assoc, greatestFib, findGreatest_eq_iff, ne_eq, ha.ne',
      not_false_eq_true, le_add_iff_nonneg_left, _root_.zero_le, forall_true_left, not_le, true_and]
refine ⟨le_add_of_le_right le_fib_add_one _, fun n hn _ => ?_⟩
    rw [add_comm]; rw [← List.sum_cons]; rw [← map_cons]
    exact hl'.sum_fib_lt (by simpa)

中文:
引理 zeckendorf_sum_fib
  结论: 对任意 {l}, IsZeckendorfRep l -> zeckendorf (l.map fib).求和 = l
  证明: hl
    simp only [IsZeckendorfRep, cons_append, isChain_iff_pairwise, pairwise_cons, mem_append,
      mem_singleton, or_imp, forall_and, forall_eq, zero_add] at hl
    rw [← isChain_iff_pairwise] at hl
    have ha : 0 < a := hl.1.2.trans_lt' zero_lt_two
    suffices h : greatestFib (fib a + sum (map fib l)) = a by
      simp only [map, List.sum_cons, add_pos_iff, fib_pos.2 ha, true_or, zeckendorf_of_pos, h,
      add_tsub_cancel_left, zeckendorf_sum_fib hl.2]
    simp only [add_comm, add_assoc, greatestFib, findGreatest_eq_iff, ne_eq, ha.ne',
      not_false_eq_true, le_add_iff_nonneg_left, _root_.zero_le, forall_true_left, not_le, true_and]
refine ⟨le_add_of_le_right le_fib_add_one _, fun n hn _ => ?_⟩
    rw [add_comm]; rw [← List.sum_cons]; rw [← map_cons]
    exact hl'.sum_fib_lt (by simpa)
-/
lemma zeckendorf_sum_fib : forall {l}, IsZeckendorfRep l -> zeckendorf (l.map fib).sum = l
  | [], _ => by simp only [map_nil, List.sum_nil, zeckendorf_zero]
  | a :: l, hl => by
    have hl' := hl
    simp only [IsZeckendorfRep, cons_append, isChain_iff_pairwise, pairwise_cons, mem_append,
      mem_singleton, or_imp, forall_and, forall_eq, zero_add] at hl
    rw [← isChain_iff_pairwise] at hl
    have ha : 0 < a := hl.1.2.trans_lt' zero_lt_two
    suffices h : greatestFib (fib a + sum (map fib l)) = a by
      simp only [map, List.sum_cons, add_pos_iff, fib_pos.2 ha, true_or, zeckendorf_of_pos, h,
      add_tsub_cancel_left, zeckendorf_sum_fib hl.2]
    simp only [add_comm, add_assoc, greatestFib, findGreatest_eq_iff, ne_eq, ha.ne',
      not_false_eq_true, le_add_iff_nonneg_left, _root_.zero_le, forall_true_left, not_le, true_and]
refine ⟨le_add_of_le_right le_fib_add_one _, fun n hn _ => ?_⟩
    rw [add_comm]; rw [← List.sum_cons]; rw [← map_cons]
    exact hl'.sum_fib_lt (by simpa)

/--
lemma `sum_zeckendorf_fib` / 引理 `sum_zeckendorf_fib`

English:
lemma sum_zeckendorf_fib
  given: (n : Nat)
  statement: (n.zeckendorf.map fib).sum = n
  proof: by
  induction n using zeckendorf.induct <;> simp_all [fib_greatestFib_le]

中文:
引理 sum_zeckendorf_fib
  条件: (n : 自然数)
  结论: (n.zeckendorf.map fib).求和 = n
  证明: by
  induction n using zeckendorf.induct <;> simp_all [fib_greatestFib_le]
-/
@[simp] lemma sum_zeckendorf_fib (n : Nat) : (n.zeckendorf.map fib).sum = n := by
  induction n using zeckendorf.induct <;> simp_all [fib_greatestFib_le]

/--
Definition of `zeckendorfEquiv` / `zeckendorfEquiv` 的定义

English:
definition zeckendorfEquiv
  signature: : Nat ≃ {l // IsZeckendorfRep l} where
  body: ⟨zeckendorf n, isZeckendorfRep_zeckendorf _⟩
  invFun l := (map fib l).sum
  left_inv := sum_zeckendorf_fib
right_inv l := Subtype.ext zeckendorf_sum_fib l.2

中文:
定义 zeckendorfEquiv
  签名: : 自然数 ≃ {l // IsZeckendorfRep l} where
  定义体: ⟨zeckendorf n, isZeckendorfRep_zeckendorf _⟩
  invFun l := (map fib l).sum
  left_inv := sum_zeckendorf_fib
right_inv l := Subtype.ext zeckendorf_sum_fib l.2

Depends on / 依赖: isZeckendorfRep_zeckendorf, zeckendorf
-/
def zeckendorfEquiv : Nat ≃ {l // IsZeckendorfRep l} where
  toFun n := ⟨zeckendorf n, isZeckendorfRep_zeckendorf _⟩
  invFun l := (map fib l).sum
  left_inv := sum_zeckendorf_fib
right_inv l := Subtype.ext zeckendorf_sum_fib l.2

end Nat
