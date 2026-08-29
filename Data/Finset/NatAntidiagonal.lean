/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Multiset.NatAntidiagonal

/-!
# Antidiagonals in ℕ × ℕ as finsets

This file defines the antidiagonals of ℕ × ℕ as finsets: the `n`-th antidiagonal is the finset of
pairs `(i, j)` such that `i + j = n`. This is useful for polynomial multiplication and more
generally for sums going from `0` to `n`.

## Notes

This refines files `Data.List.NatAntidiagonal` and `Data.Multiset.NatAntidiagonal`, providing an
instance enabling `Finset.antidiagonal` on `Nat`.
-/

@[expose] public section

assert_not_exists Field

open Function

namespace Finset

open Finset.HasAntidiagonal

namespace Nat

/--
Instance `instHasAntidiagonal` / 实例 `instHasAntidiagonal`

English:
instance instHasAntidiagonal
  signature: : HasAntidiagonal Nat where
  body: ⟨Multiset.Nat.antidiagonal n, Multiset.Nat.nodup_antidiagonal n⟩
  mem_antidiagonal {n} {xy} := by
    rw [mem_def]; rw [Multiset.Nat.mem_antidiagonal]

中文:
实例 instHasAntidiagonal
  签名: : 有Antidiagonal 自然数 where
  定义体: ⟨Multiset.Nat.antidiagonal n, Multiset.Nat.nodup_antidiagonal n⟩
  mem_antidiagonal {n} {xy} := by
    rw [mem_def]; rw [Multiset.Nat.mem_antidiagonal]

Depends on / 依赖: Multiset, Multiset.Nat.antidiagonal, Multiset.Nat.nodup_antidiagonal, antidiagonal, nodup_antidiagonal
-/
instance instHasAntidiagonal : HasAntidiagonal Nat where
  antidiagonal n := ⟨Multiset.Nat.antidiagonal n, Multiset.Nat.nodup_antidiagonal n⟩
  mem_antidiagonal {n} {xy} := by
    rw [mem_def]; rw [Multiset.Nat.mem_antidiagonal]

/--
lemma `antidiagonal_eq_map` / 引理 `antidiagonal_eq_map`

English:
lemma antidiagonal_eq_map
  given: (n : Nat)
  proof: rfl

中文:
引理 antidiagonal_eq_map
  条件: (n : 自然数)
  证明: rfl
-/
lemma antidiagonal_eq_map (n : Nat) :
    antidiagonal n = (range (n + 1)).map ⟨fun i => (i, n - i), fun _ _ h => (Prod.ext_iff.1 h).1⟩ :=
  rfl

/--
lemma `antidiagonal_eq_map'` / 引理 `antidiagonal_eq_map'`

English:
lemma antidiagonal_eq_map'
  given: (n : Nat)
  proof: by
  rw [← map_swap_antidiagonal]; rw [antidiagonal_eq_map]; rw [map_map]; rfl

中文:
引理 antidiagonal_eq_map'
  条件: (n : 自然数)
  证明: by
  rw [← map_swap_antidiagonal]; rw [antidiagonal_eq_map]; rw [map_map]; rfl

Depends on / 依赖: antidiagonal_eq_map, map_map, map_swap_antidiagonal
-/
lemma antidiagonal_eq_map' (n : Nat) :
    antidiagonal n =
      (range (n + 1)).map ⟨fun i => (n - i, i), fun _ _ h => (Prod.ext_iff.1 h).2⟩ := by
  rw [← map_swap_antidiagonal]; rw [antidiagonal_eq_map]; rw [map_map]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `antidiagonal_eq_image` / 引理 `antidiagonal_eq_image`

English:
lemma antidiagonal_eq_image
  given: (n : Nat)
  proof: by
  simp only [antidiagonal_eq_map, map_eq_image, Function.Embedding.coeFn_mk]

中文:
引理 antidiagonal_eq_image
  条件: (n : 自然数)
  证明: by
  simp only [antidiagonal_eq_map, map_eq_image, Function.Embedding.coeFn_mk]

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, antidiagonal_eq_map, coeFn_mk, map_eq_image
-/
lemma antidiagonal_eq_image (n : Nat) :
    antidiagonal n = (range (n + 1)).image fun i => (i, n - i) := by
  simp only [antidiagonal_eq_map, map_eq_image, Function.Embedding.coeFn_mk]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `antidiagonal_eq_image'` / 引理 `antidiagonal_eq_image'`

English:
lemma antidiagonal_eq_image'
  given: (n : Nat)
  proof: by
  simp only [antidiagonal_eq_map', map_eq_image, Function.Embedding.coeFn_mk]

中文:
引理 antidiagonal_eq_image'
  条件: (n : 自然数)
  证明: by
  simp only [antidiagonal_eq_map', map_eq_image, Function.Embedding.coeFn_mk]

Depends on / 依赖: Embedding, Function, Function.Embedding.coeFn_mk, antidiagonal_eq_map, coeFn_mk, map_eq_image
-/
lemma antidiagonal_eq_image' (n : Nat) :
    antidiagonal n = (range (n + 1)).image fun i => (n - i, i) := by
  simp only [antidiagonal_eq_map', map_eq_image, Function.Embedding.coeFn_mk]

/-- The cardinality of the antidiagonal of `n` is `n + 1`. -/
@[simp]
/--
theorem `card_antidiagonal` / 定理 `card_antidiagonal`

English:
theorem card_antidiagonal
  given: (n : Nat)
  statement: (antidiagonal n).card = n + 1
  proof: by simp [antidiagonal]

中文:
定理 card_antidiagonal
  条件: (n : 自然数)
  结论: (antidiagonal n).card = n + 1
  证明: by simp [antidiagonal]

Depends on / 依赖: antidiagonal
-/
theorem card_antidiagonal (n : Nat) : (antidiagonal n).card = n + 1 := by simp [antidiagonal]

/-- The antidiagonal of `0` is the list `[(0, 0)]` -/
@[simp]
/--
theorem `antidiagonal_zero` / 定理 `antidiagonal_zero`

English:
theorem antidiagonal_zero
  statement: antidiagonal 0 = {(0, 0)}
  proof: rfl

中文:
定理 antidiagonal_zero
  结论: antidiagonal 0 = {(0, 0)}
  证明: rfl
-/
theorem antidiagonal_zero : antidiagonal 0 = {(0, 0)} := rfl

/--
theorem `antidiagonal_succ` / 定理 `antidiagonal_succ`

English:
theorem antidiagonal_succ
  given: (n : Nat)
  proof: by
  apply eq_of_veq
  rw [cons_val]; rw [map_val]
  apply Multiset.Nat.antidiagonal_succ

中文:
定理 antidiagonal_succ
  条件: (n : 自然数)
  证明: by
  apply eq_of_veq
  rw [cons_val]; rw [map_val]
  apply Multiset.Nat.antidiagonal_succ

Depends on / 依赖: Multiset, Multiset.Nat.antidiagonal_succ, antidiagonal_succ, cons_val, eq_of_veq, map_val
-/
theorem antidiagonal_succ (n : Nat) :
    antidiagonal (n + 1) =
      cons (0, n + 1)
        ((antidiagonal n).map
          (Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩ (Embedding.refl _)))
        (by simp) := by
  apply eq_of_veq
  rw [cons_val]; rw [map_val]
  apply Multiset.Nat.antidiagonal_succ

/--
theorem `antidiagonal_succ'` / 定理 `antidiagonal_succ'`

English:
theorem antidiagonal_succ'
  given: (n : Nat)
  proof: by
  apply eq_of_veq
  rw [cons_val]; rw [map_val]
  exact Multiset.Nat.antidiagonal_succ'

中文:
定理 antidiagonal_succ'
  条件: (n : 自然数)
  证明: by
  apply eq_of_veq
  rw [cons_val]; rw [map_val]
  exact Multiset.Nat.antidiagonal_succ'

Depends on / 依赖: Multiset, Multiset.Nat.antidiagonal_succ, antidiagonal_succ, cons_val, eq_of_veq, map_val
-/
theorem antidiagonal_succ' (n : Nat) :
    antidiagonal (n + 1) =
      cons (n + 1, 0)
        ((antidiagonal n).map
          (Embedding.prodMap (Embedding.refl _) ⟨Nat.succ, Nat.succ_injective⟩))
        (by simp) := by
  apply eq_of_veq
  rw [cons_val]; rw [map_val]
  exact Multiset.Nat.antidiagonal_succ'

/--
theorem `antidiagonal_succ_succ'` / 定理 `antidiagonal_succ_succ'`

English:
theorem antidiagonal_succ_succ'
  given: {n : Nat}
  proof: by
  simp_rw [antidiagonal_succ (n + 1), antidiagonal_succ', Finset.map_cons, map_map]
  rfl

中文:
定理 antidiagonal_succ_succ'
  条件: {n : 自然数}
  证明: by
  simp_rw [antidiagonal_succ (n + 1), antidiagonal_succ', Finset.map_cons, map_map]
  rfl

Depends on / 依赖: Finset, Finset.map_cons, antidiagonal_succ, map_cons, map_map, simp_rw
-/
theorem antidiagonal_succ_succ' {n : Nat} :
    antidiagonal (n + 2) =
      cons (0, n + 2)
        (cons (n + 2, 0)
            ((antidiagonal n).map
              (Embedding.prodMap ⟨Nat.succ, Nat.succ_injective⟩
                ⟨Nat.succ, Nat.succ_injective⟩)) <|
          by simp)
        (by simp) := by
  simp_rw [antidiagonal_succ (n + 1), antidiagonal_succ', Finset.map_cons, map_map]
  rfl

/--
theorem `antidiagonal.fst_lt` / 定理 `antidiagonal.fst_lt`

English:
theorem antidiagonal.fst_lt
  given: {n : Nat} {kl : Nat × Nat} (hlk : kl in antidiagonal n)
  statement: kl.1 < n + 1
  proof: Nat.lt_succ_of_le antidiagonal.fst_le hlk

中文:
定理 antidiagonal.fst_lt
  条件: {n : 自然数} {kl : 自然数 × 自然数} (hlk : kl in antidiagonal n)
  结论: kl.1 < n + 1
  证明: Nat.lt_succ_of_le antidiagonal.fst_le hlk

Depends on / 依赖: Nat.lt_succ_of_le, antidiagonal, antidiagonal.fst_le, fst_le, lt_succ_of_le
-/
theorem antidiagonal.fst_lt {n : Nat} {kl : Nat × Nat} (hlk : kl in antidiagonal n) : kl.1 < n + 1 :=
Nat.lt_succ_of_le antidiagonal.fst_le hlk

/--
theorem `antidiagonal.snd_lt` / 定理 `antidiagonal.snd_lt`

English:
theorem antidiagonal.snd_lt
  given: {n : Nat} {kl : Nat × Nat} (hlk : kl in antidiagonal n)
  statement: kl.2 < n + 1
  proof: Nat.lt_succ_of_le antidiagonal.snd_le hlk

中文:
定理 antidiagonal.snd_lt
  条件: {n : 自然数} {kl : 自然数 × 自然数} (hlk : kl in antidiagonal n)
  结论: kl.2 < n + 1
  证明: Nat.lt_succ_of_le antidiagonal.snd_le hlk

Depends on / 依赖: Nat.lt_succ_of_le, antidiagonal, antidiagonal.snd_le, lt_succ_of_le, snd_le
-/
theorem antidiagonal.snd_lt {n : Nat} {kl : Nat × Nat} (hlk : kl in antidiagonal n) : kl.2 < n + 1 :=
Nat.lt_succ_of_le antidiagonal.snd_le hlk

/--
lemma `antidiagonal_filter_snd_le_of_le` / 引理 `antidiagonal_filter_snd_le_of_le`

English:
lemma antidiagonal_filter_snd_le_of_le
  given: {n k : Nat} (h : k <= n)
  proof: by
  ext ⟨i, j⟩
  suffices i + j = n ∧ j <= k ↔ exists a, a + j = k ∧ a + (n - k) = i by simpa
  refine ⟨fun hi => ⟨k - j, tsub_add_cancel_of_le hi.2, ?_⟩, ?_⟩
  · rw [add_comm, tsub_add_eq_add_tsub h, ← hi.1, add_assoc, Nat.add_sub_of_le hi.2,
      add_tsub_cancel_right]
  · rintro ⟨l, hl, rfl⟩
  

中文:
引理 antidiagonal_filter_snd_le_of_le
  条件: {n k : 自然数} (h : k <= n)
  证明: by
  ext ⟨i, j⟩
  suffices i + j = n ∧ j <= k ↔ exists a, a + j = k ∧ a + (n - k) = i by simpa
  refine ⟨fun hi => ⟨k - j, tsub_add_cancel_of_le hi.2, ?_⟩, ?_⟩
  · rw [add_comm, tsub_add_eq_add_tsub h, ← hi.1, add_assoc, Nat.add_sub_of_le hi.2,
      add_tsub_cancel_right]
  · rintro ⟨l, hl, rfl⟩
  
-/
@[simp] lemma antidiagonal_filter_snd_le_of_le {n k : Nat} (h : k <= n) :
    {a in antidiagonal n | a.snd <= k} = (antidiagonal k).map
      (Embedding.prodMap ⟨_, add_left_injective (n - k)⟩ (Embedding.refl Nat)) := by
  ext ⟨i, j⟩
  suffices i + j = n ∧ j <= k ↔ exists a, a + j = k ∧ a + (n - k) = i by simpa
  refine ⟨fun hi => ⟨k - j, tsub_add_cancel_of_le hi.2, ?_⟩, ?_⟩
  · rw [add_comm, tsub_add_eq_add_tsub h, ← hi.1, add_assoc, Nat.add_sub_of_le hi.2,
      add_tsub_cancel_right]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨?_, hl ▸ Nat.le_add_left j l⟩
    rw [add_assoc]; rw [add_comm]; rw [add_assoc]; rw [add_comm j l]; rw [hl]
    exact Nat.sub_add_cancel h

/--
lemma `antidiagonal_filter_fst_le_of_le` / 引理 `antidiagonal_filter_fst_le_of_le`

English:
lemma antidiagonal_filter_fst_le_of_le
  given: {n k : Nat} (h : k <= n)
  proof: by
  have aux₁ : fun a => a.fst <= k = (fun a => a.snd <= k) ∘ (Equiv.prodComm Nat Nat).symm := rfl
  have aux₂ : forall i j, (exists a b, a + b = k ∧ b = i ∧ a + (n - k) = j) ↔
                      exists a b, a + b = k ∧ a = i ∧ b + (n - k) = j :=
    fun i j => by rw [exists_comm]; exact exists₂

中文:
引理 antidiagonal_filter_fst_le_of_le
  条件: {n k : 自然数} (h : k <= n)
  证明: by
  have aux₁ : fun a => a.fst <= k = (fun a => a.snd <= k) ∘ (Equiv.prodComm Nat Nat).symm := rfl
  have aux₂ : forall i j, (exists a b, a + b = k ∧ b = i ∧ a + (n - k) = j) ↔
                      exists a b, a + b = k ∧ a = i ∧ b + (n - k) = j :=
    fun i j => by rw [exists_comm]; exact exists₂
-/
@[simp] lemma antidiagonal_filter_fst_le_of_le {n k : Nat} (h : k <= n) :
    {a in antidiagonal n | a.fst <= k} = (antidiagonal k).map
      (Embedding.prodMap (Embedding.refl Nat) ⟨_, add_left_injective (n - k)⟩) := by
  have aux₁ : fun a => a.fst <= k = (fun a => a.snd <= k) ∘ (Equiv.prodComm Nat Nat).symm := rfl
  have aux₂ : forall i j, (exists a b, a + b = k ∧ b = i ∧ a + (n - k) = j) ↔
                      exists a b, a + b = k ∧ a = i ∧ b + (n - k) = j :=
    fun i j => by rw [exists_comm]; exact exists₂_congr (fun a b => by rw [add_comm])
  rw [← map_prodComm_antidiagonal]
  simp_rw [aux₁, ← map_filter, antidiagonal_filter_snd_le_of_le h, map_map]
  ext ⟨i, j⟩
  simpa using aux₂ i j

/--
lemma `antidiagonal_filter_le_fst_of_le` / 引理 `antidiagonal_filter_le_fst_of_le`

English:
lemma antidiagonal_filter_le_fst_of_le
  given: {n k : Nat} (h : k <= n)
  proof: by
  ext ⟨i, j⟩
  suffices i + j = n ∧ k <= i ↔ exists a, a + j = n - k ∧ a + k = i by simpa
  refine ⟨fun hi => ⟨i - k, ?_, tsub_add_cancel_of_le hi.2⟩, ?_⟩
  · rw [← Nat.sub_add_comm hi.2, hi.1]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨?_, Nat.le_add_left k l⟩
    rw [add_right_comm]; rw [hl]
    exact

中文:
引理 antidiagonal_filter_le_fst_of_le
  条件: {n k : 自然数} (h : k <= n)
  证明: by
  ext ⟨i, j⟩
  suffices i + j = n ∧ k <= i ↔ exists a, a + j = n - k ∧ a + k = i by simpa
  refine ⟨fun hi => ⟨i - k, ?_, tsub_add_cancel_of_le hi.2⟩, ?_⟩
  · rw [← Nat.sub_add_comm hi.2, hi.1]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨?_, Nat.le_add_left k l⟩
    rw [add_right_comm]; rw [hl]
    exact
-/
@[simp] lemma antidiagonal_filter_le_fst_of_le {n k : Nat} (h : k <= n) :
    {a in antidiagonal n | k <= a.fst} = (antidiagonal (n - k)).map
      (Embedding.prodMap ⟨_, add_left_injective k⟩ (Embedding.refl Nat)) := by
  ext ⟨i, j⟩
  suffices i + j = n ∧ k <= i ↔ exists a, a + j = n - k ∧ a + k = i by simpa
  refine ⟨fun hi => ⟨i - k, ?_, tsub_add_cancel_of_le hi.2⟩, ?_⟩
  · rw [← Nat.sub_add_comm hi.2, hi.1]
  · rintro ⟨l, hl, rfl⟩
    refine ⟨?_, Nat.le_add_left k l⟩
    rw [add_right_comm]; rw [hl]
    exact tsub_add_cancel_of_le h

/--
lemma `antidiagonal_filter_le_snd_of_le` / 引理 `antidiagonal_filter_le_snd_of_le`

English:
lemma antidiagonal_filter_le_snd_of_le
  given: {n k : Nat} (h : k <= n)
  proof: by
  have aux₁ : fun a => k <= a.snd = (fun a => k <= a.fst) ∘ (Equiv.prodComm Nat Nat).symm := rfl
  have aux₂ : forall i j, (exists a b, a + b = n - k ∧ b = i ∧ a + k = j) ↔
                      exists a b, a + b = n - k ∧ a = i ∧ b + k = j :=
    fun i j => by rw [exists_comm]; exact exists₂_con

中文:
引理 antidiagonal_filter_le_snd_of_le
  条件: {n k : 自然数} (h : k <= n)
  证明: by
  have aux₁ : fun a => k <= a.snd = (fun a => k <= a.fst) ∘ (Equiv.prodComm Nat Nat).symm := rfl
  have aux₂ : forall i j, (exists a b, a + b = n - k ∧ b = i ∧ a + k = j) ↔
                      exists a b, a + b = n - k ∧ a = i ∧ b + k = j :=
    fun i j => by rw [exists_comm]; exact exists₂_con
-/
@[simp] lemma antidiagonal_filter_le_snd_of_le {n k : Nat} (h : k <= n) :
    {a in antidiagonal n | k <= a.snd} = (antidiagonal (n - k)).map
      (Embedding.prodMap (Embedding.refl Nat) ⟨_, add_left_injective k⟩) := by
  have aux₁ : fun a => k <= a.snd = (fun a => k <= a.fst) ∘ (Equiv.prodComm Nat Nat).symm := rfl
  have aux₂ : forall i j, (exists a b, a + b = n - k ∧ b = i ∧ a + k = j) ↔
                      exists a b, a + b = n - k ∧ a = i ∧ b + k = j :=
    fun i j => by rw [exists_comm]; exact exists₂_congr (fun a b => by rw [add_comm])
  rw [← map_prodComm_antidiagonal]
  simp_rw [aux₁, ← map_filter, antidiagonal_filter_le_fst_of_le h,
    map_map]
  ext ⟨i, j⟩
  simpa using aux₂ i j

/-- The set `antidiagonal n` is equivalent to `Fin (n+1)`, via the first projection. -/
@[simps]
/--
Definition of `antidiagonalEquivFin` / `antidiagonalEquivFin` 的定义

English:
definition antidiagonalEquivFin
  signature: (n : Nat)
  body: fun ⟨⟨i, _⟩, h⟩ => ⟨i, antidiagonal.fst_lt h⟩
  invFun := fun ⟨i, h⟩ => ⟨⟨i, n - i⟩, by
    rw [mem_antidiagonal]; rw [add_comm]; rw [Nat.sub_add_cancel]
    exact Nat.le_of_lt_succ h⟩

中文:
定义 antidiagonalEquivFin
  签名: (n : 自然数)
  定义体: fun ⟨⟨i, _⟩, h⟩ => ⟨i, antidiagonal.fst_lt h⟩
  invFun := fun ⟨i, h⟩ => ⟨⟨i, n - i⟩, by
    rw [mem_antidiagonal]; rw [add_comm]; rw [Nat.sub_add_cancel]
    exact Nat.le_of_lt_succ h⟩

Depends on / 依赖: antidiagonal, antidiagonal.fst_lt, fst_lt
-/
def antidiagonalEquivFin (n : Nat) : antidiagonal n ≃ Fin (n + 1) where
  toFun := fun ⟨⟨i, _⟩, h⟩ => ⟨i, antidiagonal.fst_lt h⟩
  invFun := fun ⟨i, h⟩ => ⟨⟨i, n - i⟩, by
    rw [mem_antidiagonal]; rw [add_comm]; rw [Nat.sub_add_cancel]
    exact Nat.le_of_lt_succ h⟩

end Nat

end Finset
