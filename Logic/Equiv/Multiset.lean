/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Sort
public import Mathlib.Logic.Equiv.List

/-!
# `Encodable` and `Denumerable` instances for `Multiset`
-/

@[expose] public section

variable {α : Type*}

open Encodable

section Finset

variable [Encodable α]

set_option backward.privateInPublic true in
/--
Definition of `enle` / `enle` 的定义

English:
definition enle
  signature: : α -> α -> Prop
  body: encode ⁻¹'o (· <= ·)
deriving DecidableRel

中文:
定义 enle
  签名: : α -> α -> 命题
  定义体: encode ⁻¹'o (· <= ·)
deriving DecidableRel
-/
private def enle : α -> α -> Prop :=
  encode ⁻¹'o (· <= ·)
deriving DecidableRel

set_option backward.privateInPublic true in
private local instance enle.isLinearOrder : IsLinearOrder α enle :=
  (RelEmbedding.preimage ⟨encode, encode_injective⟩ (· <= ·)).isLinearOrder

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `encodeMultiset` / `encodeMultiset` 的定义

English:
definition encodeMultiset
  signature: (s : Multiset α)
  body: encode (s.sort enle)

中文:
定义 encodeMultiset
  签名: (s : Multiset α)
  定义体: encode (s.sort enle)

Depends on / 依赖: encode, s.sort
-/
def encodeMultiset (s : Multiset α) : Nat :=
  encode (s.sort enle)

/--
Definition of `decodeMultiset` / `decodeMultiset` 的定义

English:
definition decodeMultiset
  signature: (n : Nat)
  body: ((↑) : List α -> Multiset α) < > decode (α := List α) n

中文:
定义 decodeMultiset
  签名: (n : 自然数)
  定义体: ((↑) : List α -> Multiset α) < > decode (α := List α) n

Depends on / 依赖: Multiset, decode
-/
def decodeMultiset (n : Nat) : Option (Multiset α) :=
((↑) : List α -> Multiset α) < > decode (α := List α) n

/--
Instance `_root_.Multiset.encodable` / 实例 `_root_.Multiset.encodable`

English:
instance _root_.Multiset.encodable
  signature: : Encodable (Multiset α)
  body: ⟨encodeMultiset, decodeMultiset, fun s => by simp [encodeMultiset, decodeMultiset, encodek]⟩

中文:
实例 _root_.Multiset.encodable
  签名: : 可编码 (Multiset α)
  定义体: ⟨encodeMultiset, decodeMultiset, fun s => by simp [encodeMultiset, decodeMultiset, encodek]⟩

Depends on / 依赖: decodeMultiset, encodeMultiset, encodek
-/
instance _root_.Multiset.encodable : Encodable (Multiset α) :=
  ⟨encodeMultiset, decodeMultiset, fun s => by simp [encodeMultiset, decodeMultiset, encodek]⟩

end Finset

namespace Denumerable
variable [Denumerable α]

section Multiset

/--
Definition of `lower` / `lower` 的定义

English:
definition lower
  signature: : List Nat -> Nat -> List Nat

中文:
定义 lower
  签名: : 列表 自然数 -> 自然数 -> 列表 自然数
-/
def lower : List Nat -> Nat -> List Nat
  | [], _ => []
  | m :: l, n => (m - n) :: lower l m

/--
Definition of `raise` / `raise` 的定义

English:
definition raise
  signature: : List Nat -> Nat -> List Nat

中文:
定义 raise
  签名: : 列表 自然数 -> 自然数 -> 列表 自然数
-/
def raise : List Nat -> Nat -> List Nat
  | [], _ => []
  | m :: l, n => (m + n) :: raise l (m + n)

/--
theorem `lower_raise` / 定理 `lower_raise`

English:
theorem lower_raise
  statement: forall l n, lower (raise l n) n = l

中文:
定理 lower_raise
  结论: 对任意 l n, lower (raise l n) n = l
-/
theorem lower_raise : forall l n, lower (raise l n) n = l
  | [], _ => rfl
  | m :: l, n => by rw [raise, lower, Nat.add_sub_cancel_right, lower_raise l]

/--
theorem `raise_lower` / 定理 `raise_lower`

English:
theorem raise_lower
  statement: forall {l n}, List.SortedLE (n :: l) -> raise (lower l n) n = l
  proof: List.rel_of_pairwise_cons h.pairwise List.mem_cons_self
    simp [raise, lower, Nat.sub_add_cancel this, raise_lower h.pairwise.of_cons.sortedLE]

中文:
定理 raise_lower
  结论: 对任意 {l n}, 列表.SortedLE (n :: l) -> raise (lower l n) n = l
  证明: List.rel_of_pairwise_cons h.pairwise List.mem_cons_self
    simp [raise, lower, Nat.sub_add_cancel this, raise_lower h.pairwise.of_cons.sortedLE]

Depends on / 依赖: List.mem_cons_self, List.rel_of_pairwise_cons, h.pairwise, mem_cons_self, pairwise, rel_of_pairwise_cons
-/
theorem raise_lower : forall {l n}, List.SortedLE (n :: l) -> raise (lower l n) n = l
  | [], _, _ => rfl
  | m :: l, n, h => by
    have : n <= m := List.rel_of_pairwise_cons h.pairwise List.mem_cons_self
    simp [raise, lower, Nat.sub_add_cancel this, raise_lower h.pairwise.of_cons.sortedLE]

/--
theorem `isChain_raise` / 定理 `isChain_raise`

English:
theorem isChain_raise
  statement: forall l n, List.IsChain (· <= ·) (raise l n)

中文:
定理 isChain_raise
  结论: 对任意 l n, 列表.IsChain (· <= ·) (raise l n)
-/
theorem isChain_raise : forall l n, List.IsChain (· <= ·) (raise l n)
  | [], _ => .nil
  | [_], _ => .singleton _
  | _ :: _ :: _, _ => .cons_cons (Nat.le_add_left _ _) (isChain_raise (_ :: _) _)

/--
theorem `isChain_cons_raise` / 定理 `isChain_cons_raise`

English:
theorem isChain_cons_raise
  given: (l n)
  statement: List.IsChain (· <= ·) (n :: raise l n)
  proof: isChain_raise (n :: l) 0

中文:
定理 isChain_cons_raise
  条件: (l n)
  结论: 列表.IsChain (· <= ·) (n :: raise l n)
  证明: isChain_raise (n :: l) 0

Depends on / 依赖: isChain_raise
-/
theorem isChain_cons_raise (l n) : List.IsChain (· <= ·) (n :: raise l n) :=
  isChain_raise (n :: l) 0

/--
theorem `raise_sorted` / 定理 `raise_sorted`

English:
theorem raise_sorted
  given: (l n)
  statement: List.SortedLE (raise l n)
  proof: (isChain_raise _ _).sortedLE

中文:
定理 raise_sorted
  条件: (l n)
  结论: 列表.SortedLE (raise l n)
  证明: (isChain_raise _ _).sortedLE

Depends on / 依赖: isChain_raise, sortedLE
-/
theorem raise_sorted (l n) : List.SortedLE (raise l n) := (isChain_raise _ _).sortedLE

/--
Instance `multiset` / 实例 `multiset`

English:
instance multiset
  signature: : Denumerable (Multiset α)
  body: mk'
⟨fun s : Multiset α => encode lower (s.map encode).sort 0,
     fun n =>
      Multiset.map (ofNat α) (raise (ofNat (List Nat) n) 0),
     fun s => by
      have :=
        raise_lower (List.pairwise_cons.2 ⟨fun n _ => Nat.zero_le n,
        (s.map encode).pairwise_sort _⟩).sortedLE
      simp [-Multiset.map_coe, this],
     fun n => by
      simp [-Multiset.map_coe, List.mergeSort_eq_self _ (raise_sorted _ _).pairwise, lower_raise]⟩

中文:
实例 multiset
  签名: : 可枚举 (Multiset α)
  定义体: mk'
⟨fun s : Multiset α => encode lower (s.map encode).sort 0,
     fun n =>
      Multiset.map (ofNat α) (raise (ofNat (List Nat) n) 0),
     fun s => by
      have :=
        raise_lower (List.pairwise_cons.2 ⟨fun n _ => Nat.zero_le n,
        (s.map encode).pairwise_sort _⟩).sortedLE
      simp [-Multiset.map_coe, this],
     fun n => by
      simp [-Multiset.map_coe, List.mergeSort_eq_self _ (raise_sorted _ _).pairwise, lower_raise]⟩

Depends on / 依赖: List.mergeSort_eq_self, List.pairwise_cons, Multiset, Multiset.map, Multiset.map_coe, Nat.zero_le, encode, lower_raise, map_coe, mergeSort_eq_self, pairwise, pairwise_cons, pairwise_sort, raise_lower, raise_sorted, s.map, sortedLE, zero_le
-/
instance multiset : Denumerable (Multiset α) :=
  mk'
⟨fun s : Multiset α => encode lower (s.map encode).sort 0,
     fun n =>
      Multiset.map (ofNat α) (raise (ofNat (List Nat) n) 0),
     fun s => by
      have :=
        raise_lower (List.pairwise_cons.2 ⟨fun n _ => Nat.zero_le n,
        (s.map encode).pairwise_sort _⟩).sortedLE
      simp [-Multiset.map_coe, this],
     fun n => by
      simp [-Multiset.map_coe, List.mergeSort_eq_self _ (raise_sorted _ _).pairwise, lower_raise]⟩

end Multiset

end Denumerable
