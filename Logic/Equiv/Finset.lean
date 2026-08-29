/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Multiset

/-!
# `Encodable` and `Denumerable` instances for `Finset`
-/

@[expose] public section

variable {α}

open Encodable

/--
Instance `Finset.encodable` / 实例 `Finset.encodable`

English:
instance Finset.encodable
  signature: [Encodable α]
  body: haveI := decidableEqOfEncodable α
  ofEquiv { s : Multiset α // s.Nodup }
    { toFun := fun ⟨a, b⟩ => ⟨a, b⟩
      invFun := fun ⟨a, b⟩ => ⟨a, b⟩ }

中文:
实例 Finset.encodable
  签名: [Encodable α]
  定义体: haveI := decidableEqOfEncodable α
  ofEquiv { s : Multiset α // s.Nodup }
    { toFun := fun ⟨a, b⟩ => ⟨a, b⟩
      invFun := fun ⟨a, b⟩ => ⟨a, b⟩ }

Depends on / 依赖: Multiset, decidableEqOfEncodable, invFun, ofEquiv, s.Nodup
-/
instance Finset.encodable [Encodable α] : Encodable (Finset α) :=
  haveI := decidableEqOfEncodable α
  ofEquiv { s : Multiset α // s.Nodup }
    { toFun := fun ⟨a, b⟩ => ⟨a, b⟩
      invFun := fun ⟨a, b⟩ => ⟨a, b⟩ }

namespace Encodable

/--
Definition of `sortedUniv` / `sortedUniv` 的定义

English:
definition sortedUniv
  signature: (α) [Fintype α] [Encodable α]
  body: Finset.univ.sort (Encodable.encode' α ⁻¹'o (· <= ·))

@[simp]

中文:
定义 sortedUniv
  签名: (α) [Fintype α] [Encodable α]
  定义体: Finset.univ.sort (Encodable.encode' α ⁻¹'o (· <= ·))

@[simp]

Depends on / 依赖: Encodable, Encodable.encode, Finset, Finset.univ.sort, encode
-/
def sortedUniv (α) [Fintype α] [Encodable α] : List α :=
  Finset.univ.sort (Encodable.encode' α ⁻¹'o (· <= ·))

@[simp]
/--
theorem `mem_sortedUniv` / 定理 `mem_sortedUniv`

English:
theorem mem_sortedUniv
  given: {α} [Fintype α] [Encodable α] (x : α)
  statement: x in sortedUniv α
  proof: (Finset.mem_sort _).2 (Finset.mem_univ _)

@[simp]

中文:
定理 mem_sortedUniv
  条件: {α} [Fintype α] [Encodable α] (x : α)
  结论: x in sortedUniv α
  证明: (Finset.mem_sort _).2 (Finset.mem_univ _)

@[simp]

Depends on / 依赖: Finset, Finset.mem_sort, Finset.mem_univ, mem_sort, mem_univ
-/
theorem mem_sortedUniv {α} [Fintype α] [Encodable α] (x : α) : x in sortedUniv α :=
  (Finset.mem_sort _).2 (Finset.mem_univ _)

@[simp]
/--
theorem `length_sortedUniv` / 定理 `length_sortedUniv`

English:
theorem length_sortedUniv
  given: (α) [Fintype α] [Encodable α]
  statement: (sortedUniv α).length = Fintype.card α
  proof: Finset.length_sort _

@[simp]

中文:
定理 length_sortedUniv
  条件: (α) [Fintype α] [Encodable α]
  结论: (sortedUniv α).length = Fintype.card α
  证明: Finset.length_sort _

@[simp]

Depends on / 依赖: Finset, Finset.length_sort, length_sort
-/
theorem length_sortedUniv (α) [Fintype α] [Encodable α] : (sortedUniv α).length = Fintype.card α :=
  Finset.length_sort _

@[simp]
/--
theorem `sortedUniv_nodup` / 定理 `sortedUniv_nodup`

English:
theorem sortedUniv_nodup
  given: (α) [Fintype α] [Encodable α]
  statement: (sortedUniv α).Nodup
  proof: Finset.sort_nodup _ _

@[simp]

中文:
定理 sortedUniv_nodup
  条件: (α) [Fintype α] [Encodable α]
  结论: (sortedUniv α).Nodup
  证明: Finset.sort_nodup _ _

@[simp]

Depends on / 依赖: Finset, Finset.sort_nodup, sort_nodup
-/
theorem sortedUniv_nodup (α) [Fintype α] [Encodable α] : (sortedUniv α).Nodup :=
  Finset.sort_nodup _ _

@[simp]
/--
theorem `sortedUniv_toFinset` / 定理 `sortedUniv_toFinset`

English:
theorem sortedUniv_toFinset
  given: (α) [Fintype α] [Encodable α] [DecidableEq α]
  proof: Finset.sort_toFinset _ _

中文:
定理 sortedUniv_toFinset
  条件: (α) [Fintype α] [Encodable α] [DecidableEq α]
  证明: Finset.sort_toFinset _ _

Depends on / 依赖: Finset, Finset.sort_toFinset, sort_toFinset
-/
theorem sortedUniv_toFinset (α) [Fintype α] [Encodable α] [DecidableEq α] :
    (sortedUniv α).toFinset = Finset.univ :=
  Finset.sort_toFinset _ _

/--
Definition of `fintypeEquivFin` / `fintypeEquivFin` 的定义

English:
definition fintypeEquivFin
  signature: {α} [Fintype α] [Encodable α]
  body: haveI : DecidableEq α := Encodable.decidableEqOfEncodable _
((sortedUniv_nodup α).getEquivOfForallMemList _ mem_sortedUniv).symm.trans
    Equiv.cast (congr_arg _ (length_sortedUniv α))

中文:
定义 fintypeEquivFin
  签名: {α} [Fintype α] [Encodable α]
  定义体: haveI : DecidableEq α := Encodable.decidableEqOfEncodable _
((sortedUniv_nodup α).getEquivOfForallMemList _ mem_sortedUniv).symm.trans
    Equiv.cast (congr_arg _ (length_sortedUniv α))

Depends on / 依赖: DecidableEq, Encodable, Encodable.decidableEqOfEncodable, Equiv.cast, congr_arg, decidableEqOfEncodable, getEquivOfForallMemList, length_sortedUniv, mem_sortedUniv, sortedUniv_nodup, symm.trans
-/
def fintypeEquivFin {α} [Fintype α] [Encodable α] : α ≃ Fin (Fintype.card α) :=
  haveI : DecidableEq α := Encodable.decidableEqOfEncodable _
((sortedUniv_nodup α).getEquivOfForallMemList _ mem_sortedUniv).symm.trans
    Equiv.cast (congr_arg _ (length_sortedUniv α))

end Encodable


namespace Denumerable
variable [Denumerable α]

/--
Definition of `lower'` / `lower'` 的定义

English:
definition lower'
  signature: : List Nat -> Nat -> List Nat

中文:
定义 lower'
  签名: : List 自然数 -> 自然数 -> List 自然数
-/
def lower' : List Nat -> Nat -> List Nat
  | [], _ => []
  | m :: l, n => (m - n) :: lower' l (m + 1)

/--
Definition of `raise'` / `raise'` 的定义

English:
definition raise'
  signature: : List Nat -> Nat -> List Nat

中文:
定义 raise'
  签名: : List 自然数 -> 自然数 -> List 自然数
-/
def raise' : List Nat -> Nat -> List Nat
  | [], _ => []
  | m :: l, n => (m + n) :: raise' l (m + n + 1)

/--
theorem `lower_raise'` / 定理 `lower_raise'`

English:
theorem lower_raise'
  statement: forall l n, lower' (raise' l n) n = l

中文:
定理 lower_raise'
  结论: 对任意 l n, lower' (raise' l n) n = l
-/
theorem lower_raise' : forall l n, lower' (raise' l n) n = l
  | [], _ => rfl
  | m :: l, n => by simp [raise', lower', lower_raise']

/--
theorem `raise_lower'` / 定理 `raise_lower'`

English:
theorem raise_lower'
  statement: forall {l n}, (forall m in l, n <= m) -> List.SortedLT l -> raise' (lower' l n) n = l
  proof: h₁ _ List.mem_cons_self
    simp [raise', lower', Nat.sub_add_cancel this,
      raise_lower' (fun _ => List.rel_of_pairwise_cons h₂.pairwise : forall a in l, m < a)
      h₂.pairwise.of_cons.sortedLT]

中文:
定理 raise_lower'
  结论: 对任意 {l n}, (对任意 m in l, n <= m) -> List.SortedLT l -> raise' (lower' l n) n = l
  证明: h₁ _ List.mem_cons_self
    simp [raise', lower', Nat.sub_add_cancel this,
      raise_lower' (fun _ => List.rel_of_pairwise_cons h₂.pairwise : forall a in l, m < a)
      h₂.pairwise.of_cons.sortedLT]

Depends on / 依赖: List.mem_cons_self, mem_cons_self
-/
theorem raise_lower' : forall {l n}, (forall m in l, n <= m) -> List.SortedLT l -> raise' (lower' l n) n = l
  | [], _, _, _ => rfl
  | m :: l, n, h₁, h₂ => by
    have : n <= m := h₁ _ List.mem_cons_self
    simp [raise', lower', Nat.sub_add_cancel this,
      raise_lower' (fun _ => List.rel_of_pairwise_cons h₂.pairwise : forall a in l, m < a)
      h₂.pairwise.of_cons.sortedLT]

/--
theorem `isChain_raise'` / 定理 `isChain_raise'`

English:
theorem isChain_raise'
  statement: forall (l) (n), List.IsChain (· < ·) (raise' l n)

中文:
定理 isChain_raise'
  结论: 对任意 (l) (n), List.IsChain (· < ·) (raise' l n)
-/
theorem isChain_raise' : forall (l) (n), List.IsChain (· < ·) (raise' l n)
  | [], _ => .nil
  | [_], _ => .singleton _
  | _ :: _ :: _, _ => .cons_cons (by lia) (isChain_raise' (_ :: _) _)

/--
theorem `isChain_cons_raise'` / 定理 `isChain_cons_raise'`

English:
theorem isChain_cons_raise'
  given: (l m)
  statement: List.IsChain (· < ·) (m :: raise' l (m + 1))
  proof: isChain_raise' (m :: l) 0

中文:
定理 isChain_cons_raise'
  条件: (l m)
  结论: List.IsChain (· < ·) (m :: raise' l (m + 1))
  证明: isChain_raise' (m :: l) 0

Depends on / 依赖: isChain_raise
-/
theorem isChain_cons_raise' (l m) : List.IsChain (· < ·) (m :: raise' l (m + 1)) :=
  isChain_raise' (m :: l) 0

/--
theorem `isChain_cons_raise'_of_lt` / 定理 `isChain_cons_raise'_of_lt`

English:
theorem isChain_cons_raise'_of_lt
  given: (l) {m n} (h : m < n)
  proof: by
  unfold raise'; cases l with grind [isChain_cons_raise']

中文:
定理 isChain_cons_raise'_of_lt
  条件: (l) {m n} (h : m < n)
  证明: by
  unfold raise'; cases l with grind [isChain_cons_raise']
-/
theorem isChain_cons_raise'_of_lt (l) {m n} (h : m < n) :
    List.IsChain (· < ·) (m :: raise' l n) := by
  unfold raise'; cases l with grind [isChain_cons_raise']

/--
theorem `raise'_sorted` / 定理 `raise'_sorted`

English:
theorem raise'_sorted
  given: (l n)
  statement: List.SortedLT (raise' l n)
  proof: (isChain_raise' _ _).sortedLT

中文:
定理 raise'_sorted
  条件: (l n)
  结论: List.SortedLT (raise' l n)
  证明: (isChain_raise' _ _).sortedLT

Depends on / 依赖: isChain_raise, sortedLT
-/
theorem raise'_sorted (l n) : List.SortedLT (raise' l n) := (isChain_raise' _ _).sortedLT

/--
Definition of `raise'Finset` / `raise'Finset` 的定义

English:
definition raise'Finset
  signature: (l : List Nat) (n : Nat)
  body: ⟨raise' l n, (raise'_sorted _ _).nodup⟩

中文:
定义 raise'Finset
  签名: (l : List 自然数) (n : 自然数)
  定义体: ⟨raise' l n, (raise'_sorted _ _).nodup⟩
-/
def raise'Finset (l : List Nat) (n : Nat) : Finset Nat :=
  ⟨raise' l n, (raise'_sorted _ _).nodup⟩

/--
Instance `finset` / 实例 `finset`

English:
instance finset
  signature: : Denumerable (Finset α)
  body: mk'
⟨fun s : Finset α => encode lower' (s.map (eqv α).toEmbedding).sort 0, fun n =>
      Finset.map (eqv α).symm.toEmbedding (raise'Finset (ofNat (List Nat) n) 0), fun s =>
Finset.eq_of_veq by
        simp [-Multiset.map_coe, raise'Finset,
          raise_lower' (fun n _ => Nat.zero_le n) (Finset.s

中文:
实例 finset
  签名: : Denumerable (Finset α)
  定义体: mk'
⟨fun s : Finset α => encode lower' (s.map (eqv α).toEmbedding).sort 0, fun n =>
      Finset.map (eqv α).symm.toEmbedding (raise'Finset (ofNat (List Nat) n) 0), fun s =>
Finset.eq_of_veq by
        simp [-Multiset.map_coe, raise'Finset,
          raise_lower' (fun n _ => Nat.zero_le n) (Finset.s

Depends on / 依赖: Finset, Finset.eq_of_veq, Finset.map, Finset.sort, Finset.sortedLT_sort, List.mergeSort_eq_self, Multiset, Multiset.map_coe, Nat.zero_le, _sorted, encode, eq_of_veq, lower_raise, map_coe, mergeSort_eq_self, pairwise, raise_lower, s.map, sortedLE, sortedLE.pairwise
-/
instance finset : Denumerable (Finset α) :=
  mk'
⟨fun s : Finset α => encode lower' (s.map (eqv α).toEmbedding).sort 0, fun n =>
      Finset.map (eqv α).symm.toEmbedding (raise'Finset (ofNat (List Nat) n) 0), fun s =>
Finset.eq_of_veq by
        simp [-Multiset.map_coe, raise'Finset,
          raise_lower' (fun n _ => Nat.zero_le n) (Finset.sortedLT_sort _)],
      fun n => by
      simp [-Multiset.map_coe, Finset.map, raise'Finset, Finset.sort,
        List.mergeSort_eq_self _ (raise'_sorted _ _).sortedLE.pairwise, lower_raise']⟩

end Denumerable
