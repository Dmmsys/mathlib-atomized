/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Denumerable

/-!
# Equivalences involving `List`-like types

This file defines some additional constructive equivalences using `Encodable` and the pairing
function on `ℕ`.
-/

@[expose] public section

assert_not_exists Monoid Multiset.sort

open List
open Nat

namespace Equiv

/--
Definition of `listEquivOfEquiv` / `listEquivOfEquiv` 的定义

English:
definition listEquivOfEquiv
  signature: {α β} (e : α ≃ β)
  body: List.map e
  invFun := List.map e.symm
  left_inv l := by rw [List.map_map, e.symm_comp_self, List.map_id]
  right_inv l := by rw [List.map_map, e.self_comp_symm, List.map_id]

中文:
定义 listEquivOfEquiv
  签名: {α β} (e : α ≃ β)
  定义体: List.map e
  invFun := List.map e.symm
  left_inv l := by rw [List.map_map, e.symm_comp_self, List.map_id]
  right_inv l := by rw [List.map_map, e.self_comp_symm, List.map_id]

Depends on / 依赖: List.map
-/
def listEquivOfEquiv {α β} (e : α ≃ β) : List α ≃ List β where
  toFun := List.map e
  invFun := List.map e.symm
  left_inv l := by rw [List.map_map, e.symm_comp_self, List.map_id]
  right_inv l := by rw [List.map_map, e.self_comp_symm, List.map_id]

end Equiv

namespace Encodable

variable {α : Type*}

section List

variable [Encodable α]

/--
Definition of `encodeList` / `encodeList` 的定义

English:
definition encodeList
  signature: : List α -> Nat

中文:
定义 encodeList
  签名: : List α -> 自然数
-/
def encodeList : List α -> Nat
  | [] => 0
  | a :: l => succ (pair (encode a) (encodeList l))

/--
Definition of `decodeList` / `decodeList` 的定义

English:
definition decodeList
  signature: : Nat -> Option (List α)
  body: lt_succ_of_le h
(· :: ·) < > decode (α := α) v₁ <*> decodeList v₂

@[simp]

中文:
定义 decodeList
  签名: : 自然数 -> Option (List α)
  定义体: lt_succ_of_le h
(· :: ·) < > decode (α := α) v₁ <*> decodeList v₂

@[simp]

Depends on / 依赖: lt_succ_of_le
-/
def decodeList : Nat -> Option (List α)
  | 0 => some []
  | succ v =>
    match unpair v, unpair_right_le v with
    | (v₁, v₂), h =>
      have : v₂ < succ v := lt_succ_of_le h
(· :: ·) < > decode (α := α) v₁ <*> decodeList v₂

@[simp]
/--
theorem `decodeList_encodeList_eq_self` / 定理 `decodeList_encodeList_eq_self`

English:
theorem decodeList_encodeList_eq_self
  given: (l : List α)
  statement: decodeList (encodeList l) = some l
  proof: by
  induction l <;> simp [encodeList, decodeList, unpair_pair, encodek, *]

中文:
定理 decodeList_encodeList_eq_self
  条件: (l : List α)
  结论: decodeList (encodeList l) = some l
  证明: by
  induction l <;> simp [encodeList, decodeList, unpair_pair, encodek, *]

Depends on / 依赖: decodeList, encodeList, encodek, unpair_pair
-/
theorem decodeList_encodeList_eq_self (l : List α) : decodeList (encodeList l) = some l := by
  induction l <;> simp [encodeList, decodeList, unpair_pair, encodek, *]

/--
Instance `_root_.List.encodable` / 实例 `_root_.List.encodable`

English:
instance _root_.List.encodable
  signature: : Encodable (List α)
  body: ⟨encodeList, decodeList, decodeList_encodeList_eq_self⟩

中文:
实例 _root_.List.encodable
  签名: : Encodable (List α)
  定义体: ⟨encodeList, decodeList, decodeList_encodeList_eq_self⟩

Depends on / 依赖: decodeList, decodeList_encodeList_eq_self, encodeList
-/
instance _root_.List.encodable : Encodable (List α) :=
  ⟨encodeList, decodeList, decodeList_encodeList_eq_self⟩

/--
Instance `_root_.List.countable` / 实例 `_root_.List.countable`

English:
instance _root_.List.countable
  signature: {α : Type*} [Countable α]
  body: by
  have := Encodable.ofCountable α
  infer_instance

@[simp]

中文:
实例 _root_.List.countable
  签名: {α : 类型} [Countable α]
  定义体: by
  have := Encodable.ofCountable α
  infer_instance

@[simp]

Depends on / 依赖: Encodable, Encodable.ofCountable, infer_instance, ofCountable
-/
instance _root_.List.countable {α : Type*} [Countable α] : Countable (List α) := by
  have := Encodable.ofCountable α
  infer_instance

@[simp]
/--
theorem `encode_list_nil` / 定理 `encode_list_nil`

English:
theorem encode_list_nil
  statement: encode (@nil α) = 0
  proof: rfl

@[simp]

中文:
定理 encode_list_nil
  结论: encode (@nil α) = 0
  证明: rfl

@[simp]
-/
theorem encode_list_nil : encode (@nil α) = 0 :=
  rfl

@[simp]
/--
theorem `encode_list_cons` / 定理 `encode_list_cons`

English:
theorem encode_list_cons
  given: (a : α) (l : List α)
  proof: rfl

@[simp]

中文:
定理 encode_list_cons
  条件: (a : α) (l : List α)
  证明: rfl

@[simp]
-/
theorem encode_list_cons (a : α) (l : List α) :
    encode (a :: l) = succ (pair (encode a) (encode l)) :=
  rfl

@[simp]
/--
theorem `decode_list_zero` / 定理 `decode_list_zero`

English:
theorem decode_list_zero
  statement: decode (α := List α) 0 = some []
  proof: show decodeList 0 = some [] by rw [decodeList]

@[simp]

中文:
定理 decode_list_zero
  结论: decode (α := List α) 0 = some []
  证明: show decodeList 0 = some [] by rw [decodeList]

@[simp]
-/
theorem decode_list_zero : decode (α := List α) 0 = some [] :=
  show decodeList 0 = some [] by rw [decodeList]

@[simp]
/--
theorem `decode_list_succ` / 定理 `decode_list_succ`

English:
theorem decode_list_succ
  given: (v : Nat)
  proof: show decodeList (succ v) = _ by
    rcases e : unpair v with ⟨v₁, v₂⟩
    simp [decodeList, e]; rfl

中文:
定理 decode_list_succ
  条件: (v : 自然数)
  证明: show decodeList (succ v) = _ by
    rcases e : unpair v with ⟨v₁, v₂⟩
    simp [decodeList, e]; rfl
-/
theorem decode_list_succ (v : Nat) :
    decode (α := List α) (succ v) =
(· :: ·) < > decode (α := α) v.unpair.1 <*> decode (α := List α) v.unpair.2 :=
  show decodeList (succ v) = _ by
    rcases e : unpair v with ⟨v₁, v₂⟩
    simp [decodeList, e]; rfl

/--
theorem `length_le_encode` / 定理 `length_le_encode`

English:
theorem length_le_encode
  statement: forall l : List α, length l <= encode l

中文:
定理 length_le_encode
  结论: 对任意 l : List α, length l <= encode l
-/
theorem length_le_encode : forall l : List α, length l <= encode l
  | [] => Nat.zero_le _
| _ :: l => succ_le_succ (length_le_encode l).trans (right_le_pair _ _)

end List

/-! These two lemmas are not about lists, but are convenient to keep here and don't
require `Finset.sort`. -/

/--
Instance `_root_.Multiset.countable` / 实例 `_root_.Multiset.countable`

English:
instance _root_.Multiset.countable
  signature: [Countable α]
  body: Quotient.countable

中文:
实例 _root_.Multiset.countable
  签名: [Countable α]
  定义体: Quotient.countable

Depends on / 依赖: Quotient, Quotient.countable, countable
-/
instance _root_.Multiset.countable [Countable α] : Countable (Multiset α) :=
  Quotient.countable

/--
Instance `_root_.Finset.countable` / 实例 `_root_.Finset.countable`

English:
instance _root_.Finset.countable
  signature: [Countable α]
  body: Finset.val_injective.countable

中文:
实例 _root_.Finset.countable
  签名: [Countable α]
  定义体: Finset.val_injective.countable

Depends on / 依赖: Finset, Finset.val_injective.countable, countable, val_injective
-/
instance _root_.Finset.countable [Countable α] : Countable (Finset α) :=
  Finset.val_injective.countable

/-- A listable type with decidable equality is encodable. -/
@[instance_reducible]
/--
Definition of `encodableOfList` / `encodableOfList` 的定义

English:
definition encodableOfList
  signature: [DecidableEq α] (l : List α) (H : forall x, x in l)
  body: ⟨fun a => idxOf a l, (l[·]?), fun _ => getElem?_idxOf (H _)⟩

中文:
定义 encodableOfList
  签名: [DecidableEq α] (l : List α) (H : 对任意 x, x in l)
  定义体: ⟨fun a => idxOf a l, (l[·]?), fun _ => getElem?_idxOf (H _)⟩

Depends on / 依赖: _idxOf, getElem
-/
def encodableOfList [DecidableEq α] (l : List α) (H : forall x, x in l) : Encodable α :=
  ⟨fun a => idxOf a l, (l[·]?), fun _ => getElem?_idxOf (H _)⟩

/--
Definition of `_root_.Fintype.truncEncodable` / `_root_.Fintype.truncEncodable` 的定义

English:
definition _root_.Fintype.truncEncodable
  signature: (α : Type*) [DecidableEq α] [Fintype α]
  body: @Quot.recOnSubsingleton _ _ (fun s : Multiset α => (forall x : α, x in s) -> Trunc (Encodable α)) _
    Finset.univ.1 (fun l H => Trunc.mk <| encodableOfList l H) Finset.mem_univ

中文:
定义 _root_.Fintype.truncEncodable
  签名: (α : 类型) [DecidableEq α] [Fintype α]
  定义体: @Quot.recOnSubsingleton _ _ (fun s : Multiset α => (forall x : α, x in s) -> Trunc (Encodable α)) _
    Finset.univ.1 (fun l H => Trunc.mk <| encodableOfList l H) Finset.mem_univ

Depends on / 依赖: Encodable, Finset, Finset.mem_univ, Finset.univ, Multiset, Quot.recOnSubsingleton, Trunc.mk, encodableOfList, mem_univ, recOnSubsingleton
-/
def _root_.Fintype.truncEncodable (α : Type*) [DecidableEq α] [Fintype α] : Trunc (Encodable α) :=
  @Quot.recOnSubsingleton _ _ (fun s : Multiset α => (forall x : α, x in s) -> Trunc (Encodable α)) _
    Finset.univ.1 (fun l H => Trunc.mk <| encodableOfList l H) Finset.mem_univ

/-- A noncomputable way to arbitrarily choose an ordering on a finite type.
It is not made into a global instance, since it involves an arbitrary choice.
This can be locally made into an instance with `attribute [local instance] Fintype.toEncodable`. -/
@[instance_reducible]
/--
Definition of `_root_.Fintype.toEncodable` / `_root_.Fintype.toEncodable` 的定义

English:
definition _root_.Fintype.toEncodable
  signature: (α : Type*) [Fintype α]
  body: by
  classical exact (Fintype.truncEncodable α).out

中文:
定义 _root_.Fintype.toEncodable
  签名: (α : 类型) [Fintype α]
  定义体: by
  classical exact (Fintype.truncEncodable α).out

Depends on / 依赖: Fintype, Fintype.truncEncodable, classical, truncEncodable
-/
noncomputable def _root_.Fintype.toEncodable (α : Type*) [Fintype α] : Encodable α := by
  classical exact (Fintype.truncEncodable α).out

end Encodable

namespace Denumerable

variable {α : Type*} {β : Type*} [Denumerable α] [Denumerable β]

open Encodable

section List

/--
theorem `denumerable_list_aux` / 定理 `denumerable_list_aux`

English:
theorem denumerable_list_aux
  statement: forall n : Nat, exists a in @decodeList α _ n, encodeList a = n
  proof: unpair_right_le v
    rw [e] at h
    rcases have : v₂ < succ v := lt_succ_of_le h
      denumerable_list_aux v₂ with
      ⟨a, h₁, h₂⟩
    rw [Option.mem_def] at h₁
    use ofNat α v₁ :: a
    simp [decodeList, e, h₂, h₁, encodeList, pair_eq_of_unpair_eq e]

中文:
定理 denumerable_list_aux
  结论: 对任意 n : 自然数, 存在 a in @decodeList α _ n, encodeList a = n
  证明: unpair_right_le v
    rw [e] at h
    rcases have : v₂ < succ v := lt_succ_of_le h
      denumerable_list_aux v₂ with
      ⟨a, h₁, h₂⟩
    rw [Option.mem_def] at h₁
    use ofNat α v₁ :: a
    simp [decodeList, e, h₂, h₁, encodeList, pair_eq_of_unpair_eq e]

Depends on / 依赖: unpair_right_le
-/
theorem denumerable_list_aux : forall n : Nat, exists a in @decodeList α _ n, encodeList a = n
  | 0 => by rw [decodeList]; exact ⟨_, rfl, rfl⟩
  | succ v => by
    rcases e : unpair v with ⟨v₁, v₂⟩
    have h := unpair_right_le v
    rw [e] at h
    rcases have : v₂ < succ v := lt_succ_of_le h
      denumerable_list_aux v₂ with
      ⟨a, h₁, h₂⟩
    rw [Option.mem_def] at h₁
    use ofNat α v₁ :: a
    simp [decodeList, e, h₂, h₁, encodeList, pair_eq_of_unpair_eq e]

/--
Instance `denumerableList` / 实例 `denumerableList`

English:
instance denumerableList
  signature: : Denumerable (List α)
  body: ⟨denumerable_list_aux⟩

@[simp]

中文:
实例 denumerableList
  签名: : Denumerable (List α)
  定义体: ⟨denumerable_list_aux⟩

@[simp]

Depends on / 依赖: denumerable_list_aux
-/
instance denumerableList : Denumerable (List α) :=
  ⟨denumerable_list_aux⟩

@[simp]
/--
theorem `list_ofNat_zero` / 定理 `list_ofNat_zero`

English:
theorem list_ofNat_zero
  statement: ofNat (List α) 0 = []
  proof: by rw [← @encode_list_nil α, ofNat_encode]

@[simp]

中文:
定理 list_ofNat_zero
  结论: of自然数 (List α) 0 = []
  证明: by rw [← @encode_list_nil α, ofNat_encode]

@[simp]

Depends on / 依赖: encode_list_nil, ofNat_encode
-/
theorem list_ofNat_zero : ofNat (List α) 0 = [] := by rw [← @encode_list_nil α, ofNat_encode]

@[simp]
/--
theorem `list_ofNat_succ` / 定理 `list_ofNat_succ`

English:
theorem list_ofNat_succ
  given: (v : Nat)
  proof: ofNat_of_decode
    show decodeList (succ v) = _ by
      rcases e : unpair v with ⟨v₁, v₂⟩
      simp [decodeList, e, show decodeList v₂ = decode (α := List α) v₂ from rfl]

中文:
定理 list_ofNat_succ
  条件: (v : 自然数)
  证明: ofNat_of_decode
    show decodeList (succ v) = _ by
      rcases e : unpair v with ⟨v₁, v₂⟩
      simp [decodeList, e, show decodeList v₂ = decode (α := List α) v₂ from rfl]

Depends on / 依赖: decode, decodeList, ofNat_of_decode, unpair
-/
theorem list_ofNat_succ (v : Nat) :
    ofNat (List α) (succ v) = ofNat α v.unpair.1 :: ofNat (List α) v.unpair.2 :=
ofNat_of_decode
    show decodeList (succ v) = _ by
      rcases e : unpair v with ⟨v₁, v₂⟩
      simp [decodeList, e, show decodeList v₂ = decode (α := List α) v₂ from rfl]

end List

end Denumerable

namespace Equiv

/-- A list on a unique type is equivalent to ℕ by sending each list to its length. -/
@[simps!]
/--
Definition of `listUniqueEquiv` / `listUniqueEquiv` 的定义

English:
definition listUniqueEquiv
  signature: (α : Type*) [Unique α]
  body: List.length
  invFun n := List.replicate n default
  left_inv u := List.length_injective (by simp)
  right_inv n := List.length_replicate

中文:
定义 listUniqueEquiv
  签名: (α : 类型) [Unique α]
  定义体: List.length
  invFun n := List.replicate n default
  left_inv u := List.length_injective (by simp)
  right_inv n := List.length_replicate

Depends on / 依赖: List.length, length
-/
def listUniqueEquiv (α : Type*) [Unique α] : List α ≃ Nat where
  toFun := List.length
  invFun n := List.replicate n default
  left_inv u := List.length_injective (by simp)
  right_inv n := List.length_replicate

/--
Definition of `listNatEquivNat` / `listNatEquivNat` 的定义

English:
definition listNatEquivNat
  signature: : List Nat ≃ Nat
  body: Denumerable.eqv _

中文:
定义 listNatEquivNat
  签名: : List 自然数 ≃ 自然数
  定义体: Denumerable.eqv _

Depends on / 依赖: Denumerable, Denumerable.eqv
-/
def listNatEquivNat : List Nat ≃ Nat :=
  Denumerable.eqv _

/--
Definition of `listEquivSelfOfEquivNat` / `listEquivSelfOfEquivNat` 的定义

English:
definition listEquivSelfOfEquivNat
  signature: {α : Type*} (e : α ≃ Nat)
  body: calc
    List α ≃ List Nat := listEquivOfEquiv e
    _ ≃ Nat := listNatEquivNat
    _ ≃ α := e.symm

中文:
定义 listEquivSelfOfEquivNat
  签名: {α : 类型} (e : α ≃ 自然数)
  定义体: calc
    List α ≃ List Nat := listEquivOfEquiv e
    _ ≃ Nat := listNatEquivNat
    _ ≃ α := e.symm

Depends on / 依赖: e.symm, listEquivOfEquiv, listNatEquivNat
-/
def listEquivSelfOfEquivNat {α : Type*} (e : α ≃ Nat) : List α ≃ α :=
  calc
    List α ≃ List Nat := listEquivOfEquiv e
    _ ≃ Nat := listNatEquivNat
    _ ≃ α := e.symm

end Equiv
