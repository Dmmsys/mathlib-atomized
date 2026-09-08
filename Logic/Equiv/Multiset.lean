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
/-
**enle** 是 Mathlib 中的一个定义，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def enle : α → α → Prop :=
  encode ⁻¹'o (· ≤ ·)
deriving DecidableRel

set_option backward.privateInPublic true in
private local instance enle.isLinearOrder : IsLinearOrder α enle :=
  (RelEmbedding.preimage ⟨encode, encode_injective⟩ (· ≤ ·)).isLinearOrder

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Explicit encoding function for `Multiset α` -/
/-
**encodeMultiset** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：encodeMultiset (s : Multiset α) : Nat
参数：s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit encoding function for `Multiset α`
-/
def encodeMultiset (s : Multiset α) : ℕ :=
  encode (s.sort enle)

/-- Explicit decoding function for `Multiset α` -/
/-
**decodeMultiset** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：decodeMultiset (n : Nat) : Option (Multiset α)
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Explicit decoding function for `Multiset α`
-/
def decodeMultiset (n : ℕ) : Option (Multiset α) :=
  ((↑) : List α → Multiset α) <$> decode (α := List α) n

/-- If `α` is encodable, then so is `Multiset α`. -/
/-
**_root_.Multiset.encodable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：_root_.Multiset.encodable : Encodable (Multiset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is encodable, then so is `Multiset α`.
-/
instance _root_.Multiset.encodable : Encodable (Multiset α) :=
  ⟨encodeMultiset, decodeMultiset, fun s => by simp [encodeMultiset, decodeMultiset, encodek]⟩

end Finset

namespace Denumerable
variable [Denumerable α]

section Multiset

/-- Outputs the list of differences of the input list, that is
`lower [a₁, a₂, ...] n = [a₁ - n, a₂ - a₁, ...]` -/
/-
**Denumerable.lower** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
形式化陈述：List ℕ → ℕ → List ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Outputs the list of differences of the input list, that is
`lower [a₁, a₂, ...] n = [a₁ - n, a₂ - a₁, ...]`
-/
def lower : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: l, n => (m - n) :: lower l m

/-- Outputs the list of partial sums of the input list, that is
`raise [a₁, a₂, ...] n = [n + a₁, n + a₁ + a₂, ...]` -/
/-
**Denumerable.raise** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
形式化陈述：List ℕ → ℕ → List ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Outputs the list of partial sums of the input list, that is
`raise [a₁, a₂, ...] n = [n + a₁, n + a₁ + a₂, ...]`
-/
def raise : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: l, n => (m + n) :: raise l (m + n)
/-
**Denumerable.lower_raise** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：∀ (l : List ℕ) (n : ℕ), Denumerable.lower (Denumerable.raise l n) n = l
参数：l : List ℕ；n : ℕ；Denumerable.raise l n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lower_raise : ∀ l n, lower (raise l n) n = l
  | [], _ => rfl
  | m :: l, n => by rw [raise, lower, Nat.add_sub_cancel_right, lower_raise l]
/-
**Denumerable.raise_lower** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：raise_lower : forall {l n}, List.SortedLE (n :: l) -> raise (lower l n) n 
= l | [], _, _ => rfl | m :: l, n, h => by have : n <= m
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem raise_lower : ∀ {l n}, List.SortedLE (n :: l) → raise (lower l n) n = l
  | [], _, _ => rfl
  | m :: l, n, h => by
    have : n ≤ m := List.rel_of_pairwise_cons h.pairwise List.mem_cons_self
    simp [raise, lower, Nat.sub_add_cancel this, raise_lower h.pairwise.of_cons.sortedLE]
/-
**Denumerable.isChain_raise** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：∀ (l : List ℕ) (n : ℕ), List.IsChain (fun x1 x2 => x1 ≤ x2) (Denumerable.r
aise l n)
参数：l : List ℕ；n : ℕ；fun x1 x2 => x1 ≤ x2；Denumerable.raise l n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_raise : ∀ l n, List.IsChain (· ≤ ·) (raise l n)
  | [], _ => .nil
  | [_], _ => .singleton _
  | _ :: _ :: _, _ => .cons_cons (Nat.le_add_left _ _) (isChain_raise (_ :: _) _)
/-
**Denumerable.isChain_cons_raise** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：isChain_cons_raise (l n) : List.IsChain (· <= ·) (n :: raise l n)
参数：l n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.isChain_raise`：∀ (l : List ℕ) (n : ℕ), List.IsChain (fun x1 
x2 => x1 ≤ x2) (Denumerable.raise l n)
-/
theorem isChain_cons_raise (l n) : List.IsChain (· ≤ ·) (n :: raise l n) :=
  isChain_raise (n :: l) 0

/-- `raise l n` is a non-decreasing sequence. -/
/-
**Denumerable.raise_sorted** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：raise_sorted (l n) : List.SortedLE (raise l n)
参数：l n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α]
, List.IsChain (fun x1 x2 => x1 ≤ x2) l → l.SortedLE
· 使用定理 `Denumerable.isChain_raise`：∀ (l : List ℕ) (n : ℕ), List.IsChain (fun x1 
x2 => x1 ≤ x2) (Denumerable.raise l n)

--- 原说明 ---
`raise l n` is a non-decreasing sequence.
-/
theorem raise_sorted (l n) : List.SortedLE (raise l n) := (isChain_raise _ _).sortedLE

/-- If `α` is denumerable, then so is `Multiset α`. Warning: this is *not* the same encoding as used
in `Multiset.encodable`. -/
/-
**Denumerable.multiset** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：multiset : Denumerable (Multiset α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2

--- 原说明 ---
If `α` is denumerable, then so is `Multiset α`. Warning: this is *not* the same 
encoding as used
in `Multiset.encodable`.
-/
instance multiset : Denumerable (Multiset α) :=
  mk'
    ⟨fun s : Multiset α => encode <| lower (s.map encode).sort 0,
     fun n =>
      Multiset.map (ofNat α) (raise (ofNat (List ℕ) n) 0),
     fun s => by
      have :=
        raise_lower (List.pairwise_cons.2 ⟨fun n _ => Nat.zero_le n,
        (s.map encode).pairwise_sort _⟩).sortedLE
      simp [-Multiset.map_coe, this],
     fun n => by
      simp [-Multiset.map_coe, List.mergeSort_eq_self _ (raise_sorted _ _).pairwise, lower_raise]⟩

end Multiset

end Denumerable

