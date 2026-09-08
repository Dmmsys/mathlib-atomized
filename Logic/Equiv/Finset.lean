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

/-- If `α` is encodable, then so is `Finset α`. -/
/-
**Finset.encodable** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Finset.encodable [Encodable α] : Encodable (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` is encodable, then so is `Finset α`.
-/
instance Finset.encodable [Encodable α] : Encodable (Finset α) :=
  haveI := decidableEqOfEncodable α
  ofEquiv { s : Multiset α // s.Nodup }
    { toFun := fun ⟨a, b⟩ => ⟨a, b⟩
      invFun := fun ⟨a, b⟩ => ⟨a, b⟩ }

namespace Encodable

/-- The elements of a `Fintype` as a sorted list. -/
/-
**Encodable.sortedUniv** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：sortedUniv (α) [Fintype α] [Encodable α] : List α
参数：α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Encodable.instAntisymmPreimageNatCoeEmbeddingEncode'Le`：∀ {α : Type u_1}
 [inst : Encodable α], Std.Antisymm (⇑(Encodable.encode' α) ⁻¹'o fun x1 x2 => x1
 ≤ x2)
· 使用定理 `Encodable.instTotalPreimageNatCoeEmbeddingEncode'Le`：∀ {α : Type u_1} [i
nst : Encodable α], Std.Total (⇑(Encodable.encode' α) ⁻¹'o fun x1 x2 => x1 ≤ x2)

--- 原说明 ---
The elements of a `Fintype` as a sorted list.
-/
def sortedUniv (α) [Fintype α] [Encodable α] : List α :=
  Finset.univ.sort (Encodable.encode' α ⁻¹'o (· ≤ ·))

@[simp]
/-
**Encodable.mem_sortedUniv** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：mem_sortedUniv {α} [Fintype α] [Encodable α] (x : α) : x in sortedUniv α
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Encodable.instAntisymmPreimageNatCoeEmbeddingEncode'Le`：∀ {α : Type u_1}
 [inst : Encodable α], Std.Antisymm (⇑(Encodable.encode' α) ⁻¹'o fun x1 x2 => x1
 ≤ x2)
· 使用定理 `Encodable.instTotalPreimageNatCoeEmbeddingEncode'Le`：∀ {α : Type u_1} [i
nst : Encodable α], Std.Total (⇑(Encodable.encode' α) ⁻¹'o fun x1 x2 => x1 ≤ x2)
· 使用定理 `Finset.mem_sort`：mem_sort {a : α} : a in sort s r ↔ a in s
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
theorem mem_sortedUniv {α} [Fintype α] [Encodable α] (x : α) : x ∈ sortedUniv α :=
  (Finset.mem_sort _).2 (Finset.mem_univ _)

@[simp]
/-
**Encodable.length_sortedUniv** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：length_sortedUniv (α) [Fintype α] [Encodable α] : (sortedUniv α).length = 
Fintype.card α
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.length_sort`：length_sort : (sort s r).length = s.card
· 使用定理 `Encodable.instAntisymmPreimageNatCoeEmbeddingEncode'Le`：∀ {α : Type u_1}
 [inst : Encodable α], Std.Antisymm (⇑(Encodable.encode' α) ⁻¹'o fun x1 x2 => x1
 ≤ x2)
· 使用定理 `Encodable.instTotalPreimageNatCoeEmbeddingEncode'Le`：∀ {α : Type u_1} [i
nst : Encodable α], Std.Total (⇑(Encodable.encode' α) ⁻¹'o fun x1 x2 => x1 ≤ x2)
-/
theorem length_sortedUniv (α) [Fintype α] [Encodable α] : (sortedUniv α).length = Fintype.card α :=
  Finset.length_sort _

@[simp]
/-
**Encodable.sortedUniv_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：sortedUniv_nodup (α) [Fintype α] [Encodable α] : (sortedUniv α).Nodup
参数：α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sort_nodup`：sort_nodup : (sort s r).Nodup
· 使用定理 `Encodable.instAntisymmPreimageNatCoeEmbeddingEncode'Le`：∀ {α : Type u_1}
 [inst : Encodable α], Std.Antisymm (⇑(Encodable.encode' α) ⁻¹'o fun x1 x2 => x1
 ≤ x2)
· 使用定理 `Encodable.instTotalPreimageNatCoeEmbeddingEncode'Le`：∀ {α : Type u_1} [i
nst : Encodable α], Std.Total (⇑(Encodable.encode' α) ⁻¹'o fun x1 x2 => x1 ≤ x2)
-/
theorem sortedUniv_nodup (α) [Fintype α] [Encodable α] : (sortedUniv α).Nodup :=
  Finset.sort_nodup _ _

@[simp]
/-
**Encodable.sortedUniv_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Encodable`。
形式化陈述：sortedUniv_toFinset (α) [Fintype α] [Encodable α] [DecidableEq α] : (sorte
dUniv α).toFinset = Finset.univ
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sort_toFinset`：sort_toFinset [DecidableEq α] : (sort s r).toFinse
t = s
· 使用定理 `Encodable.instAntisymmPreimageNatCoeEmbeddingEncode'Le`：∀ {α : Type u_1}
 [inst : Encodable α], Std.Antisymm (⇑(Encodable.encode' α) ⁻¹'o fun x1 x2 => x1
 ≤ x2)
· 使用定理 `Encodable.instTotalPreimageNatCoeEmbeddingEncode'Le`：∀ {α : Type u_1} [i
nst : Encodable α], Std.Total (⇑(Encodable.encode' α) ⁻¹'o fun x1 x2 => x1 ≤ x2)
-/
theorem sortedUniv_toFinset (α) [Fintype α] [Encodable α] [DecidableEq α] :
    (sortedUniv α).toFinset = Finset.univ :=
  Finset.sort_toFinset _ _

/-- An encodable `Fintype` is equivalent to the same size `Fin`. -/
/-
**Encodable.fintypeEquivFin** 是 Mathlib 中的一个定义，位于命名空间 `Encodable`。
形式化陈述：fintypeEquivFin {α} [Fintype α] [Encodable α] : α ≃ Fin (Fintype.card α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Encodable.sortedUniv_nodup`：sortedUniv_nodup (α) [Fintype α] [Encodable 
α] : (sortedUniv α).Nodup
· 使用定理 `Encodable.mem_sortedUniv`：mem_sortedUniv {α} [Fintype α] [Encodable α] (
x : α) : x in sortedUniv α

--- 原说明 ---
An encodable `Fintype` is equivalent to the same size `Fin`.
-/
def fintypeEquivFin {α} [Fintype α] [Encodable α] : α ≃ Fin (Fintype.card α) :=
  haveI : DecidableEq α := Encodable.decidableEqOfEncodable _
  ((sortedUniv_nodup α).getEquivOfForallMemList _ mem_sortedUniv).symm.trans <|
    Equiv.cast (congr_arg _ (length_sortedUniv α))

end Encodable


namespace Denumerable
variable [Denumerable α]

/-- Outputs the list of differences minus one of the input list, that is
`lower' [a₁, a₂, a₃, ...] n = [a₁ - n, a₂ - a₁ - 1, a₃ - a₂ - 1, ...]`. -/
/-
**Denumerable.lower'** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
形式化陈述：List ℕ → ℕ → List ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Outputs the list of differences minus one of the input list, that is
`lower' [a₁, a₂, a₃, ...] n = [a₁ - n, a₂ - a₁ - 1, a₃ - a₂ - 1, ...]`.
-/
def lower' : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: l, n => (m - n) :: lower' l (m + 1)

/-- Outputs the list of partial sums plus one of the input list, that is
`raise [a₁, a₂, a₃, ...] n = [n + a₁, n + a₁ + a₂ + 1, n + a₁ + a₂ + a₃ + 2, ...]`. Adding one each
time ensures the elements are distinct. -/
/-
**Denumerable.raise'** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：raise'_sorted (l n) : List.SortedLT (raise' l n)
参数：l n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Outputs the list of partial sums plus one of the input list, that is
`raise [a₁, a₂, a₃, ...] n = [n + a₁, n + a₁ + a₂ + 1, n + a₁ + a₂ + a₃ + 2, ...
]`. Adding one each
time ensures the elements are distinct.
-/
def raise' : List ℕ → ℕ → List ℕ
  | [], _ => []
  | m :: l, n => (m + n) :: raise' l (m + n + 1)
/-
**Denumerable.lower_raise'** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：∀ (l : List ℕ) (n : ℕ), Denumerable.lower' (Denumerable.raise' l n) n = l
参数：l : List ℕ；n : ℕ；Denumerable.raise' l n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.raise'`：raise'_sorted (l n) : List.SortedLT (raise' l n)
-/
theorem lower_raise' : ∀ l n, lower' (raise' l n) n = l
  | [], _ => rfl
  | m :: l, n => by simp [raise', lower', lower_raise']
/-
**Denumerable.raise_lower'** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：raise_lower' : forall {l n}, (forall m in l, n <= m) -> List.SortedLT l ->
 raise' (lower' l n) n = l | [], _, _, _ => rfl | m :: l, n, h₁, h₂ => by have :
 n <= m
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.raise'`：raise'_sorted (l n) : List.SortedLT (raise' l n)
-/
theorem raise_lower' : ∀ {l n}, (∀ m ∈ l, n ≤ m) → List.SortedLT l → raise' (lower' l n) n = l
  | [], _, _, _ => rfl
  | m :: l, n, h₁, h₂ => by
    have : n ≤ m := h₁ _ List.mem_cons_self
    simp [raise', lower', Nat.sub_add_cancel this,
      raise_lower' (fun _ => List.rel_of_pairwise_cons h₂.pairwise : ∀ a ∈ l, m < a)
      h₂.pairwise.of_cons.sortedLT]
/-
**Denumerable.isChain_raise'** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：∀ (l : List ℕ) (n : ℕ), List.IsChain (fun x1 x2 => x1 < x2) (Denumerable.r
aise' l n)
参数：l : List ℕ；n : ℕ；fun x1 x2 => x1 < x2；Denumerable.raise' l n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.raise'`：raise'_sorted (l n) : List.SortedLT (raise' l n)
-/
theorem isChain_raise' : ∀ (l) (n), List.IsChain (· < ·) (raise' l n)
  | [], _ => .nil
  | [_], _ => .singleton _
  | _ :: _ :: _, _ => .cons_cons (by lia) (isChain_raise' (_ :: _) _)
/-
**Denumerable.isChain_cons_raise'** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：isChain_cons_raise' (l m) : List.IsChain (· < ·) (m :: raise' l (m + 1))
参数：l m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.isChain_raise'`：∀ (l : List ℕ) (n : ℕ), List.IsChain (fun x1
 x2 => x1 < x2) (Denumerable.raise' l n)
-/
theorem isChain_cons_raise' (l m) : List.IsChain (· < ·) (m :: raise' l (m + 1)) :=
  isChain_raise' (m :: l) 0
/-
**Denumerable.isChain_cons_raise'_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：∀ (l : List ℕ) {m n : ℕ}, m < n → List.IsChain (fun x1 x2 => x1 < x2) (m :
: Denumerable.raise' l n)
参数：l : List ℕ；fun x1 x2 => x1 < x2；m :: Denumerable.raise' l n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.raise'`：raise'_sorted (l n) : List.SortedLT (raise' l n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Denumerable.raise'.eq_def`：∀ (x : List ℕ) (x_1 : ℕ),   Denumerable.raise
' x x_1 =     match x, x_1 with     | [], x => []     | m :: l, n => (m + n) :: 
Denumerable.rai…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isChain_cons_raise'_of_lt (l) {m n} (h : m < n) :
    List.IsChain (· < ·) (m :: raise' l n) := by
  unfold raise'; cases l with grind [isChain_cons_raise']

/-- `raise' l n` is a strictly increasing sequence. -/
/-
**Denumerable.raise'_sorted** 是 Mathlib 中的一个定理，位于命名空间 `Denumerable`。
形式化陈述：∀ (l : List ℕ) (n : ℕ), (Denumerable.raise' l n).SortedLT
参数：l : List ℕ；n : ℕ；Denumerable.raise' l n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.sortedLT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α]
, List.IsChain (fun x1 x2 => x1 < x2) l → l.SortedLT
· 使用定理 `Denumerable.raise'`：raise'_sorted (l n) : List.SortedLT (raise' l n)
· 使用定理 `Denumerable.isChain_raise'`：∀ (l : List ℕ) (n : ℕ), List.IsChain (fun x1
 x2 => x1 < x2) (Denumerable.raise' l n)

--- 原说明 ---
`raise' l n` is a strictly increasing sequence.
-/
theorem raise'_sorted (l n) : List.SortedLT (raise' l n) := (isChain_raise' _ _).sortedLT

/-- Makes `raise' l n` into a finset. Elements are distinct thanks to `raise'_sorted`. -/
/-
**Denumerable.raise'Finset** 是 Mathlib 中的一个定义，位于命名空间 `Denumerable`。
形式化陈述：List ℕ → ℕ → Finset ℕ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Denumerable.raise'`：raise'_sorted (l n) : List.SortedLT (raise' l n)

--- 原说明 ---
Makes `raise' l n` into a finset. Elements are distinct thanks to `raise'_sorted
`.
-/
def raise'Finset (l : List ℕ) (n : ℕ) : Finset ℕ :=
  ⟨raise' l n, (raise'_sorted _ _).nodup⟩

/-- If `α` is denumerable, then so is `Finset α`. Warning: this is *not* the same encoding as used
in `Finset.encodable`. -/
/-
**Denumerable.finset** 是 Mathlib 中的一个实例，位于命名空间 `Denumerable`。
形式化陈述：finset : Denumerable (Finset α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `α` is denumerable, then so is `Finset α`. Warning: this is *not* the same en
coding as used
in `Finset.encodable`.
-/
instance finset : Denumerable (Finset α) :=
  mk'
    ⟨fun s : Finset α => encode <| lower' (s.map (eqv α).toEmbedding).sort 0, fun n =>
      Finset.map (eqv α).symm.toEmbedding (raise'Finset (ofNat (List ℕ) n) 0), fun s =>
      Finset.eq_of_veq <| by
        simp [-Multiset.map_coe, raise'Finset,
          raise_lower' (fun n _ => Nat.zero_le n) (Finset.sortedLT_sort _)],
      fun n => by
      simp [-Multiset.map_coe, Finset.map, raise'Finset, Finset.sort,
        List.mergeSort_eq_self _ (raise'_sorted _ _).sortedLE.pairwise, lower_raise']⟩

end Denumerable

