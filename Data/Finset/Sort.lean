/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Order.RelIso.Set

/-!
# Construct a sorted list from a finset.
-/

@[expose] public section

namespace Finset

open Multiset Nat

variable {α β : Type*}

/-! ### sort -/


section sort

/-- `sort s` constructs a sorted list from the unordered set `s`.
  (Uses merge sort algorithm.) -/
/-
**Finset.sort** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：sort (s : Finset α) (r : α -> α -> Prop
参数：s : Finset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sort s` constructs a sorted list from the unordered set `s`.
  (Uses merge sort algorithm.)
-/
def sort (s : Finset α) (r : α → α → Prop := by exact fun a b => a ≤ b)
    [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] : List α :=
  Multiset.sort s.1 r

section

variable (f : α ↪ β) (s : Finset α)
variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]
variable (r' : β → β → Prop) [DecidableRel r'] [IsTrans β r'] [Std.Antisymm r'] [Std.Total r']

@[simp]
/-
**Finset.sort_val** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_val : Multiset.sort s.val r = sort s r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sort_val : Multiset.sort s.val r = sort s r :=
  rfl

@[simp]
/-
**Finset.pairwise_sort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：pairwise_sort : List.Pairwise r (sort s r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.pairwise_sort`：pairwise_sort : (sort s r).Pairwise r
-/
theorem pairwise_sort : List.Pairwise r (sort s r) :=
  Multiset.pairwise_sort _ _

@[simp]
/-
**Finset.sort_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_eq : ↑(sort s r) = s.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sort_eq`：sort_eq : ↑(sort s r) = s
-/
theorem sort_eq : ↑(sort s r) = s.1 :=
  Multiset.sort_eq _ _

@[simp]
/-
**Finset.sort_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_nodup : (sort s r).Nodup
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sort_eq`：sort_eq : ↑(sort s r) = s.1
· 使用定理 `Finset.nodup`：∀ {α : Type u_4} (self : Finset α), self.val.Nodup
-/
theorem sort_nodup : (sort s r).Nodup :=
  (by rw [sort_eq]; exact s.2 : @Multiset.Nodup α (sort s r))

@[simp]
/-
**Finset.sort_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_toFinset [DecidableEq α] : (sort s r).toFinset = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sort_nodup`：sort_nodup : (sort s r).Nodup
· 使用定理 `Finset.eq_of_veq`：∀ {α : Type u_1} {s t : Finset α}, s.val = t.val → s =
 t
· 使用定理 `Finset.sort_eq`：sort_eq : ↑(sort s r) = s.1
· 使用定理 `List.toFinset_eq`：toFinset_eq (n : Nodup l) : @Finset.mk α l n = l.toFin
set
-/
theorem sort_toFinset [DecidableEq α] : (sort s r).toFinset = s :=
  List.toFinset_eq (s.sort_nodup r) ▸ eq_of_veq (s.sort_eq r)

@[simp]
/-
**Finset.sort_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_empty : sort ∅ r = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sort_zero`：sort_zero : sort 0 r = []
-/
theorem sort_empty : sort ∅ r = [] :=
  Multiset.sort_zero r

@[simp]
/-
**Finset.sort_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_singleton (a : α) : sort {a} r = [a]
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sort_singleton`：sort_singleton : sort {a} r = [a]
-/
theorem sort_singleton (a : α) : sort {a} r = [a] :=
  Multiset.sort_singleton a r
/-
**Finset.map_sort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_sort (hs : forall a in s, forall b in s, r a b ↔ r' (f a) (f b)) : (s.
sort r).map f = (s.map f).sort r'
参数：hs : forall a in s, forall b in s, r a b ↔ r' (f a) (f b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.map_sort`：map_sort (hs : forall a in s, forall b in s, r a b ↔ 
r' (f a) (f b)) : (s.sort r).map f = (s.map f).sort r'
-/
theorem map_sort
    (hs : ∀ a ∈ s, ∀ b ∈ s, r a b ↔ r' (f a) (f b)) :
    (s.sort r).map f = (s.map f).sort r' :=
  Multiset.map_sort _ _ _ _ hs
/-
**Finset._root_.StrictMonoOn.map_finsetSort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.StrictMonoOn.map_finsetSort [LinearOrder α] [LinearOrder β]
    (hf : StrictMonoOn f s) :
    s.sort.map f = (s.map f).sort :=
  Finset.map_sort _ _ _ _ fun _a ha _b hb => (hf.le_iff_le ha hb).symm

@[simp]
/-
**Finset.sort_range** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_range (n : Nat) : sort (range n) = List.range n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sort_range`：sort_range (n : Nat) : sort (range n) = List.range 
n
-/
theorem sort_range (n : ℕ) : sort (range n) = List.range n :=
  Multiset.sort_range n

open scoped List in
/-
**Finset.sort_perm_toList** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_perm_toList : sort s r ~ s.toList
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l
₂ ↔ l₁ ~ l₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sort_eq`：sort_eq : ↑(sort s r) = s.1
· 使用定理 `Finset.coe_toList`：coe_toList (s : Finset α) : (s.toList : Multiset α) =
 s.val
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sort_perm_toList : sort s r ~ s.toList := by
  rw [← Multiset.coe_eq_coe]
  simp only [coe_toList, sort_eq]
/-
**Finset._root_.List.toFinset_sort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.List.toFinset_sort [DecidableEq α] {l : List α} (hl : l.Nodup) :
    sort l.toFinset r = l ↔ l.Pairwise r := by
  refine ⟨?_, ((sort_perm_toList _ r).trans (List.toFinset_toList hl)).eq_of_pairwise'
    (pairwise_sort _ _)⟩
  intro h
  rw [← h]
  exact pairwise_sort _ r

end

section

variable {m : Multiset α} {s : Finset α}
variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

@[simp]
/-
**Finset.sort_mk** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_mk (h : m.Nodup) : sort ⟨m, h⟩ r = m.sort r
参数：h : m.Nodup。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sort_mk (h : m.Nodup) : sort ⟨m, h⟩ r = m.sort r := rfl

@[simp]
/-
**Finset.mem_sort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_sort {a : α} : a in sort s r ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.mem_sort`：mem_sort : a in sort s r ↔ a in s
-/
theorem mem_sort {a : α} : a ∈ sort s r ↔ a ∈ s :=
  Multiset.mem_sort _

@[simp]
/-
**Finset.length_sort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：length_sort : (sort s r).length = s.card
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.length_sort`：length_sort : (sort s r).length = card s
-/
theorem length_sort : (sort s r).length = s.card :=
  Multiset.length_sort _
/-
**Finset.sort_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_cons {a : α} (h₁ : forall b in s, r a b) (h₂ : a ∉ s) : sort (cons a 
s h₂) r = a :: sort s r
参数：h₁ : forall b in s, r a b；h₂ : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sort.eq_1`：∀ {α : Type u_1} (s : Finset α) (r : α → α → Prop) [in
st : DecidableRel r] [inst_1 : IsTrans α r]   [inst_2 : Std.Antisymm r] [inst_3 
: Std.…
· 使用定理 `Finset.cons_val`：cons_val (h : a ∉ s) : (cons a s h).1 = a ::ₘ s.1
· 使用定理 `Multiset.sort_cons`：sort_cons : (forall b in s, r a b) -> sort (a ::ₘ s)
 r = a :: sort s r
· 使用定理 `Finset.sort_val`：sort_val : Multiset.sort s.val r = sort s r
-/
theorem sort_cons {a : α} (h₁ : ∀ b ∈ s, r a b) (h₂ : a ∉ s) :
    sort (cons a s h₂) r = a :: sort s r := by
  rw [sort, cons_val, Multiset.sort_cons a _ r h₁, sort_val]
/-
**Finset.sort_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sort_insert [DecidableEq α] {a : α} (h₁ : forall b in s, r a b) (h₂ : a ∉ 
s) : sort (insert a s) r = a :: sort s r
参数：h₁ : forall b in s, r a b；h₂ : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.sort_cons`：sort_cons {a : α} (h₁ : forall b in s, r a b) (h₂ : a 
∉ s) : sort (cons a s h₂) r = a :: sort s r
-/
theorem sort_insert [DecidableEq α] {a : α} (h₁ : ∀ b ∈ s, r a b) (h₂ : a ∉ s) :
    sort (insert a s) r = a :: sort s r := by
  rw [← cons_eq_insert _ _ h₂, sort_cons r h₁]

end

end sort

section SortLinearOrder

variable [LinearOrder α]

/-
**Finset.sortedLT_sort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sortedLT_sort (s : Finset α) : (sort s).SortedLT
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedLE.sortedLT_of_nodup`：∀ {α : Type u_1} [inst : PartialOrder α
] {l : List α}, l.SortedLE → l.Nodup → l.SortedLT
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `List.Pairwise.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≤ x2) l → l.SortedLE
· 使用定理 `Finset.pairwise_sort`：pairwise_sort : List.Pairwise r (sort s r)
· 使用定理 `Finset.sort_nodup`：sort_nodup : (sort s r).Nodup
-/
theorem sortedLT_sort (s : Finset α) : (sort s).SortedLT :=
  (pairwise_sort _ _).sortedLE.sortedLT_of_nodup (sort_nodup _ _)
/-
**Finset.sortedGT_sort** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sortedGT_sort (s : Finset α) : (sort s (· >= ·)).SortedGT
参数：s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedGE.sortedGT_of_nodup`：∀ {α : Type u_1} [inst : PartialOrder α
] {l : List α}, l.SortedGE → l.Nodup → l.SortedGT
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `List.Pairwise.sortedGE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≥ x2) l → l.SortedGE
· 使用定理 `Finset.pairwise_sort`：pairwise_sort : List.Pairwise r (sort s r)
· 使用定理 `Finset.sort_nodup`：sort_nodup : (sort s r).Nodup
-/
theorem sortedGT_sort (s : Finset α) : (sort s (· ≥ ·)).SortedGT :=
  (pairwise_sort _ _).sortedGE.sortedGT_of_nodup (sort_nodup _ _)
/-
**Finset.sorted_zero_eq_min'_aux** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] (s : Finset α) (h : 0 < (s.sort fu
n a b => a ≤ b).length) (H : s.Nonempty),   (s.sort fun a b => a ≤ b).get ⟨0, h⟩
 = s.min' H
参数：s : Finset α；h : 0 < (s.sort fun a b => a ≤ b).length；H : s.Nonempty；s.sort f
un a b => a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sort`：mem_sort {a : α} : a in sort s r ↔ a in s
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_iff_get`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ ∃ n, l.
get n = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Pairwise.rel_get_of_le`：∀ {α : Type u_1} {R : α → α → Prop} [Std.Re
fl R] {l : List α},   List.Pairwise R l → ∀ {a b : Fin l.length}, a ≤ b → R (l.g
et a) (l.get b)
· 使用定理 `Finset.pairwise_sort`：pairwise_sort : List.Pairwise r (sort s r)
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
-/
theorem sorted_zero_eq_min'_aux (s : Finset α) (h : 0 < s.sort.length) (H : s.Nonempty) :
    s.sort.get ⟨0, h⟩ = s.min' H := by
  let l := s.sort
  apply le_antisymm
  · have : s.min' H ∈ l := (s.mem_sort (· ≤ ·)).mpr (s.min'_mem H)
    obtain ⟨i, hi⟩ : ∃ i, l.get i = s.min' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.pairwise_sort (· ≤ ·)).rel_get_of_le (Nat.zero_le i)
  · have : l.get ⟨0, h⟩ ∈ s := (Finset.mem_sort (α := α) (· ≤ ·)).1 (List.get_mem l _)
    exact s.min'_le _ this
/-
**Finset.sorted_zero_eq_min'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sorted_zero_eq_min'_aux (s : Finset α) (h : 0 < s.sort.length) (H : s.None
mpty) : s.sort.get ⟨0, h⟩ = s.min' H
参数：s : Finset α；h : 0 < s.sort.length；H : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Finset.sorted_zero_eq_min'_aux`：∀ {α : Type u_1} [inst : LinearOrder α] 
(s : Finset α) (h : 0 < (s.sort fun a b => a ≤ b).length) (H : s.Nonempty),   (s
.sort fun a b => a ≤…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
-/
theorem sorted_zero_eq_min' {s : Finset α} {h : 0 < s.sort.length} :
    s.sort[0] = s.min' (card_pos.1 <| by rwa [length_sort] at h) :=
  sorted_zero_eq_min'_aux _ _ _
/-
**Finset.min'_eq_sorted_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {s : Finset α} {h : s.Nonempty}, s
.min' h = (s.sort fun a b => a ≤ b)[0]
参数：s.sort fun a b => a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Finset.sorted_zero_eq_min'_aux`：∀ {α : Type u_1} [inst : LinearOrder α] 
(s : Finset α) (h : 0 < (s.sort fun a b => a ≤ b).length) (H : s.Nonempty),   (s
.sort fun a b => a ≤…
-/
theorem min'_eq_sorted_zero {s : Finset α} {h : s.Nonempty} :
    s.min' h = s.sort[0]'(by rw [length_sort]; exact card_pos.2 h) :=
  (sorted_zero_eq_min'_aux _ _ _).symm
/-
**Finset.sorted_last_eq_max'_aux** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] (s : Finset α)   (h : (s.sort fun 
a b => a ≤ b).length - 1 < (s.sort fun a b => a ≤ b).length) (H : s.Nonempty),  
 (s.sort fun a b => a ≤ b)[(s.sort fun a b => a ≤ b).length - 1] = s.max' H
参数：s : Finset α；h : (s.sort fun a b => a ≤ b).length - 1 < (s.sort fun a b => a 
≤ b).length；H : s.Nonempty；s.sort fun a b => a ≤ b；s.sort fun a b => a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_sort`：mem_sort {a : α} : a in sort s r ↔ a in s
· 使用定理 `List.get_mem`：∀ {α : Type u_1} (l : List α) (n : Fin l.length), l.get n 
∈ l
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `List.mem_iff_get`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ ∃ n, l.
get n = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Pairwise.rel_get_of_le`：∀ {α : Type u_1} {R : α → α → Prop} [Std.Re
fl R] {l : List α},   List.Pairwise R l → ∀ {a b : Fin l.length}, a ≤ b → R (l.g
et a) (l.get b)
· 使用定理 `Finset.pairwise_sort`：pairwise_sort : List.Pairwise r (sort s r)
· 使用定理 `Nat.le_sub_one_of_lt`：∀ {a b : ℕ}, a < b → a ≤ b - 1
· 使用定理 `Fin.prop`：∀ {n : ℕ} (a : Fin n), ↑a < n
-/
theorem sorted_last_eq_max'_aux (s : Finset α)
    (h : s.sort.length - 1 < s.sort.length) (H : s.Nonempty) :
    s.sort[s.sort.length - 1] = s.max' H := by
  let l := s.sort
  apply le_antisymm
  · have : l.get ⟨s.sort.length - 1, h⟩ ∈ s :=
      (s.mem_sort (· ≤ ·)).1 (List.get_mem l _)
    exact s.le_max' _ this
  · have : s.max' H ∈ l := (s.mem_sort (· ≤ ·)).mpr (s.max'_mem H)
    obtain ⟨i, hi⟩ : ∃ i, l.get i = s.max' H := List.mem_iff_get.1 this
    rw [← hi]
    exact (s.pairwise_sort (· ≤ ·)).rel_get_of_le (Nat.le_sub_one_of_lt i.prop)
/-
**Finset.sorted_last_eq_max'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sorted_last_eq_max'_aux (s : Finset α) (h : s.sort.length - 1 < s.sort.len
gth) (H : s.Nonempty) : s.sort[s.sort.length - 1] = s.max' H
参数：s : Finset α；h : s.sort.length - 1 < s.sort.length；H : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Finset.sorted_last_eq_max'_aux`：∀ {α : Type u_1} [inst : LinearOrder α] 
(s : Finset α)   (h : (s.sort fun a b => a ≤ b).length - 1 < (s.sort fun a b => 
a ≤ b).length) (H : …
-/
theorem sorted_last_eq_max' {s : Finset α}
    {h : s.sort.length - 1 < s.sort.length} :
    s.sort[s.sort.length - 1] =
      s.max' (by rw [length_sort] at h; exact card_pos.1 (lt_of_le_of_lt bot_le h)) :=
  sorted_last_eq_max'_aux _ h _
/-
**Finset.max'_eq_sorted_last** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {s : Finset α} {h : s.Nonempty},  
 s.max' h = (s.sort fun a b => a ≤ b)[(s.sort fun a b => a ≤ b).length - 1]
参数：s.sort fun a b => a ≤ b；s.sort fun a b => a ≤ b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.length_sort`：length_sort : (sort s r).length = s.card
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Nat.zero_lt_one`：0 < 1
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Finset.sorted_last_eq_max'_aux`：∀ {α : Type u_1} [inst : LinearOrder α] 
(s : Finset α)   (h : (s.sort fun a b => a ≤ b).length - 1 < (s.sort fun a b => 
a ≤ b).length) (H : …
-/
theorem max'_eq_sorted_last {s : Finset α} {h : s.Nonempty} :
    s.max' h =
      s.sort[s.sort.length - 1]'
        (by simpa using Nat.sub_lt (card_pos.mpr h) Nat.zero_lt_one) :=
  (sorted_last_eq_max'_aux _ (by simpa using Nat.sub_lt (card_pos.mpr h) Nat.zero_lt_one) _).symm

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderIsoOfFin s h`
is the increasing bijection between `Fin k` and `s` as an `OrderIso`. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of an iso `Fin s.card ≃o s` to avoid
casting issues in further uses of this function. -/
/-
**Finset.orderIsoOfFin** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：orderIsoOfFin (s : Finset α) {k : Nat} (h : s.card = k) : Fin k ≃o s
参数：s : Finset α；h : s.card = k。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sortedLT_sort`：sortedLT_sort (s : Finset α) : (sort s).SortedLT

--- 原说明 ---
Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderIsoOf
Fin s h`
is the increasing bijection between `Fin k` and `s` as an `OrderIso`. Here, `h` 
is a proof that
the cardinality of `s` is `k`. We use this instead of an iso `Fin s.card ≃o s` t
o avoid
casting issues in further uses of this function.
-/
def orderIsoOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ≃o s :=
  OrderIso.trans (Fin.castOrderIso ((s.length_sort (· ≤ ·)).trans h).symm) <|
    (s.sortedLT_sort.getIso _).trans <| OrderIso.setCongr {x | x ∈ s.sort (· ≤ ·)} _ <| by simp

/-- Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderEmbOfFin s h` is
the increasing bijection between `Fin k` and `s` as an order embedding into `α`. Here, `h` is a
proof that the cardinality of `s` is `k`. We use this instead of an embedding `Fin s.card ↪o α` to
avoid casting issues in further uses of this function. -/
/-
**Finset.orderEmbOfFin** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin (s : Finset α) {k : Nat} (h : s.card = k) : Fin k ↪o α
参数：s : Finset α；h : s.card = k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finset `s` of cardinality `k` in a linear order `α`, the map `orderEmbOf
Fin s h` is
the increasing bijection between `Fin k` and `s` as an order embedding into `α`.
 Here, `h` is a
proof that the cardinality of `s` is `k`. We use this instead of an embedding `F
in s.card ↪o α` to
avoid casting issues in further uses of this function.
-/
def orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) : Fin k ↪o α :=
  (orderIsoOfFin s h).toOrderEmbedding.trans (OrderEmbedding.subtype _)

@[simp]
/-
**Finset.coe_orderIsoOfFin_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_orderIsoOfFin_apply (s : Finset α) {k : Nat} (h : s.card = k) (i : Fin
 k) : ↑(orderIsoOfFin s h i) = orderEmbOfFin s h i
参数：s : Finset α；h : s.card = k；i : Fin k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_orderIsoOfFin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    ↑(orderIsoOfFin s h i) = orderEmbOfFin s h i :=
  rfl
/-
**Finset.orderIsoOfFin_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：orderIsoOfFin_symm_apply (s : Finset α) {k : Nat} (h : s.card = k) (x : s)
 : ↑((s.orderIsoOfFin h).symm x) = s.sort.idxOf ↑x
参数：s : Finset α；h : s.card = k；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoOfFin_symm_apply (s : Finset α) {k : ℕ} (h : s.card = k) (x : s) :
    ↑((s.orderIsoOfFin h).symm x) = s.sort.idxOf ↑x :=
  rfl
/-
**Finset.orderEmbOfFin_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_apply (s : Finset α) {k : Nat} (h : s.card = k) (i : Fin k) 
: s.orderEmbOfFin h i = s.sort[i]'(by rw [length_sort, h]; exact i.2)
参数：s : Finset α；h : s.card = k；i : Fin k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderEmbOfFin_apply (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i = s.sort[i]'(by rw [length_sort, h]; exact i.2) :=
  rfl

@[simp]
/-
**Finset.orderEmbOfFin_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_mem (s : Finset α) {k : Nat} (h : s.card = k) (i : Fin k) : 
s.orderEmbOfFin h i in s
参数：s : Finset α；h : s.card = k；i : Fin k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem orderEmbOfFin_mem (s : Finset α) {k : ℕ} (h : s.card = k) (i : Fin k) :
    s.orderEmbOfFin h i ∈ s :=
  (s.orderIsoOfFin h i).2

@[simp]
/-
**Finset.range_orderEmbOfFin** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：range_orderEmbOfFin (s : Finset α) {k : Nat} (h : s.card = k) : Set.range 
(s.orderEmbOfFin h) = s
参数：s : Finset α；h : s.card = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `RelIso.range_eq`：range_eq (e : r ≃r s) : Set.range e = Set.univ
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_orderEmbOfFin (s : Finset α) {k : ℕ} (h : s.card = k) :
    Set.range (s.orderEmbOfFin h) = s := by
  simp only [orderEmbOfFin, Set.range_comp ((↑) : _ → α) (s.orderIsoOfFin h),
  RelEmbedding.coe_trans, Set.image_univ, Finset.orderEmbOfFin, RelIso.range_eq,
    OrderEmbedding.coe_subtype, OrderIso.coe_toOrderEmbedding,
    Subtype.range_coe_subtype, Finset.setOfPred_mem]

@[simp]
/-
**Finset.image_orderEmbOfFin_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：image_orderEmbOfFin_univ (s : Finset α) {k : Nat} (h : s.card = k) : Finse
t.image (s.orderEmbOfFin h) Finset.univ = s
参数：s : Finset α；h : s.card = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_injective`：coe_injective {α} : Injective ((↑) : Finset α -> S
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finset.range_orderEmbOfFin`：range_orderEmbOfFin (s : Finset α) {k : Nat}
 (h : s.card = k) : Set.range (s.orderEmbOfFin h) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem image_orderEmbOfFin_univ (s : Finset α) {k : ℕ} (h : s.card = k) :
    Finset.image (s.orderEmbOfFin h) Finset.univ = s := by
  apply Finset.coe_injective
  simp

@[simp]
/-
**Finset.map_orderEmbOfFin_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：map_orderEmbOfFin_univ (s : Finset α) {k : Nat} (h : s.card = k) : Finset.
map (s.orderEmbOfFin h).toEmbedding Finset.univ = s
参数：s : Finset α；h : s.card = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.map_eq_image`：map_eq_image (f : α ↪ β) (s : Finset α) : s.map f =
 s.image f
· 使用定理 `Finset.image_orderEmbOfFin_univ`：image_orderEmbOfFin_univ (s : Finset α)
 {k : Nat} (h : s.card = k) : Finset.image (s.orderEmbOfFin h) Finset.univ = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_orderEmbOfFin_univ (s : Finset α) {k : ℕ} (h : s.card = k) :
    Finset.map (s.orderEmbOfFin h).toEmbedding Finset.univ = s := by
  simp [map_eq_image]

@[simp]
/-
**Finset.listMap_orderEmbOfFin_finRange** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：listMap_orderEmbOfFin_finRange (s : Finset α) {k : Nat} (h : s.card = k) :
 (List.finRange k).map (s.orderEmbOfFin h) = s.sort
参数：s : Finset α；h : s.card = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `List.map_getElem_finRange`：∀ {α : Type u_1} (l : List α), List.map (fun 
x => l[↑x]) (List.finRange l.length) = l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.length_sort`：length_sort : (sort s r).length = s.card
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem listMap_orderEmbOfFin_finRange (s : Finset α) {k : ℕ} (h : s.card = k) :
    (List.finRange k).map (s.orderEmbOfFin h) = s.sort := by
  obtain rfl : k = s.sort.length := by simp [h]
  exact List.map_getElem_finRange s.sort

/-- The bijection `orderEmbOfFin s h` sends `0` to the minimum of `s`. -/
/-
**Finset.orderEmbOfFin_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_zero {s : Finset α} {k : Nat} (h : s.card = k) (hz : 0 < k) 
: orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (h.symm ▸ hz))
参数：h : s.card = k；hz : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sorted_zero_eq_min'`：sorted_zero_eq_min'_aux (s : Finset α) (h : 
0 < s.sort.length) (H : s.Nonempty) : s.sort.get ⟨0, h⟩ = s.min' H
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The bijection `orderEmbOfFin s h` sends `0` to the minimum of `s`.
-/
theorem orderEmbOfFin_zero {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (h.symm ▸ hz)) := by
  simp only [orderEmbOfFin_apply, Fin.getElem_fin, sorted_zero_eq_min']

/-- The bijection `orderEmbOfFin s h` sends `k-1` to the maximum of `s`. -/
/-
**Finset.orderEmbOfFin_last** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_last {s : Finset α} {k : Nat} (h : s.card = k) (hz : 0 < k) 
: orderEmbOfFin s h ⟨k - 1, Nat.sub_lt hz (Nat.succ_pos 0)⟩ = s.max' (card_pos.m
p (h.symm ▸ hz))
参数：h : s.card = k；hz : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.sub_lt`：∀ {n m : ℕ}, 0 < n → 0 < m → n - m < n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.length_sort`：length_sort : (sort s r).length = s.card
· 使用定理 `Finset.max'_eq_sorted_last`：∀ {α : Type u_1} [inst : LinearOrder α] {s :
 Finset α} {h : s.Nonempty},   s.max' h = (s.sort fun a b => a ≤ b)[(s.sort fun 
a b => a ≤ b).le…
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The bijection `orderEmbOfFin s h` sends `k-1` to the maximum of `s`.
-/
theorem orderEmbOfFin_last {s : Finset α} {k : ℕ} (h : s.card = k) (hz : 0 < k) :
    orderEmbOfFin s h ⟨k - 1, Nat.sub_lt hz (Nat.succ_pos 0)⟩ =
      s.max' (card_pos.mp (h.symm ▸ hz)) := by
  simp [orderEmbOfFin_apply, max'_eq_sorted_last, h]

/-- `orderEmbOfFin {a} h` sends any argument to `a`. -/
@[simp]
/-
**Finset.orderEmbOfFin_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_singleton (a : α) (i : Fin 1) : orderEmbOfFin {a} (card_sing
leton a) i = a
参数：a : α；i : Fin 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Nat.zero_lt_one`：0 < 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.orderEmbOfFin_zero`：orderEmbOfFin_zero {s : Finset α} {k : Nat} (
h : s.card = k) (hz : 0 < k) : orderEmbOfFin s h ⟨0, hz⟩ = s.min' (card_pos.mp (
h.symm ▸ hz))
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `Finset.min'_singleton`：∀ {α : Type u_2} [inst : LinearOrder α] (a : α), 
{a}.min' ⋯ = a

--- 原说明 ---
`orderEmbOfFin {a} h` sends any argument to `a`.
-/
theorem orderEmbOfFin_singleton (a : α) (i : Fin 1) :
    orderEmbOfFin {a} (card_singleton a) i = a := by
  rw [Subsingleton.elim i ⟨0, Nat.zero_lt_one⟩, orderEmbOfFin_zero _ Nat.zero_lt_one,
    min'_singleton]

/-- Any increasing map `f` from `Fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `orderEmbOfFin s h`. -/
/-
**Finset.orderEmbOfFin_unique** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_unique {s : Finset α} {k : Nat} (h : s.card = k) {f : Fin k 
-> α} (hfs : forall x, f x in s) (hmono : StrictMono f) : f = s.orderEmbOfFin h
参数：h : s.card = k；hfs : forall x, f x in s；hmono : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StrictMono.range_inj`：StrictMono.range_inj [WellFoundedLT β] {f g : β ->
 γ} (hf : StrictMono f) (hg : StrictMono g) : Set.range f = Set.range g ↔ f = g
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `Fin.Lt.isWellOrder`：∀ (n : ℕ), IsWellOrder (Fin n) fun x1 x2 => x1 < x2
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
· 使用定理 `Finset.range_orderEmbOfFin`：range_orderEmbOfFin (s : Finset α) {k : Nat}
 (h : s.card = k) : Set.range (s.orderEmbOfFin h) = s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.card_image_of_injective`：card_image_of_injective [DecidableEq β] 
(s : Finset α) (H : Injective f) : #(s.image f) = #s
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Any increasing map `f` from `Fin k` to a finset of cardinality `k` has to coinci
de with
the increasing bijection `orderEmbOfFin s h`.
-/
theorem orderEmbOfFin_unique {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k → α}
    (hfs : ∀ x, f x ∈ s) (hmono : StrictMono f) : f = s.orderEmbOfFin h := by
  rw [← hmono.range_inj (s.orderEmbOfFin h).strictMono, range_orderEmbOfFin, ← Set.image_univ,
    ← coe_univ, ← coe_image, coe_inj]
  refine eq_of_subset_of_card_le (fun x hx => ?_) ?_
  · rcases mem_image.1 hx with ⟨x, _, rfl⟩
    exact hfs x
  · rw [h, card_image_of_injective _ hmono.injective, card_univ, Fintype.card_fin]

/-- An order embedding `f` from `Fin k` to a finset of cardinality `k` has to coincide with
the increasing bijection `orderEmbOfFin s h`. -/
/-
**Finset.orderEmbOfFin_unique'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_unique' {s : Finset α} {k : Nat} (h : s.card = k) {f : Fin k
 ↪o α} (hfs : forall x, f x in s) : f = s.orderEmbOfFin h
参数：h : s.card = k；hfs : forall x, f x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `Finset.orderEmbOfFin_unique`：orderEmbOfFin_unique {s : Finset α} {k : Na
t} (h : s.card = k) {f : Fin k -> α} (hfs : forall x, f x in s) (hmono : StrictM
ono f) : f = s.or…
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f

--- 原说明 ---
An order embedding `f` from `Fin k` to a finset of cardinality `k` has to coinci
de with
the increasing bijection `orderEmbOfFin s h`.
-/
theorem orderEmbOfFin_unique' {s : Finset α} {k : ℕ} (h : s.card = k) {f : Fin k ↪o α}
    (hfs : ∀ x, f x ∈ s) : f = s.orderEmbOfFin h :=
  RelEmbedding.ext <| funext_iff.1 <| orderEmbOfFin_unique h hfs f.strictMono

/-- Two parametrizations `orderEmbOfFin` of the same set take the same value on `i` and `j` if
and only if `i = j`. Since they can be defined on a priori not defeq types `Fin k` and `Fin l`
(although necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j : ℕ)`. -/
@[simp]
/-
**Finset.orderEmbOfFin_eq_orderEmbOfFin_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_eq_orderEmbOfFin_iff {k l : Nat} {s : Finset α} {i : Fin k} 
{j : Fin l} {h : s.card = k} {h' : s.card = l} : s.orderEmbOfFin h i = s.orderEm
bOfFin h' j ↔ (i : Nat) = (j : Nat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `OrderEmbedding.eq_iff_eq`：eq_iff_eq {a b} : f a = f b ↔ a = b
· 使用定理 `Fin.ext_iff`：∀ {n : ℕ} {a b : Fin n}, a = b ↔ ↑a = ↑b

--- 原说明 ---
Two parametrizations `orderEmbOfFin` of the same set take the same value on `i` 
and `j` if
and only if `i = j`. Since they can be defined on a priori not defeq types `Fin 
k` and `Fin l`
(although necessarily `k = l`), the conclusion is rather written `(i : ℕ) = (j :
 ℕ)`.
-/
theorem orderEmbOfFin_eq_orderEmbOfFin_iff {k l : ℕ} {s : Finset α} {i : Fin k} {j : Fin l}
    {h : s.card = k} {h' : s.card = l} :
    s.orderEmbOfFin h i = s.orderEmbOfFin h' j ↔ (i : ℕ) = (j : ℕ) := by
  subst k l
  exact (s.orderEmbOfFin rfl).eq_iff_eq.trans Fin.ext_iff

/-- Given a finset `s` of size at least `k` in a linear order `α`, the map `orderEmbOfCardLe`
is an order embedding from `Fin k` to `α` whose image is contained in `s`. Specifically, it maps
`Fin k` to an initial segment of `s`. -/
/-
**Finset.orderEmbOfCardLe** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：orderEmbOfCardLe (s : Finset α) {k : Nat} (h : k <= s.card) : Fin k ↪o α
参数：s : Finset α；h : k <= s.card。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finset `s` of size at least `k` in a linear order `α`, the map `orderEmb
OfCardLe`
is an order embedding from `Fin k` to `α` whose image is contained in `s`. Speci
fically, it maps
`Fin k` to an initial segment of `s`.
-/
def orderEmbOfCardLe (s : Finset α) {k : ℕ} (h : k ≤ s.card) : Fin k ↪o α :=
  (Fin.castLEOrderEmb h).trans (s.orderEmbOfFin rfl)
/-
**Finset.orderEmbOfCardLe_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfCardLe_mem (s : Finset α) {k : Nat} (h : k <= s.card) (a) : orde
rEmbOfCardLe s h a in s
参数：s : Finset α；h : k <= s.card；a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem orderEmbOfCardLe_mem (s : Finset α) {k : ℕ} (h : k ≤ s.card) (a) :
    orderEmbOfCardLe s h a ∈ s := by
  simp only [orderEmbOfCardLe, RelEmbedding.coe_trans, Finset.orderEmbOfFin_mem,
    Function.comp_apply]
/-
**Finset.orderEmbOfFin_compl_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_compl_singleton {n : Nat} {i : Fin (n + 1)} {k : Nat} (h : (
{i}ᶜ : Finset _).card = k) : ({i}ᶜ : Finset _).orderEmbOfFin h = (Fin.castOrderI
so <| by simp_all [card_compl]).toOrderEmbedding.trans (Fin.succAboveOrderEmb i)
参数：n + 1；h : ({i}ᶜ : Finset _).card = k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.orderEmbOfFin_unique`：orderEmbOfFin_unique {s : Finset α} {k : Na
t} (h : s.card = k) {f : Fin k -> α} (hfs : forall x, f x in s) (hmono : StrictM
ono f) : f = s.or…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用引理 `Fin.strictMono_succAbove`：strictMono_succAbove (p : Fin (n + 1)) : Stric
tMono (succAbove p)
· 使用引理 `Fin.cast_strictMono`：cast_strictMono {k l : Nat} (h : k = l) : StrictMon
o (Fin.cast h)
-/
lemma orderEmbOfFin_compl_singleton {n : ℕ} {i : Fin (n + 1)} {k : ℕ}
    (h : ({i}ᶜ : Finset _).card = k) :
    ({i}ᶜ : Finset _).orderEmbOfFin h =
      (Fin.castOrderIso <| by simp_all [card_compl]).toOrderEmbedding.trans
        (Fin.succAboveOrderEmb i) := by
  apply DFunLike.coe_injective
  rw [eq_comm]
  convert!
    orderEmbOfFin_unique _ (fun x ↦ ?_) ((Fin.strictMono_succAbove _).comp (Fin.cast_strictMono _))
  · simp
  · simp [← h, card_compl]

@[simp]
/-
**Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb** 是 Mathlib 中的一个引理，位
于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb {n : Nat} (i : Fin (n +
 1)) : ({i}ᶜ : Finset _).orderEmbOfFin (by simp [card_compl]) = Fin.succAboveOrd
erEmb i
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.orderEmbOfFin_compl_singleton`：orderEmbOfFin_compl_singleton {n :
 Nat} {i : Fin (n + 1)} {k : Nat} (h : ({i}ᶜ : Finset _).card = k) : ({i}ᶜ : Fin
set _).orderEmbOfFin h = (…
-/
lemma orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb {n : ℕ} (i : Fin (n + 1)) :
    ({i}ᶜ : Finset _).orderEmbOfFin (by simp [card_compl]) = Fin.succAboveOrderEmb i :=
  orderEmbOfFin_compl_singleton _
/-
**Finset.orderEmbOfFin_compl_singleton_apply** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：orderEmbOfFin_compl_singleton_apply {n : Nat} {i : Fin (n + 1)} {k : Nat} 
(h : ({i}ᶜ : Finset _).card = k) (j : Fin k) : ({i}ᶜ : Finset _).orderEmbOfFin h
 j = Fin.succAbove i (Fin.cast (h.symm.trans (by simp [card_compl])) j)
参数：n + 1；h : ({i}ᶜ : Finset _).card = k；j : Fin k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.orderEmbOfFin_compl_singleton`：orderEmbOfFin_compl_singleton {n :
 Nat} {i : Fin (n + 1)} {k : Nat} (h : ({i}ᶜ : Finset _).card = k) : ({i}ᶜ : Fin
set _).orderEmbOfFin h = (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.castOrderIso_apply`：∀ {m n : ℕ} (eq : n = m) (i : Fin n), (Fin.castO
rderIso eq) i = Fin.cast eq i
· 使用定理 `Fin.succAboveOrderEmb_apply`：∀ {n : ℕ} (p : Fin (n + 1)) (i : Fin n), p.
succAboveOrderEmb i = p.succAbove i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma orderEmbOfFin_compl_singleton_apply {n : ℕ} {i : Fin (n + 1)} {k : ℕ}
    (h : ({i}ᶜ : Finset _).card = k) (j : Fin k) : ({i}ᶜ : Finset _).orderEmbOfFin h j =
      Fin.succAbove i (Fin.cast (h.symm.trans (by simp [card_compl])) j) := by
  rw [orderEmbOfFin_compl_singleton]
  simp

end SortLinearOrder

/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe instance [Repr α] : Repr (Finset α) where
  reprPrec s _ :=
    -- multiset uses `0` not `∅` for empty sets
    if s.card = 0 then "∅" else repr s.1

end Finset

namespace Fin

/-
**Fin.sort_univ** 是 Mathlib 中的一个定理，位于命名空间 `Fin`。
形式化陈述：sort_univ (n : Nat) : Finset.univ.sort (fun x y : Fin n => x <= y) = List.
finRange n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedLT.eq_of_mem_iff`：∀ {α : Type u_1} [inst : PartialOrder α] {l
₁ l₂ : List α},   l₁.SortedLT → l₂.SortedLT → (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁ 
= l₂
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Finset.sortedLT_sort`：sortedLT_sort (s : Finset α) : (sort s).SortedLT
· 使用定理 `List.sortedLT_finRange`：sortedLT_finRange (n : Nat) : (finRange n).Sorte
dLT
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sort_univ (n : ℕ) : Finset.univ.sort (fun x y : Fin n => x ≤ y) = List.finRange n :=
  Finset.univ.sortedLT_sort.eq_of_mem_iff (List.sortedLT_finRange n) (by simp)

end Fin

/-- Given a `Fintype` `α` of cardinality `k`, the map `orderIsoFinOfCardEq s h` is the increasing
bijection between `Fin k` and `α` as an `OrderIso`. Here, `h` is a proof that the cardinality of `α`
is `k`. We use this instead of an iso `Fin (Fintype.card α) ≃o α` to avoid casting issues in further
uses of this function. -/
/-
**Fintype.orderIsoFinOfCardEq** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fintype.orderIsoFinOfCardEq (α : Type*) [LinearOrder α] [Fintype α] {k : N
at} (h : Fintype.card α = k) : Fin k ≃o α
参数：α : Type*；h : Fintype.card α = k。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)

--- 原说明 ---
Given a `Fintype` `α` of cardinality `k`, the map `orderIsoFinOfCardEq s h` is t
he increasing
bijection between `Fin k` and `α` as an `OrderIso`. Here, `h` is a proof that th
e cardinality of `α`
is `k`. We use this instead of an iso `Fin (Fintype.card α) ≃o α` to avoid casti
ng issues in further
uses of this function.
-/
def Fintype.orderIsoFinOfCardEq
    (α : Type*) [LinearOrder α] [Fintype α] {k : ℕ} (h : Fintype.card α = k) :
    Fin k ≃o α :=
  (Finset.univ.orderIsoOfFin h).trans
    ((OrderIso.setCongr _ _ Finset.coe_univ).trans OrderIso.Set.univ)

/-- Any finite linear order order-embeds into any infinite linear order. -/
/-
**nonempty_orderEmbedding_of_finite_infinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nonempty_orderEmbedding_of_finite_infinite (α : Type*) [LinearOrder α] [hα
 : Finite α] (β : Type*) [LinearOrder β] [hβ : Infinite β] : Nonempty (α ↪o β)
参数：α : Type*；β : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.exists_subset_card_eq`：exists_subset_card_eq (α : Type*) [Infin
ite α] (n : Nat) : exists s : Finset α, #s = n

--- 原说明 ---
Any finite linear order order-embeds into any infinite linear order.
-/
lemma nonempty_orderEmbedding_of_finite_infinite
    (α : Type*) [LinearOrder α] [hα : Finite α]
    (β : Type*) [LinearOrder β] [hβ : Infinite β] : Nonempty (α ↪o β) := by
  have := Fintype.ofFinite α
  obtain ⟨s, hs⟩ := Infinite.exists_subset_card_eq β (Fintype.card α)
  exact ⟨((Fintype.orderIsoFinOfCardEq α rfl).symm.toOrderEmbedding).trans (s.orderEmbOfFin hs)⟩
