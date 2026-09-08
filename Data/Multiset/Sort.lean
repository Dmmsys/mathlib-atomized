/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Sort
public import Mathlib.Data.Multiset.Range
public meta import Mathlib.Util.Qq
public meta import Mathlib.Data.Multiset.Defs

/-!
# Construct a sorted list from a multiset.
-/

@[expose] public section

variable {α β : Type*}

namespace Multiset

open List

section sort


/-- `sort s` constructs a sorted list from the multiset `s`.
  (Uses merge sort algorithm.) -/
/-
**Multiset.sort** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：sort (s : Multiset α) (r : α -> α -> Prop
参数：s : Multiset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sort s` constructs a sorted list from the multiset `s`.
  (Uses merge sort algorithm.)
-/
def sort (s : Multiset α) (r : α → α → Prop := by exact fun a b => a ≤ b)
    [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r] : List α :=
  Quot.liftOn s (mergeSort · (r · ·)) fun _ _ h =>
    ((mergeSort_perm _ _).trans <| h.trans (mergeSort_perm _ _).symm).eq_of_pairwise' (r := r)
      (pairwise_mergeSort' _ _) (pairwise_mergeSort' _ _)

section

variable (a : α) (f : α → β) (l : List α) (s : Multiset α)
variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]
variable (r' : β → β → Prop) [DecidableRel r'] [IsTrans β r'] [Std.Antisymm r'] [Std.Total r']

@[simp]
/-
**Multiset.coe_sort** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_sort : sort l r = mergeSort l (r · ·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sort : sort l r = mergeSort l (r · ·) :=
  rfl

@[simp]
/-
**Multiset.pairwise_sort** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pairwise_sort : (sort s r).Pairwise r
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.pairwise_mergeSort'`：pairwise_mergeSort' (l : List α) : Pairwise r 
(mergeSort l (r · ·))
-/
theorem pairwise_sort : (sort s r).Pairwise r :=
  Quot.inductionOn s (pairwise_mergeSort' _)

@[simp]
/-
**Multiset.sort_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sort_eq : ↑(sort s r) = s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.mergeSort_perm`：∀ {α : Type u_1} (l : List α) (le : α → α → Bool), 
(l.mergeSort le).Perm l
-/
theorem sort_eq : ↑(sort s r) = s :=
  Quot.inductionOn s fun _ => Quot.sound <| mergeSort_perm _ _

@[simp]
/-
**Multiset.sort_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sort_zero : sort 0 r = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mergeSort_nil`：∀ {α : Type u_1} {r : α → α → Bool}, [].mergeSort r 
= []
-/
theorem sort_zero : sort 0 r = [] :=
  List.mergeSort_nil

@[simp]
/-
**Multiset.sort_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sort_singleton : sort {a} r = [a]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mergeSort_singleton`：∀ {α : Type u_1} {r : α → α → Bool} (a : α), [
a].mergeSort r = [a]
-/
theorem sort_singleton : sort {a} r = [a] :=
  List.mergeSort_singleton a
/-
**Multiset.map_sort** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_sort (hs : forall a in s, forall b in s, r a b ↔ r' (f a) (f b)) : (s.
sort r).map f = (s.map f).sort r'
参数：hs : forall a in s, forall b in s, r a b ↔ r' (f a) (f b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.map_mergeSort`：∀ {α : Type u_2} {β : Type u_1} {r : α → α → Bool} {
s : β → β → Bool} {f : α → β} {l : List α},   (∀ a ∈ l, ∀ b ∈ l, r a b = s (f a)
 (f b)) …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem map_sort (hs : ∀ a ∈ s, ∀ b ∈ s, r a b ↔ r' (f a) (f b)) :
    (s.sort r).map f = (s.map f).sort r' := by
  revert s
  exact Quot.ind fun l h => map_mergeSort (l := l) (by simpa using h)
/-
**Multiset.sort_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sort_cons : (forall b in s, r a b) -> sort (a ::ₘ s) r = a :: sort s r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.mergeSort_eq_insertionSort`：mergeSort_eq_insertionSort (l : List α)
 : mergeSort l (r · ·) = insertionSort r l
· 使用定理 `List.insertionSort_cons`：∀ {α : Type u_1} (r : α → α → Prop) [inst : Dec
idableRel r] (a : α) (l : List α),   List.insertionSort r (a :: l) = List.ordere
dInsert r a (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.insertionSort_cons_of_forall_rel`：insertionSort_cons_of_forall_rel 
{a : α} {l : List α} (h : forall b in l, r a b) : insertionSort r (a :: l) = a :
: insertionSort r l
-/
theorem sort_cons : (∀ b ∈ s, r a b) → sort (a ::ₘ s) r = a :: sort s r := by
  refine Quot.inductionOn s fun l => ?_
  simpa [mergeSort_eq_insertionSort] using insertionSort_cons_of_forall_rel r (a := a) (l := l)

@[simp]
/-
**Multiset.sort_range** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sort_range (n : Nat) : sort (range n) = List.range n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mergeSort_eq_self`：mergeSort_eq_self {l : List α} : Pairwise r l ->
 mergeSort l (r · ·) = l
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Nat.instAntisymmLe`：Std.Antisymm fun x1 x2 => x1 ≤ x2
· 使用定理 `List.SortedLE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLE → List.Pairwise (fun x1 x2 => x1 ≤ x2) l
· 使用定理 `List.SortedLT.sortedLE`：∀ {α : Type u_1} [inst : Preorder α] {l : List α
}, l.SortedLT → l.SortedLE
· 使用定理 `List.sortedLT_range`：sortedLT_range (n : Nat) : (range n).SortedLT
-/
theorem sort_range (n : ℕ) : sort (range n) = List.range n :=
  List.mergeSort_eq_self _ (sortedLT_range n).sortedLE.pairwise

end

section

variable {a : α} {s : Multiset α}
variable (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r] [Std.Total r]

@[simp]
/-
**Multiset.mem_sort** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_sort : a in sort s r ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.mem_coe`：mem_coe {a : α} {l : List α} : a in (l : Multiset α) ↔
 a in l
· 使用定理 `Multiset.sort_eq`：sort_eq : ↑(sort s r) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sort : a ∈ sort s r ↔ a ∈ s := by rw [← mem_coe, sort_eq]

@[simp]
/-
**Multiset.length_sort** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：length_sort : (sort s r).length = card s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.length_mergeSort`：∀ {α : Type u_1} {le : α → α → Bool} (l : List α)
, (l.mergeSort le).length = l.length
-/
theorem length_sort : (sort s r).length = card s := Quot.inductionOn s <| length_mergeSort

end

end sort

open Qq in
universe u in
meta unsafe instance {α : Type u} [Lean.ToLevel.{u}] [Lean.ToExpr α] :
    Lean.ToExpr (Multiset α) :=
  haveI u' := Lean.toLevel.{u}
  haveI α' : Q(Type u') := Lean.toTypeExpr α
  { toTypeExpr := q(Multiset $α')
    toExpr s := show Q(Multiset $α') from
      if Multiset.card s = 0 then
        q(0)
      else
        mkSetLiteralQ (α := q($α')) q(Multiset $α') (s.unquot.map Lean.toExpr)}

-- TODO: use a sort order if available, gh-18166
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
unsafe instance [Repr α] : Repr (Multiset α) where
  reprPrec s _ :=
    if Multiset.card s = 0 then
      "0"
    else
      Std.Format.bracket "{" (Std.Format.joinSep (s.unquot.map repr) ("," ++ Std.Format.line)) "}"

end Multiset

