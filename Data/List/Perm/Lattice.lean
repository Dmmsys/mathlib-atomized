/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.Lattice
public import Mathlib.Data.List.Nodup

/-!
# List Permutations and list lattice operations.

This file develops theory about the `List.Perm` relation and the lattice structure on lists.
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid

open Nat

namespace List
variable {α : Type*}

open Perm (swap)

variable [DecidableEq α]

/-
**List.Perm.bagInter_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {l₁ l₂ : List α} (t : List α), l₁.
Perm l₂ → (l₁.bagInter t).Perm (l₂.bagInter t)
参数：t : List α；l₁.bagInter t；l₂.bagInter t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Perm.bagInter_right {l₁ l₂ : List α} (t : List α) (h : l₁ ~ l₂) :
    l₁.bagInter t ~ l₂.bagInter t := by
  induction h generalizing t with grind
/-
**List.Perm.bagInter_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) {t₁ t₂ : List α}, t₁.
Perm t₂ → l.bagInter t₁ = l.bagInter t₂
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nil_bagInter`：nil_bagInter (l : List α) : [].bagInter l = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.cons_bagInter_of_mem`：cons_bagInter_of_mem (l₁ : List α) (h : a in 
l₂) : (a :: l₁).bagInter l₂ = a :: l₁.bagInter (l₂.erase a)
· 使用定理 `List.Perm.erase`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a : α) {
l₁ l₂ : List α}, l₁.Perm l₂ → (l₁.erase a).Perm (l₂.erase a)
· 使用定理 `List.Perm.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁ ⊆ l
₂
· 使用定理 `List.cons_bagInter_of_not_mem`：cons_bagInter_of_not_mem (l₁ : List α) (h
 : a ∉ l₂) : (a :: l₁).bagInter l₂ = l₁.bagInter l₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
-/
theorem Perm.bagInter_left (l : List α) {t₁ t₂ : List α} (p : t₁ ~ t₂) :
    l.bagInter t₁ = l.bagInter t₂ := by
  induction l generalizing t₁ t₂ p with | nil => simp | cons a l IH => ?_
  by_cases h : a ∈ t₁
  · simp [h, p.subset h, IH (p.erase _)]
  · simp [h, mt p.mem_iff.2 h, IH p]
/-
**List.Perm.bagInter** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {l₁ l₂ t₁ t₂ : List α},   l₁.Perm 
l₂ → t₁.Perm t₂ → (l₁.bagInter t₁).Perm (l₂.bagInter t₂)
参数：l₁.bagInter t₁；l₂.bagInter t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.bagInter_right`：∀ {α : Type u_1} [inst : DecidableEq α] {l₁ l₂
 : List α} (t : List α), l₁.Perm l₂ → (l₁.bagInter t).Perm (l₂.bagInter t)
· 使用定理 `List.Perm.bagInter_left`：∀ {α : Type u_1} [inst : DecidableEq α] (l : Li
st α) {t₁ t₂ : List α}, t₁.Perm t₂ → l.bagInter t₁ = l.bagInter t₂
-/
theorem Perm.bagInter {l₁ l₂ t₁ t₂ : List α} (hl : l₁ ~ l₂) (ht : t₁ ~ t₂) :
    l₁.bagInter t₁ ~ l₂.bagInter t₂ :=
  ht.bagInter_left l₂ ▸ hl.bagInter_right _
/-
**List.Perm.bagInter_symm** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (l₁ l₂ : List α), (l₁.bagInter l₂)
.Perm (l₂.bagInter l₁)
参数：l₁ l₂ : List α；l₁.bagInter l₂；l₂.bagInter l₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.perm_iff_count`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l₁ l
₂ : List α},   l₁.Perm l₂ ↔ ∀ (a : α), List.count a l₁ = List.count a l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.count_bagInter`：count_bagInter {a : α} {l₁ l₂ : List α} : count a (
l₁.bagInter l₂) = min (count a l₁) (count a l₂)
· 使用定理 `Nat.min_comm`：∀ (a b : ℕ), min a b = min b a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Perm.bagInter_symm (l₁ l₂ : List α) : (l₁.bagInter l₂).Perm (l₂.bagInter l₁) :=
  perm_iff_count.mpr fun _ ↦ (by simp [List.count_bagInter, Nat.min_comm])
/-
**List.Perm.inter_append** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {l t₁ t₂ : List α}, t₁.Disjoint t₂
 → (l ∩ (t₁ ++ t₂)).Perm (l ∩ t₁ ++ l ∩ t₂)
参数：l ∩ (t₁ ++ t₂)；l ∩ t₁ ++ l ∩ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.inter_cons_of_mem`：inter_cons_of_mem (l₁ : List α) (h : a in l₂) : 
(a :: l₁) inter l₂ = a :: l₁ inter l₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.inter_cons_of_notMem`：inter_cons_of_notMem (l₁ : List α) (h : a ∉ l
₂) : (a :: l₁) inter l₂ = l₁ inter l₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `List.perm_cons_append_cons`：∀ {α : Type u_1} {l l₁ l₂ : List α} (a : α),
 l.Perm (l₁ ++ l₂) → (a :: l).Perm (l₁ ++ a :: l₂)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem Perm.inter_append {l t₁ t₂ : List α} (h : Disjoint t₁ t₂) :
    l ∩ (t₁ ++ t₂) ~ l ∩ t₁ ++ l ∩ t₂ := by
  induction l with
  | nil => simp
  | cons x xs l_ih =>
    by_cases h₁ : x ∈ t₁
    · have h₂ : x ∉ t₂ := h h₁
      simp [*]
    by_cases h₂ : x ∈ t₂
    · simp only [*, inter_cons_of_notMem, false_or, mem_append, inter_cons_of_mem,
        not_false_iff]
      exact perm_cons_append_cons _ l_ih
    · simp [*]
/-
**List.Perm.take_inter** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : List α} (n : ℕ),   xs.Per
m ys → ys.Nodup → (List.take n xs).Perm (ys ∩ List.take n xs)
参数：n : ℕ；List.take n xs；ys ∩ List.take n xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Nodup.take_eq_filter_mem`：∀ {α : Type u} [inst : BEq α] [LawfulBEq 
α] {l : List α} {n : ℕ},   l.Nodup → List.take n l = List.filter (fun a => List.
elem a (List.take n…
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `List.Perm.filter`：∀ {α : Type u_1} (p : α → Bool) {l₁ l₂ : List α}, l₁.P
erm l₂ → (List.filter p l₁).Perm (List.filter p l₂)
-/
theorem Perm.take_inter {xs ys : List α} (n : ℕ) (h : xs ~ ys)
    (h' : ys.Nodup) : xs.take n ~ ys ∩ (xs.take n) := calc
  xs.take n ~ xs.filter (xs.take n).elem := by
    conv_lhs => rw [Nodup.take_eq_filter_mem ((Perm.nodup_iff h).2 h')]
  _ ~ ys ∩ (xs.take n) := Perm.filter _ h
/-
**List.Perm.drop_inter** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : List α} (n : ℕ),   xs.Per
m ys → ys.Nodup → (List.drop n xs).Perm (ys ∩ List.drop n xs)
参数：n : ℕ；List.drop n xs；ys ∩ List.drop n xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_sub_self`：∀ {n m : ℕ}, m ≤ n → n - (n - m) = m
· 使用定理 `List.take_reverse`：∀ {α : Type u_1} {xs : List α} {i : ℕ}, List.take i x
s.reverse = (List.drop (xs.length - i) xs).reverse
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `List.reverse_perm`：∀ {α : Type u_1} (l : List α), l.reverse.Perm l
· 使用定理 `List.inter_reverse`：inter_reverse {xs ys : List α} : xs inter ys.reverse
 = xs inter ys
· 使用定理 `List.Perm.take_inter`：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : L
ist α} (n : ℕ),   xs.Perm ys → ys.Nodup → (List.take n xs).Perm (ys ∩ List.take 
n xs)
-/
theorem Perm.drop_inter {xs ys : List α} (n : ℕ) (h : xs ~ ys) (h' : ys.Nodup) :
    xs.drop n ~ ys ∩ (xs.drop n) := by
  by_cases h'' : n ≤ xs.length
  · let n' := xs.length - n
    have h₀ : n = xs.length - n' := by rwa [Nat.sub_sub_self]
    have h₁ : xs.drop n = (xs.reverse.take n').reverse := by
      rw [take_reverse, h₀, reverse_reverse]
    rw [h₁]
    apply (reverse_perm _).trans
    rw [inter_reverse]
    apply Perm.take_inter _ _ h'
    apply (reverse_perm _).trans; assumption
  · grind [drop_eq_nil_of_le]
/-
**List.Perm.dropSlice_inter** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : List α} (n m : ℕ),   xs.P
erm ys → ys.Nodup → (List.dropSlice n m xs).Perm (ys ∩ List.dropSlice n m xs)
参数：n m : ℕ；List.dropSlice n m xs；ys ∩ List.dropSlice n m xs。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dropSlice_eq`：dropSlice_eq (xs : List α) (n m : Nat) : dropSlice n 
m xs = xs.take n ++ xs.drop (n + m)
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `List.Perm.append`：∀ {α : Type u_1} {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → 
t₁.Perm t₂ → (l₁ ++ t₁).Perm (l₂ ++ t₂)
· 使用定理 `List.Perm.take_inter`：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : L
ist α} (n : ℕ),   xs.Perm ys → ys.Nodup → (List.take n xs).Perm (ys ∩ List.take 
n xs)
· 使用定理 `List.Perm.drop_inter`：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : L
ist α} (n : ℕ),   xs.Perm ys → ys.Nodup → (List.drop n xs).Perm (ys ∩ List.drop 
n xs)
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.Perm.inter_append`：∀ {α : Type u_1} [inst : DecidableEq α] {l t₁ t₂
 : List α}, t₁.Disjoint t₂ → (l ∩ (t₁ ++ t₂)).Perm (l ∩ t₁ ++ l ∩ t₂)
· 使用定理 `List.disjoint_take_drop`：∀ {α : Type u_1} {m n : ℕ} {l : List α}, l.Nodu
p → m ≤ n → (List.take m l).Disjoint (List.drop n l)
-/
theorem Perm.dropSlice_inter {xs ys : List α} (n m : ℕ) (h : xs ~ ys)
    (h' : ys.Nodup) : List.dropSlice n m xs ~ ys ∩ List.dropSlice n m xs := by
  simp only [dropSlice_eq]
  have : n ≤ n + m := Nat.le_add_right _ _
  have h₂ := h.nodup_iff.2 h'
  apply Perm.trans _ (Perm.inter_append _).symm
  · exact Perm.append (Perm.take_inter _ h h') (Perm.drop_inter _ h h')
  · exact disjoint_take_drop h₂ this

end List

