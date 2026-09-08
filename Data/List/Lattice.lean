/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
Kim Morrison
-/
module

public import Mathlib.Data.List.Basic

/-!
# Lattice structure of lists

This file proves basic properties about `List.disjoint`, `List.union`, `List.inter` and
`List.bagInter`, which are defined in core Lean and `Data.List.Defs`.

`l₁ ∪ l₂` is the list where all elements of `l₁` have been inserted in `l₂` in order. For example,
`[0, 0, 1, 2, 2, 3] ∪ [4, 3, 3, 0] = [1, 2, 4, 3, 3, 0]`.

`l₁ ∩ l₂` is the list of elements of `l₁` in order which are in `l₂`. For example,
`[0, 0, 1, 2, 2, 3] ∩ [4, 3, 3, 0] = [0, 0, 3]`.

`List.bagInter l₁ l₂` is the list of elements that are in both `l₁` and `l₂`,
counted with multiplicity and in the order they appear in `l₁`.
As opposed to `List.inter`, `List.bagInter` copes well with multiplicity. For example,
`bagInter [0, 1, 2, 3, 2, 1, 0] [1, 0, 1, 4, 3] = [0, 1, 3, 1]`.
-/

public section


open Nat

namespace List

variable {α : Type*} {l₁ l₂ : List α} {p : α → Prop} {a : α}

/-! ### `Disjoint` -/


section Disjoint

@[symm]
/-
**List.Disjoint.symm** 是 Mathlib 中的一个定理，位于命名空间 `List.Disjoint`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Disjoint l₂ → l₂.Disjoint l₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Disjoint.symm (d : Disjoint l₁ l₂) : Disjoint l₂ l₁ := fun _ i₂ i₁ => d i₁ i₂

end Disjoint

variable [DecidableEq α]

/-! ### `union` -/


section Union

/-
**List.mem_union_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_union_left (h : a in l₁) (l₂ : List α) : a in l₁ union l₂
参数：h : a in l₁；l₂ : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_union_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {x : α
} {l₁ l₂ : List α}, x ∈ l₁ ∪ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem mem_union_left (h : a ∈ l₁) (l₂ : List α) : a ∈ l₁ ∪ l₂ :=
  mem_union_iff.2 (Or.inl h)
/-
**List.mem_union_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_union_right (l₁ : List α) (h : a in l₂) : a in l₁ union l₂
参数：l₁ : List α；h : a in l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_union_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {x : α
} {l₁ l₂ : List α}, x ∈ l₁ ∪ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem mem_union_right (l₁ : List α) (h : a ∈ l₂) : a ∈ l₁ ∪ l₂ :=
  mem_union_iff.2 (Or.inr h)
/-
**List.sublist_suffix_of_union** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_suffix_of_union : forall l₁ l₂ : List α, exists t, t <+ l₁ ∧ t ++ 
l₂ = l₁ union l₂ | [], _ => ⟨[], by rfl, rfl⟩ | a :: l₁, l₂ => let ⟨t, s, e⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublist_suffix_of_union : ∀ l₁ l₂ : List α, ∃ t, t <+ l₁ ∧ t ++ l₂ = l₁ ∪ l₂
  | [], _ => ⟨[], by rfl, rfl⟩
  | a :: l₁, l₂ =>
    let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂
    if h : a ∈ l₁ ∪ l₂ then
      ⟨t, sublist_cons_of_sublist _ s, by
        simp only [e, cons_union, insert_of_mem h]⟩
    else
      ⟨a :: t, s.cons_cons _, by
        simp only [cons_append, cons_union, e, insert_of_not_mem h]⟩
/-
**List.suffix_union_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：suffix_union_right (l₁ l₂ : List α) : l₂ <:+ l₁ union l₂
参数：l₁ l₂ : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.sublist_suffix_of_union`：sublist_suffix_of_union : forall l₁ l₂ : L
ist α, exists t, t <+ l₁ ∧ t ++ l₂ = l₁ union l₂ | [], _ => ⟨[], by rfl, rfl⟩ | 
a :: l₁, l₂ => let…
-/
theorem suffix_union_right (l₁ l₂ : List α) : l₂ <:+ l₁ ∪ l₂ :=
  (sublist_suffix_of_union l₁ l₂).imp fun _ => And.right
/-
**List.union_sublist_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：union_sublist_append (l₁ l₂ : List α) : l₁ union l₂ <+ l₁ ++ l₂
参数：l₁ l₂ : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublist_suffix_of_union`：sublist_suffix_of_union : forall l₁ l₂ : L
ist α, exists t, t <+ l₁ ∧ t ++ l₂ = l₁ union l₂ | [], _ => ⟨[], by rfl, rfl⟩ | 
a :: l₁, l₂ => let…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.append_sublist_append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} (l :
 List α), (l₁ ++ l).Sublist (l₂ ++ l) ↔ l₁.Sublist l₂
-/
theorem union_sublist_append (l₁ l₂ : List α) : l₁ ∪ l₂ <+ l₁ ++ l₂ :=
  let ⟨_, s, e⟩ := sublist_suffix_of_union l₁ l₂
  e ▸ (append_sublist_append_right _).2 s
/-
**List.forall_mem_union** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_mem_union : (forall x in l₁ union l₂, p x) ↔ (forall x in l₁, p x) 
∧ forall x in l₂, p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem forall_mem_union : (∀ x ∈ l₁ ∪ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ ∀ x ∈ l₂, p x := by
  simp only [mem_union_iff, or_imp, forall_and]
/-
**List.forall_mem_of_forall_mem_union_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_mem_of_forall_mem_union_left (h : forall x in l₁ union l₂, p x) : f
orall x in l₁, p x
参数：h : forall x in l₁ union l₂, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.forall_mem_union`：forall_mem_union : (forall x in l₁ union l₂, p x)
 ↔ (forall x in l₁, p x) ∧ forall x in l₂, p x
-/
theorem forall_mem_of_forall_mem_union_left (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₁, p x :=
  (forall_mem_union.1 h).1
/-
**List.forall_mem_of_forall_mem_union_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_mem_of_forall_mem_union_right (h : forall x in l₁ union l₂, p x) : 
forall x in l₂, p x
参数：h : forall x in l₁ union l₂, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.forall_mem_union`：forall_mem_union : (forall x in l₁ union l₂, p x)
 ↔ (forall x in l₁, p x) ∧ forall x in l₂, p x
-/
theorem forall_mem_of_forall_mem_union_right (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₂, p x :=
  (forall_mem_union.1 h).2
/-
**List.Subset.union_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Subset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : List α}, xs ⊆ ys → xs ∪ y
s = ys
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nil_union`：∀ {α : Type u_1} [inst : BEq α] (l : List α), [] ∪ l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.cons_union`：∀ {α : Type u_1} [inst : BEq α] (a : α) (l₁ l₂ : List α
), a :: l₁ ∪ l₂ = List.insert a (l₁ ∪ l₂)
· 使用定理 `List.insert_of_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, a ∈ l → List.insert a l = l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.mem_union_right`：mem_union_right (l₁ : List α) (h : a in l₂) : a in
 l₁ union l₂
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.subset_of_cons_subset`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, a
 :: l₁ ⊆ l₂ → l₁ ⊆ l₂
-/
theorem Subset.union_eq_right {xs ys : List α} (h : xs ⊆ ys) : xs ∪ ys = ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cons_union, insert_of_mem <| mem_union_right _ <| h mem_cons_self,
      ih <| subset_of_cons_subset h]

end Union

/-! ### `inter` -/


section Inter

@[simp, grind =]
/-
**List.inter_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inter_nil (l : List α) : [] inter l = []
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_nil (l : List α) : [] ∩ l = [] :=
  rfl

@[simp]
/-
**List.inter_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inter_cons_of_mem (l₁ : List α) (h : a in l₂) : (a :: l₁) inter l₂ = a :: 
l₁ inter l₂
参数：l₁ : List α；h : a in l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.elem_eq_contains`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l : List
 α}, List.elem a l = l.contains a
· 使用定理 `List.contains_eq_mem`：∀ {α : Type u_1} [inst : BEq α] [inst_1 : LawfulBE
q α] (a : α) (as : List α), as.contains a = decide (a ∈ as)
· 使用定理 `List.filter_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, p a = true → List.filter p (a :: l) = a :: List.filter p l
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inter_cons_of_mem (l₁ : List α) (h : a ∈ l₂) : (a :: l₁) ∩ l₂ = a :: l₁ ∩ l₂ := by
  simp [Inter.inter, List.inter, h]

@[simp]
/-
**List.inter_cons_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inter_cons_of_notMem (l₁ : List α) (h : a ∉ l₂) : (a :: l₁) inter l₂ = l₁ 
inter l₂
参数：l₁ : List α；h : a ∉ l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.elem_eq_contains`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l : List
 α}, List.elem a l = l.contains a
· 使用定理 `List.contains_eq_mem`：∀ {α : Type u_1} [inst : BEq α] [inst_1 : LawfulBE
q α] (a : α) (as : List α), as.contains a = decide (a ∈ as)
· 使用定理 `List.filter_cons_of_neg`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, ¬p a = true → List.filter p (a :: l) = List.filter p l
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Bool.false_eq_true`：(false = true) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inter_cons_of_notMem (l₁ : List α) (h : a ∉ l₂) : (a :: l₁) ∩ l₂ = l₁ ∩ l₂ := by
  simp [Inter.inter, List.inter, h]

@[grind =]
/-
**List.inter_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inter_cons (l₁ : List α) : (a :: l₁) inter l₂ = if a in l₂ then a :: l₁ in
ter l₂ else l₁ inter l₂
参数：l₁ : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.inter_cons_of_mem`：inter_cons_of_mem (l₁ : List α) (h : a in l₂) : 
(a :: l₁) inter l₂ = a :: l₁ inter l₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `List.inter_cons_of_notMem`：inter_cons_of_notMem (l₁ : List α) (h : a ∉ l
₂) : (a :: l₁) inter l₂ = l₁ inter l₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem inter_cons (l₁ : List α) :
    (a :: l₁) ∩ l₂ = if a ∈ l₂ then a :: l₁ ∩ l₂ else l₁ ∩ l₂ := by
  split_ifs <;> simp_all

@[simp, grind =]
/-
**List.inter_nil'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inter_nil' (l : List α) : l inter [] = []
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inter_nil' (l : List α) : l ∩ [] = [] := by
  induction l with grind
/-
**List.mem_of_mem_inter_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_of_mem_inter_left : a in l₁ inter l₂ -> a in l₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_of_mem_filter`：mem_of_mem_filter {a : α} {l} (h : a in filter p
 l) : a in l
-/
theorem mem_of_mem_inter_left : a ∈ l₁ ∩ l₂ → a ∈ l₁ :=
  mem_of_mem_filter
/-
**List.mem_of_mem_inter_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_of_mem_inter_right (h : a in l₁ inter l₂) : a in l₂
参数：h : a in l₁ inter l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.elem_eq_contains`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l : List
 α}, List.elem a l = l.contains a
· 使用定理 `List.contains_eq_mem`：∀ {α : Type u_1} [inst : BEq α] [inst_1 : LawfulBE
q α] (a : α) (as : List α), as.contains a = decide (a ∈ as)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `List.of_mem_filter`：of_mem_filter {a : α} {l} (h : a in filter p l) : p 
a
-/
theorem mem_of_mem_inter_right (h : a ∈ l₁ ∩ l₂) : a ∈ l₂ := by simpa using of_mem_filter h
/-
**List.mem_inter_of_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_inter_of_mem_of_mem (h₁ : a in l₁) (h₂ : a in l₂) : a in l₁ inter l₂
参数：h₁ : a in l₁；h₂ : a in l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_filter_of_mem`：mem_filter_of_mem {a : α} {l} (h₁ : a in l) (h₂ 
: p a) : a in filter p l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.elem_eq_contains`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l : List
 α}, List.elem a l = l.contains a
· 使用定理 `List.contains_eq_mem`：∀ {α : Type u_1} [inst : BEq α] [inst_1 : LawfulBE
q α] (a : α) (as : List α), as.contains a = decide (a ∈ as)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
-/
theorem mem_inter_of_mem_of_mem (h₁ : a ∈ l₁) (h₂ : a ∈ l₂) : a ∈ l₁ ∩ l₂ :=
  mem_filter_of_mem h₁ <| by simpa using h₂
/-
**List.inter_subset_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inter_subset_left {l₁ l₂ : List α} : l₁ inter l₂ subseteq l₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.filter_subset_self`：filter_subset_self (l : List α) : filter p l su
bseteq l
-/
theorem inter_subset_left {l₁ l₂ : List α} : l₁ ∩ l₂ ⊆ l₁ :=
  filter_subset_self _
/-
**List.inter_subset_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inter_subset_right {l₁ l₂ : List α} : l₁ inter l₂ subseteq l₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_of_mem_inter_right`：mem_of_mem_inter_right (h : a in l₁ inter l
₂) : a in l₂
-/
theorem inter_subset_right {l₁ l₂ : List α} : l₁ ∩ l₂ ⊆ l₂ := fun _ => mem_of_mem_inter_right
/-
**List.subset_inter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：subset_inter {l l₁ l₂ : List α} (h₁ : l subseteq l₁) (h₂ : l subseteq l₂) 
: l subseteq l₁ inter l₂
参数：h₁ : l subseteq l₁；h₂ : l subseteq l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_inter_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {x : α
} {l₁ l₂ : List α}, x ∈ l₁ ∩ l₂ ↔ x ∈ l₁ ∧ x ∈ l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem subset_inter {l l₁ l₂ : List α} (h₁ : l ⊆ l₁) (h₂ : l ⊆ l₂) : l ⊆ l₁ ∩ l₂ := fun _ h =>
  mem_inter_iff.2 ⟨h₁ h, h₂ h⟩
/-
**List.inter_eq_nil_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inter_eq_nil_iff_disjoint : l₁ inter l₂ = [] ↔ Disjoint l₁ l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem inter_eq_nil_iff_disjoint : l₁ ∩ l₂ = [] ↔ Disjoint l₁ l₂ := by
  simp only [eq_nil_iff_forall_not_mem, mem_inter_iff, not_and]
  rfl

alias ⟨_, Disjoint.inter_eq_nil⟩ := inter_eq_nil_iff_disjoint
/-
**List.forall_mem_inter_of_forall_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_mem_inter_of_forall_left (h : forall x in l₁, p x) (l₂ : List α) : 
forall x, x in l₁ inter l₂ -> p x
参数：h : forall x in l₁, p x；l₂ : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BAll.imp_left`：BAll.imp_left (H : forall x, p x -> q x) (h₁ : forall x, 
q x -> r x) (x) (h : p x) : r x
· 使用定理 `List.mem_of_mem_inter_left`：mem_of_mem_inter_left : a in l₁ inter l₂ -> 
a in l₁
-/
theorem forall_mem_inter_of_forall_left (h : ∀ x ∈ l₁, p x) (l₂ : List α) :
    ∀ x, x ∈ l₁ ∩ l₂ → p x :=
  BAll.imp_left (fun _ => mem_of_mem_inter_left) h
/-
**List.forall_mem_inter_of_forall_right** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：forall_mem_inter_of_forall_right (l₁ : List α) (h : forall x in l₂, p x) :
 forall x, x in l₁ inter l₂ -> p x
参数：l₁ : List α；h : forall x in l₂, p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BAll.imp_left`：BAll.imp_left (H : forall x, p x -> q x) (h₁ : forall x, 
q x -> r x) (x) (h : p x) : r x
· 使用定理 `List.mem_of_mem_inter_right`：mem_of_mem_inter_right (h : a in l₁ inter l
₂) : a in l₂
-/
theorem forall_mem_inter_of_forall_right (l₁ : List α) (h : ∀ x ∈ l₂, p x) :
    ∀ x, x ∈ l₁ ∩ l₂ → p x :=
  BAll.imp_left (fun _ => mem_of_mem_inter_right) h

@[simp]
/-
**List.inter_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inter_reverse {xs ys : List α} : xs inter ys.reverse = xs inter ys
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.elem_eq_mem`：∀ {α : Type u_1} [inst : BEq α] [inst_1 : LawfulBEq α]
 (a : α) (as : List α), List.elem a as = decide (a ∈ as)
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inter_reverse {xs ys : List α} : xs ∩ ys.reverse = xs ∩ ys := by
  simp only [List.inter_def, elem_eq_mem, mem_reverse]
/-
**List.Subset.inter_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Subset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : List α}, xs ⊆ ys → xs ∩ y
s = xs
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.filter_eq_self`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, List.
filter p l = l ↔ ∀ a ∈ l, p a = true
· 使用定理 `List.elem_eq_true_of_mem`：∀ {α : Type u} [inst : BEq α] [ReflBEq α] {a :
 α} {as : List α}, a ∈ as → List.elem a as = true
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem Subset.inter_eq_left {xs ys : List α} (h : xs ⊆ ys) : xs ∩ ys = xs :=
  List.filter_eq_self.mpr fun _ ha => elem_eq_true_of_mem (h ha)
/-
**List.Sublist.inter_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {l₁ l₂ l₃ : List α}, l₂.Sublist l₃
 → (l₁ ∩ l₂).Sublist (l₁ ∩ l₃)
参数：l₁ ∩ l₂；l₁ ∩ l₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sublist.inter_left {l₁ l₂ l₃ : List α} (h : l₂.Sublist l₃) :
    (l₁ ∩ l₂).Sublist (l₁ ∩ l₃) := by
  grind [inter_def, monotone_filter_right]
/-
**List.Sublist.inter_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {l₁ l₂ l₃ : List α}, l₁.Sublist l₂
 → (l₁ ∩ l₃).Sublist (l₂ ∩ l₃)
参数：l₁ ∩ l₃；l₂ ∩ l₃。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sublist.inter_right {l₁ l₂ l₃ : List α} (h : l₁.Sublist l₂) :
    (l₁ ∩ l₃).Sublist (l₂ ∩ l₃) := by
  grind [inter_def]

end Inter

/-! ### `bagInter` -/


section BagInter

@[simp, grind =]
/-
**List.nil_bagInter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nil_bagInter (l : List α) : [].bagInter l = []
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nil_bagInter (l : List α) : [].bagInter l = [] := by cases l <;> rfl

@[simp, grind =]
/-
**List.bagInter_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：bagInter_nil (l : List α) : l.bagInter [] = []
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bagInter_nil (l : List α) : l.bagInter [] = [] := by cases l <;> rfl

@[simp]
/-
**List.cons_bagInter_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_bagInter_of_mem (l₁ : List α) (h : a in l₂) : (a :: l₁).bagInter l₂ =
 a :: l₁.bagInter (l₂.erase a)
参数：l₁ : List α；h : a in l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cons_bagInter_of_mem (l₁ : List α) (h : a ∈ l₂) :
    (a :: l₁).bagInter l₂ = a :: l₁.bagInter (l₂.erase a) := by
  cases l₂ with grind [List.bagInter]

@[deprecated (since := "2026-05-13")]
alias cons_bagInter_of_pos := cons_bagInter_of_mem

@[simp]
/-
**List.cons_bagInter_of_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_bagInter_of_not_mem (l₁ : List α) (h : a ∉ l₂) : (a :: l₁).bagInter l
₂ = l₁.bagInter l₂
参数：l₁ : List α；h : a ∉ l₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cons_bagInter_of_not_mem (l₁ : List α) (h : a ∉ l₂) :
    (a :: l₁).bagInter l₂ = l₁.bagInter l₂ := by
  cases l₂ with grind [List.bagInter]

@[deprecated (since := "2026-05-13")]
alias cons_bagInter_of_neg := cons_bagInter_of_not_mem

@[grind =]
/-
**List.cons_bagInter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_bagInter : (a :: l₁).bagInter l₂ = if a in l₂ then a :: l₁.bagInter (
l₂.erase a) else l₁.bagInter l₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.cons_bagInter_of_mem`：cons_bagInter_of_mem (l₁ : List α) (h : a in 
l₂) : (a :: l₁).bagInter l₂ = a :: l₁.bagInter (l₂.erase a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `List.cons_bagInter_of_not_mem`：cons_bagInter_of_not_mem (l₁ : List α) (h
 : a ∉ l₂) : (a :: l₁).bagInter l₂ = l₁.bagInter l₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem cons_bagInter :
    (a :: l₁).bagInter l₂ = if a ∈ l₂ then a :: l₁.bagInter (l₂.erase a) else l₁.bagInter l₂ := by
  split_ifs <;> simp_all

@[deprecated (since := "2026-05-13")]
alias cons_bagInteger := cons_bagInter

@[simp]
/-
**List.bagInter_cons_of_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：bagInter_cons_of_not_mem (l₂ : List α) (h : a ∉ l₁) : l₁.bagInter (a :: l₂
) = l₁.bagInter l₂
参数：l₂ : List α；h : a ∉ l₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bagInter_cons_of_not_mem (l₂ : List α) (h : a ∉ l₁) :
    l₁.bagInter (a :: l₂) = l₁.bagInter l₂ := by
  induction l₁ generalizing l₂ <;> grind

@[simp]
/-
**List.mem_bagInter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_bagInter {a : α} {l₁ l₂ : List α} : a in l₁.bagInter l₂ ↔ a in l₁ ∧ a 
in l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.bagInter.induct_unfolding`：∀ {α : Type u_1} [inst : BEq α] (motive 
: List α → List α → List α → Prop),   (∀ (x : List α), motive [] x []) →     (∀ 
(t : List α), (t = […
-/
theorem mem_bagInter {a : α} {l₁ l₂ : List α} : a ∈ l₁.bagInter l₂ ↔ a ∈ l₁ ∧ a ∈ l₂ := by
  fun_induction List.bagInter with grind

@[simp]
/-
**List.count_bagInter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：count_bagInter {a : α} {l₁ l₂ : List α} : count a (l₁.bagInter l₂) = min (
count a l₁) (count a l₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.bagInter.induct_unfolding`：∀ {α : Type u_1} [inst : BEq α] (motive 
: List α → List α → List α → Prop),   (∀ (x : List α), motive [] x []) →     (∀ 
(t : List α), (t = […
-/
theorem count_bagInter {a : α} {l₁ l₂ : List α} :
    count a (l₁.bagInter l₂) = min (count a l₁) (count a l₂) := by
  fun_induction List.bagInter with grind
/-
**List.bagInter_sublist_left** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：bagInter_sublist_left {l₁ l₂ : List α} : l₁.bagInter l₂ <+ l₁
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.bagInter.induct_unfolding`：∀ {α : Type u_1} [inst : BEq α] (motive 
: List α → List α → List α → Prop),   (∀ (x : List α), motive [] x []) →     (∀ 
(t : List α), (t = […
-/
theorem bagInter_sublist_left {l₁ l₂ : List α} : l₁.bagInter l₂ <+ l₁ := by
  fun_induction List.bagInter with grind
/-
**List.singleton_bagInter** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：singleton_bagInter (a : α) : [a].bagInter l₁ = if a in l₁ then [a] else []
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem singleton_bagInter (a : α) : [a].bagInter l₁ = if a ∈ l₁ then [a] else [] := by
  grind
/-
**List.bagInter_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：bagInter_singleton (a : α) : l₁.bagInter [a] = if a in l₁ then [a] else []
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem bagInter_singleton (a : α) : l₁.bagInter [a] = if a ∈ l₁ then [a] else [] := by
  induction l₁ <;> grind

@[simp]
/-
**List.bagInter_erase_of_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：bagInter_erase_of_not_mem (h : a ∉ l₁) : l₁.bagInter (l₂.erase a) = l₁.bag
Inter l₂
参数：h : a ∉ l₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bagInter_erase_of_not_mem (h : a ∉ l₁) :
    l₁.bagInter (l₂.erase a) = l₁.bagInter l₂ := by
  induction l₁ generalizing l₂ <;> grind

@[simp]
/-
**List.erase_bagInter_of_not_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：erase_bagInter_of_not_mem (h : a ∉ l₂) : (l₁.erase a).bagInter l₂ = l₁.bag
Inter l₂
参数：h : a ∉ l₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem erase_bagInter_of_not_mem (h : a ∉ l₂) :
    (l₁.erase a).bagInter l₂ = l₁.bagInter l₂ := by
  induction l₁ generalizing l₂ <;> grind
/-
**List.bagInter_nil_iff_inter_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (l₁ l₂ : List α), l₁.bagInter l₂ =
 [] ↔ l₁ ∩ l₂ = []
参数：l₁ l₂ : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bagInter_nil_iff_inter_nil : ∀ l₁ l₂ : List α, l₁.bagInter l₂ = [] ↔ l₁ ∩ l₂ = []
  | [], l₂ => by simp
  | b :: l₁, l₂ => by
    by_cases h : b ∈ l₂
    · simp [h]
    · simpa [h] using bagInter_nil_iff_inter_nil l₁ l₂

@[simp]
/-
**List.bagInter_eq_nil_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：bagInter_eq_nil_iff_disjoint : l₁.bagInter l₂ = [] ↔ l₁.Disjoint l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.bagInter_nil_iff_inter_nil`：∀ {α : Type u_1} [inst : DecidableEq α]
 (l₁ l₂ : List α), l₁.bagInter l₂ = [] ↔ l₁ ∩ l₂ = []
· 使用定理 `List.inter_eq_nil_iff_disjoint`：inter_eq_nil_iff_disjoint : l₁ inter l₂ 
= [] ↔ Disjoint l₁ l₂
-/
theorem bagInter_eq_nil_iff_disjoint : l₁.bagInter l₂ = [] ↔ l₁.Disjoint l₂ :=
  (bagInter_nil_iff_inter_nil _ _).trans inter_eq_nil_iff_disjoint
/-
**List.Nodup.bagInter_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α} [inst : DecidableEq α], l₁.Nodup → (l₁.b
agInter l₂).Nodup
参数：l₁.bagInter l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_iff_count`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l :
 List α}, l.Nodup ↔ ∀ (a : α), List.count a l ≤ 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem Nodup.bagInter_right (h : l₁.Nodup) : (l₁.bagInter l₂).Nodup :=
  nodup_iff_count.mpr fun x ↦ (by grind [List.count_bagInter])
/-
**List.Nodup.bagInter_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α} [inst : DecidableEq α], l₂.Nodup → (l₁.b
agInter l₂).Nodup
参数：l₁.bagInter l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_iff_count`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l :
 List α}, l.Nodup ↔ ∀ (a : α), List.count a l ≤ 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem Nodup.bagInter_left (h : l₂.Nodup) : (l₁.bagInter l₂).Nodup :=
  nodup_iff_count.mpr fun x ↦ (by grind [List.count_bagInter])
/-
**List.Sublist.bagInter_inter** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α} [inst : DecidableEq α], (l₁.bagInter l₂)
.Sublist (l₁ ∩ l₂)
参数：l₁.bagInter l₂；l₁ ∩ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nil_bagInter`：nil_bagInter (l : List α) : [].bagInter l = []
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.cons_bagInter`：cons_bagInter : (a :: l₁).bagInter l₂ = if a in l₂ t
hen a :: l₁.bagInter (l₂.erase a) else l₁.bagInter l₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `List.inter_cons_of_notMem`：inter_cons_of_notMem (l₁ : List α) (h : a ∉ l
₂) : (a :: l₁) inter l₂ = l₁ inter l₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `List.inter_cons_of_mem`：inter_cons_of_mem (l₁ : List α) (h : a in l₂) : 
(a :: l₁) inter l₂ = a :: l₁ inter l₂
· 使用定理 `List.cons_sublist_cons`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, (a ::
 l₁).Sublist (a :: l₂) ↔ l₁.Sublist l₂
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `List.Sublist.inter_left`：∀ {α : Type u_1} [inst : DecidableEq α] {l₁ l₂ 
l₃ : List α}, l₂.Sublist l₃ → (l₁ ∩ l₂).Sublist (l₁ ∩ l₃)
-/
theorem Sublist.bagInter_inter : (l₁.bagInter l₂).Sublist (l₁ ∩ l₂) := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons _ _ ih =>
    rw [cons_bagInter]
    split
    · rw [inter_cons_of_mem _ (by assumption), cons_sublist_cons]
      exact ih.trans <| Sublist.inter_left (by grind [erase_sublist])
    · simp_all

end BagInter

end List

