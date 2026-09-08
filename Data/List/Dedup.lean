/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Lattice
public import Batteries.Data.List.Pairwise

/-!
# Erasure of duplicates in a list

This file proves basic results about `List.dedup` (definition in `Data.List.Defs`).
`dedup l` returns `l` without its duplicates. It keeps the earliest (that is, rightmost)
occurrence of each.

## Tags

duplicate, multiplicity, nodup, `nub`
-/

public section


universe u

namespace List

variable {α β : Type*} [DecidableEq α]

@[simp]
/-
**List.dedup_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_nil : dedup [] = ([] : List α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dedup_nil : dedup [] = ([] : List α) :=
  rfl
/-
**List.dedup_cons_of_mem'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_cons_of_mem' {a : α} {l : List α} (h : a in dedup l) : dedup (a :: l
) = dedup l
参数：h : a in dedup l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pwFilter_cons_of_neg`：∀ {α : Type u_1} {R : α → α → Prop} [inst : D
ecidableRel R] {a : α} {l : List α},   (¬∀ b ∈ List.pwFilter R l, R a b) → List.
pwFilter R (a :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem dedup_cons_of_mem' {a : α} {l : List α} (h : a ∈ dedup l) : dedup (a :: l) = dedup l :=
  pwFilter_cons_of_neg <| by simpa only [forall_mem_ne, not_not] using! h
/-
**List.dedup_cons_of_notMem'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_cons_of_notMem' {a : α} {l : List α} (h : a ∉ dedup l) : dedup (a ::
 l) = a :: dedup l
参数：h : a ∉ dedup l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pwFilter_cons_of_pos`：∀ {α : Type u_1} {R : α → α → Prop} [inst : D
ecidableRel R] {a : α} {l : List α},   (∀ b ∈ List.pwFilter R l, R a b) → List.p
wFilter R (a ::…
-/
theorem dedup_cons_of_notMem' {a : α} {l : List α} (h : a ∉ dedup l) :
    dedup (a :: l) = a :: dedup l :=
  pwFilter_cons_of_pos <| by simpa only [forall_mem_ne] using! h
/-
**List.dedup_cons'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_cons' (a : α) (l : List α) : dedup (a :: l) = if a in dedup l then d
edup l else a :: dedup l
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.dedup_cons_of_notMem'`：dedup_cons_of_notMem' {a : α} {l : List α} (
h : a ∉ dedup l) : dedup (a :: l) = a :: dedup l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `List.dedup_cons_of_mem'`：dedup_cons_of_mem' {a : α} {l : List α} (h : a 
in dedup l) : dedup (a :: l) = dedup l
-/
theorem dedup_cons' (a : α) (l : List α) :
    dedup (a :: l) = if a ∈ dedup l then dedup l else a :: dedup l := by
  split <;> simp [dedup_cons_of_mem', dedup_cons_of_notMem', *]

@[simp]
/-
**List.mem_dedup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_dedup {a : α} {l : List α} : a in dedup l ↔ a in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `List.forall_mem_pwFilter`：∀ {α : Type u_1} {R : α → α → Prop} [inst : De
cidableRel R],   (∀ {x y z : α}, R x z → R x y ∨ R y z) → ∀ (a : α) (l : List α)
, (∀ b ∈ List.…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mem_dedup {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l := by
  have := not_congr (@forall_mem_pwFilter α (· ≠ ·) _ ?_ a l)
  · simpa only [dedup, forall_mem_ne, not_not] using this
  · intro x y z xz
    exact not_and_or.1 <| mt (fun h ↦ h.1.trans h.2) xz

@[simp]
/-
**List.dedup_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_cons_of_mem {a : α} {l : List α} (h : a in l) : dedup (a :: l) = ded
up l
参数：h : a in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dedup_cons_of_mem'`：dedup_cons_of_mem' {a : α} {l : List α} (h : a 
in dedup l) : dedup (a :: l) = dedup l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_dedup`：mem_dedup {a : α} {l : List α} : a in dedup l ↔ a in l
-/
theorem dedup_cons_of_mem {a : α} {l : List α} (h : a ∈ l) : dedup (a :: l) = dedup l :=
  dedup_cons_of_mem' <| mem_dedup.2 h

@[simp]
/-
**List.dedup_cons_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_cons_of_notMem {a : α} {l : List α} (h : a ∉ l) : dedup (a :: l) = a
 :: dedup l
参数：h : a ∉ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.dedup_cons_of_notMem'`：dedup_cons_of_notMem' {a : α} {l : List α} (
h : a ∉ dedup l) : dedup (a :: l) = a :: dedup l
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_dedup`：mem_dedup {a : α} {l : List α} : a in dedup l ↔ a in l
-/
theorem dedup_cons_of_notMem {a : α} {l : List α} (h : a ∉ l) : dedup (a :: l) = a :: dedup l :=
  dedup_cons_of_notMem' <| mt mem_dedup.1 h
/-
**List.dedup_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_cons (a : α) (l : List α) : dedup (a :: l) = if a in l then dedup l 
else a :: dedup l
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `List.dedup_cons'`：dedup_cons' (a : α) (l : List α) : dedup (a :: l) = if
 a in dedup l then dedup l else a :: dedup l
-/
theorem dedup_cons (a : α) (l : List α) :
    dedup (a :: l) = if a ∈ l then dedup l else a :: dedup l := by
  simpa using dedup_cons' a l
/-
**List.dedup_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_sublist : forall l : List α, dedup l <+ l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pwFilter_sublist`：∀ {α : Type u_1} {R : α → α → Prop} [inst : Decid
ableRel R] (l : List α), (List.pwFilter R l).Sublist l
-/
theorem dedup_sublist : ∀ l : List α, dedup l <+ l :=
  pwFilter_sublist
/-
**List.dedup_subset** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_subset : forall l : List α, dedup l subseteq l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pwFilter_subset`：∀ {α : Type u_1} {R : α → α → Prop} [inst : Decida
bleRel R] (l : List α), List.pwFilter R l ⊆ l
-/
theorem dedup_subset : ∀ l : List α, dedup l ⊆ l :=
  pwFilter_subset
/-
**List.subset_dedup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：subset_dedup (l : List α) : l subseteq dedup l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_dedup`：mem_dedup {a : α} {l : List α} : a in dedup l ↔ a in l
-/
theorem subset_dedup (l : List α) : l ⊆ dedup l := fun _ => mem_dedup.2
/-
**List.nodup_dedup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_dedup : forall l : List α, Nodup (dedup l)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pairwise_pwFilter`：∀ {α : Type u_1} {R : α → α → Prop} [inst : Deci
dableRel R] (l : List α), List.Pairwise R (List.pwFilter R l)
-/
theorem nodup_dedup : ∀ l : List α, Nodup (dedup l) :=
  pairwise_pwFilter
/-
**List.headI_dedup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：headI_dedup [Inhabited α] (l : List α) : l.dedup.headI = if l.headI in l.t
ail then l.tail.dedup.headI else l.headI
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {l : List α} (h : a in
 l) : dedup (a :: l) = dedup l
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {l : List α} (h 
: a ∉ l) : dedup (a :: l) = a :: dedup l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem headI_dedup [Inhabited α] (l : List α) :
    l.dedup.headI = if l.headI ∈ l.tail then l.tail.dedup.headI else l.headI :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a ∈ l <;> simp [ha, List.dedup_cons_of_mem]
/-
**List.tail_dedup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：tail_dedup [Inhabited α] (l : List α) : l.dedup.tail = if l.headI in l.tai
l then l.tail.dedup.tail else l.tail.dedup
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {l : List α} (h : a in
 l) : dedup (a :: l) = dedup l
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {l : List α} (h 
: a ∉ l) : dedup (a :: l) = a :: dedup l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
theorem tail_dedup [Inhabited α] (l : List α) :
    l.dedup.tail = if l.headI ∈ l.tail then l.tail.dedup.tail else l.tail.dedup :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a ∈ l <;> simp [ha, List.dedup_cons_of_mem]
/-
**List.dedup_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pwFilter_eq_self`：∀ {α : Type u_1} {R : α → α → Prop} [inst : Decid
ableRel R] {l : List α}, List.pwFilter R l = l ↔ List.Pairwise R l
-/
theorem dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l :=
  pwFilter_eq_self
/-
**List.dedup_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_eq_cons (l : List α) (a : α) (l' : List α) : l.dedup = a :: l' ↔ a i
n l ∧ a ∉ l' ∧ l.dedup.tail = l'
参数：l : List α；a : α；l' : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_dedup`：mem_dedup {a : α} {l : List α} : a in dedup l ↔ a in l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.count_pos_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, 0 < List.count a l ↔ a ∈ l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.nodup_iff_count_le_one`：nodup_iff_count_le_one [BEq α] [LawfulBEq α
] {l : List α} : Nodup l ↔ forall a, count a l <= 1
· 使用定理 `List.nodup_dedup`：nodup_dedup : forall l : List α, Nodup (dedup l)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.count_cons_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a :
 α} {l : List α}, List.count a (a :: l) = List.count a l + 1
· 使用定理 `List.tail_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).tail = a
s
· 使用定理 `List.cons_head!_tail`：∀ {α : Type u} [inst : Inhabited α] {l : List α}, 
l ≠ [] → l.head! :: l.tail = l
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.cons_eq_cons`：∀ {α : Type u_1} {a b : α} {l l' : List α}, a :: l = 
b :: l' ↔ a = b ∧ l = l'
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem dedup_eq_cons (l : List α) (a : α) (l' : List α) :
    l.dedup = a :: l' ↔ a ∈ l ∧ a ∉ l' ∧ l.dedup.tail = l' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨mem_dedup.1 (h.symm ▸ mem_cons_self), fun ha => ?_, by rw [h, tail_cons]⟩
    have := count_pos_iff.2 ha
    have : count a l.dedup ≤ 1 := nodup_iff_count_le_one.1 (nodup_dedup l) a
    rw [h, count_cons_self] at this
    lia
  · have := @List.cons_head!_tail α ⟨a⟩ _ (ne_nil_of_mem (mem_dedup.2 h.1))
    have hal : a ∈ l.dedup := mem_dedup.2 h.1
    rw [← this, mem_cons, or_iff_not_imp_right] at hal
    exact this ▸ h.2.2.symm ▸ cons_eq_cons.2 ⟨(hal (h.2.2.symm ▸ h.2.1)).symm, rfl⟩

@[simp]
/-
**List.dedup_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_eq_nil (l : List α) : l.dedup = [] ↔ l = []
参数：l : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {l : List α} (h : a in
 l) : dedup (a :: l) = dedup l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {l : List α} (h 
: a ∉ l) : dedup (a :: l) = a :: dedup l
-/
theorem dedup_eq_nil (l : List α) : l.dedup = [] ↔ l = [] := by
  induction l with
  | nil => exact Iff.rfl
  | cons a l hl =>
    by_cases h : a ∈ l
    · simp only [List.dedup_cons_of_mem h, hl, List.ne_nil_of_mem h, reduceCtorEq]
    · simp only [List.dedup_cons_of_notMem h, List.cons_ne_nil]
/-
**List.Nodup.dedup** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {l : List α}, l.Nodup → l.dedup = 
l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.dedup_eq_self`：dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l
-/
protected theorem Nodup.dedup {l : List α} (h : l.Nodup) : l.dedup = l :=
  List.dedup_eq_self.2 h

@[simp]
/-
**List.dedup_idem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_idem {l : List α} : dedup (dedup l) = dedup l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pwFilter_idem`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} [in
st : DecidableRel R],   List.pwFilter R (List.pwFilter R l) = List.pwFilter R l
-/
theorem dedup_idem {l : List α} : dedup (dedup l) = dedup l :=
  pwFilter_idem
/-
**List.dedup_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁ union dedup l₂
参数：l₁ l₂ : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.cons_union`：∀ {α : Type u_1} [inst : BEq α] (a : α) (l₁ l₂ : List α
), a :: l₁ ∪ l₂ = List.insert a (l₁ ∪ l₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.dedup_cons_of_mem'`：dedup_cons_of_mem' {a : α} {l : List α} (h : a 
in dedup l) : dedup (a :: l) = dedup l
· 使用定理 `List.insert_of_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, a ∈ l → List.insert a l = l
· 使用定理 `List.dedup_cons_of_notMem'`：dedup_cons_of_notMem' {a : α} {l : List α} (
h : a ∉ dedup l) : dedup (a :: l) = a :: dedup l
· 使用定理 `List.insert_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a
 : α} {l : List α}, a ∉ l → List.insert a l = a :: l
-/
theorem dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁ ∪ dedup l₂ := by
  induction l₁ with | nil => rfl | cons a l₁ IH => ?_
  simp only [cons_union] at *
  rw [← IH, cons_append]
  by_cases h : a ∈ dedup (l₁ ++ l₂)
  · rw [dedup_cons_of_mem' h, insert_of_mem h]
  · rw [dedup_cons_of_notMem' h, insert_of_not_mem h]
/-
**List.dedup_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：dedup_map_of_injective [DecidableEq β] {f : α -> β} (hf : Function.Injecti
ve f) (xs : List α) : (xs.map f).dedup = xs.dedup.map f
参数：hf : Function.Injective f；xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {l : List α} (h : a in
 l) : dedup (a :: l) = dedup l
· 使用定理 `List.mem_map_of_mem`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {a : α
} {f : α → β}, a ∈ l → f a ∈ List.map f l
· 使用定理 `List.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {l : List α} (h 
: a ∉ l) : dedup (a :: l) = a :: dedup l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `List.mem_map_of_injective`：mem_map_of_injective {f : α -> β} (H : Inject
ive f) {a : α} {l : List α} : f a in map f l ↔ a in l
-/
theorem dedup_map_of_injective [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (xs : List α) :
    (xs.map f).dedup = xs.dedup.map f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [map_cons]
    by_cases h : x ∈ xs
    · rw [dedup_cons_of_mem h, dedup_cons_of_mem (mem_map_of_mem h), ih]
    · rw [dedup_cons_of_notMem h, dedup_cons_of_notMem <| (mem_map_of_injective hf).not.mpr h, ih,
        map_cons]

/-- Note that the weaker `List.Subset.dedup_append_left` is proved later. -/
/-
**List.Subset.dedup_append_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Subset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : List α}, xs ⊆ ys → (xs ++
 ys).dedup = ys.dedup
参数：xs ++ ys。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dedup_append`：dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁
 union dedup l₂
· 使用定理 `List.Subset.union_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {xs 
ys : List α}, xs ⊆ ys → xs ∪ ys = ys
· 使用定理 `List.Subset.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁ ⊆ l₂ → l₂ ⊆ 
l₃ → l₁ ⊆ l₃
· 使用定理 `List.subset_dedup`：subset_dedup (l : List α) : l subseteq dedup l

--- 原说明 ---
Note that the weaker `List.Subset.dedup_append_left` is proved later.
-/
theorem Subset.dedup_append_right {xs ys : List α} (h : xs ⊆ ys) :
    dedup (xs ++ ys) = dedup ys := by
  rw [List.dedup_append, Subset.union_eq_right (List.Subset.trans h <| subset_dedup _)]
/-
**List.Disjoint.union_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Disjoint`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : List α}, xs.Disjoint ys →
 xs ∪ ys = xs.dedup ++ ys
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
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.dedup_cons_of_mem`：dedup_cons_of_mem {a : α} {l : List α} (h : a in
 l) : dedup (a :: l) = dedup l
· 使用定理 `List.insert_of_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, a ∈ l → List.insert a l = l
· 使用定理 `List.mem_union_left`：mem_union_left (h : a in l₁) (l₂ : List α) : a in l
₁ union l₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.disjoint_cons_left`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, (a :
: l₁).Disjoint l₂ ↔ a ∉ l₂ ∧ l₁.Disjoint l₂
· 使用定理 `List.dedup_cons_of_notMem`：dedup_cons_of_notMem {a : α} {l : List α} (h 
: a ∉ l) : dedup (a :: l) = a :: dedup l
· 使用定理 `List.insert_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a
 : α} {l : List α}, a ∉ l → List.insert a l = a :: l
· 使用定理 `List.mem_union_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {x : α
} {l₁ l₂ : List α}, x ∈ l₁ ∪ l₂ ↔ x ∈ l₁ ∨ x ∈ l₂
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
-/
theorem Disjoint.union_eq {xs ys : List α} (h : Disjoint xs ys) :
    xs ∪ ys = xs.dedup ++ ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cons_union]
    rw [disjoint_cons_left] at h
    by_cases hx : x ∈ xs
    · rw [dedup_cons_of_mem hx, insert_of_mem (mem_union_left hx _), ih h.2]
    · rw [dedup_cons_of_notMem hx, insert_of_not_mem, ih h.2, cons_append]
      rw [mem_union_iff, not_or]
      exact ⟨hx, h.1⟩
/-
**List.Disjoint.dedup_append** 是 Mathlib 中的一个定理，位于命名空间 `List.Disjoint`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys : List α}, xs.Disjoint ys →
 (xs ++ ys).dedup = xs.dedup ++ ys.dedup
参数：xs ++ ys。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.dedup_append`：dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁
 union dedup l₂
· 使用定理 `List.Disjoint.union_eq`：∀ {α : Type u_1} [inst : DecidableEq α] {xs ys :
 List α}, xs.Disjoint ys → xs ∪ ys = xs.dedup ++ ys
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_dedup`：mem_dedup {a : α} {l : List α} : a in dedup l ↔ a in l
-/
theorem Disjoint.dedup_append {xs ys : List α} (h : Disjoint xs ys) :
    dedup (xs ++ ys) = dedup xs ++ dedup ys := by
  rw [List.dedup_append, Disjoint.union_eq]
  intro a hx hy
  exact h hx (mem_dedup.mp hy)
/-
**List.replicate_dedup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {x : α} {k : ℕ}, k ≠ 0 → (List.rep
licate k x).dedup = [x]
参数：List.replicate k x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem replicate_dedup {x : α} : ∀ {k}, k ≠ 0 → (replicate k x).dedup = [x]
  | 0, h => (h rfl).elim
  | 1, _ => rfl
  | n + 2, _ => by
    rw [replicate_succ, dedup_cons_of_mem (mem_replicate.2 ⟨n.succ_ne_zero, rfl⟩),
      replicate_dedup n.succ_ne_zero]
/-
**List.count_dedup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：count_dedup (l : List α) (a : α) : l.dedup.count a = if a in l then 1 else
 0
参数：l : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Nodup.count`：∀ {α : Type u_1} [inst : BEq α] [inst_1 : LawfulBEq α]
 {a : α} {l : List α},   l.Nodup → List.count a l = if a ∈ l then 1 else 0
· 使用定理 `List.nodup_dedup`：nodup_dedup : forall l : List α, Nodup (dedup l)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_dedup (l : List α) (a : α) : l.dedup.count a = if a ∈ l then 1 else 0 := by
  simp_rw [List.Nodup.count <| nodup_dedup l, mem_dedup]
/-
**List.Perm.dedup** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
dedup.Perm l₂.dedup
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
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.Perm.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁ ⊆ l
₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.count_eq_zero_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBE
q α] {a : α} {l : List α}, a ∉ l → List.count a l = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
-/
theorem Perm.dedup {l₁ l₂ : List α} (p : l₁ ~ l₂) : dedup l₁ ~ dedup l₂ :=
  perm_iff_count.2 fun a =>
    if h : a ∈ l₁ then by
      simp [h, nodup_dedup, p.subset h]
    else by
      simp [h, count_eq_zero_of_not_mem, mt p.mem_iff.2]

end List

