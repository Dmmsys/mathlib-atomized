/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Chris Hughes
-/
module

public import Mathlib.Data.List.Nodup

/-!
# List duplicates

## Main definitions

* `List.Duplicate x l : Prop` is an inductive property that holds when `x` is a duplicate in `l`

## Implementation details

In this file, `x ∈+ l` notation is shorthand for `List.Duplicate x l`.

-/

public section


variable {α : Type*}

namespace List

/-- Property that an element `x : α` of `l : List α` can be found in the list more than once. -/
/-
**List.Duplicate** 是 Mathlib 中的一个归纳类型，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → α → List α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Property that an element `x : α` of `l : List α` can be found in the list more t
han once.
-/
inductive Duplicate (x : α) : List α → Prop
  | cons_mem {l : List α} : x ∈ l → Duplicate x (x :: l)
  | cons_duplicate {y : α} {l : List α} : Duplicate x l → Duplicate x (y :: l)

local infixl:50 " ∈+ " => List.Duplicate

variable {l : List α} {x : α}
/-
**List.Mem.duplicate_cons_self** 是 Mathlib 中的一个定理，位于命名空间 `List.Mem`。
形式化陈述：∀ {α : Type u_1} {l : List α} {x : α}, x ∈ l → List.Duplicate x (x :: l)
参数：x :: l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Mem.duplicate_cons_self (h : x ∈ l) : x ∈+ x :: l :=
  Duplicate.cons_mem h
/-
**List.Duplicate.duplicate_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Duplicate`。
形式化陈述：∀ {α : Type u_1} {l : List α} {x : α}, List.Duplicate x l → ∀ (y : α), Lis
t.Duplicate x (y :: l)
参数：y : α；y :: l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Duplicate.duplicate_cons (h : x ∈+ l) (y : α) : x ∈+ y :: l :=
  Duplicate.cons_duplicate h
/-
**List.Duplicate.mem** 是 Mathlib 中的一个定理，位于命名空间 `List.Duplicate`。
形式化陈述：∀ {α : Type u_1} {l : List α} {x : α}, List.Duplicate x l → x ∈ l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
-/
theorem Duplicate.mem (h : x ∈+ l) : x ∈ l := by
  induction h with
  | cons_mem => exact mem_cons_self
  | cons_duplicate _ hm => exact mem_cons_of_mem _ hm
/-
**List.Duplicate.mem_cons_self** 是 Mathlib 中的一个定理，位于命名空间 `List.Duplicate`。
形式化陈述：∀ {α : Type u_1} {l : List α} {x : α}, List.Duplicate x (x :: l) → x ∈ l
参数：x :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `List.Duplicate.mem`：∀ {α : Type u_1} {l : List α} {x : α}, List.Duplicat
e x l → x ∈ l
-/
theorem Duplicate.mem_cons_self (h : x ∈+ x :: l) : x ∈ l := by
  obtain h | h := h
  · exact h
  · exact h.mem

@[simp]
/-
**List.duplicate_cons_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：duplicate_cons_self_iff : x in+ x :: l ↔ x in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Duplicate.mem_cons_self`：∀ {α : Type u_1} {l : List α} {x : α}, Lis
t.Duplicate x (x :: l) → x ∈ l
· 使用定理 `List.Mem.duplicate_cons_self`：∀ {α : Type u_1} {l : List α} {x : α}, x ∈
 l → List.Duplicate x (x :: l)
-/
theorem duplicate_cons_self_iff : x ∈+ x :: l ↔ x ∈ l :=
  ⟨Duplicate.mem_cons_self, Mem.duplicate_cons_self⟩
/-
**List.Duplicate.ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Duplicate`。
形式化陈述：∀ {α : Type u_1} {l : List α} {x : α}, List.Duplicate x l → l ≠ []
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_nil_iff`：∀ {α : Type u_1} (a : α), a ∈ [] ↔ False
· 使用定理 `List.Duplicate.mem`：∀ {α : Type u_1} {l : List α} {x : α}, List.Duplicat
e x l → x ∈ l
-/
theorem Duplicate.ne_nil (h : x ∈+ l) : l ≠ [] := fun H => (mem_nil_iff x).mp (H ▸ h.mem)

@[simp]
/-
**List.not_duplicate_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：not_duplicate_nil (x : α) : ¬x in+ []
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Duplicate.ne_nil`：∀ {α : Type u_1} {l : List α} {x : α}, List.Dupli
cate x l → l ≠ []
-/
theorem not_duplicate_nil (x : α) : ¬x ∈+ [] := fun H => H.ne_nil rfl
/-
**List.Duplicate.ne_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List.Duplicate`。
形式化陈述：∀ {α : Type u_1} {l : List α} {x : α}, List.Duplicate x l → ∀ (y : α), l ≠
 [y]
参数：y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.Duplicate.mem`：∀ {α : Type u_1} {l : List α} {x : α}, List.Duplicat
e x l → x ∈ l
-/
theorem Duplicate.ne_singleton (h : x ∈+ l) (y : α) : l ≠ [y] := by
  induction h with
  | cons_mem h => simp [ne_nil_of_mem h]
  | cons_duplicate h => simp [ne_nil_of_mem h.mem]

@[simp]
/-
**List.not_duplicate_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：not_duplicate_singleton (x y : α) : ¬x in+ [y]
参数：x y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Duplicate.ne_singleton`：∀ {α : Type u_1} {l : List α} {x : α}, List
.Duplicate x l → ∀ (y : α), l ≠ [y]
-/
theorem not_duplicate_singleton (x y : α) : ¬x ∈+ [y] := fun H => H.ne_singleton _ rfl
/-
**List.Duplicate.elim_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.Duplicate`。
形式化陈述：∀ {α : Type u_1} {x : α}, List.Duplicate x [] → False
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_duplicate_nil`：not_duplicate_nil (x : α) : ¬x in+ []
-/
theorem Duplicate.elim_nil (h : x ∈+ []) : False :=
  not_duplicate_nil x h
/-
**List.Duplicate.elim_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List.Duplicate`。
形式化陈述：∀ {α : Type u_1} {x y : α}, List.Duplicate x [y] → False
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_duplicate_singleton`：not_duplicate_singleton (x y : α) : ¬x in+
 [y]
-/
theorem Duplicate.elim_singleton {y : α} (h : x ∈+ [y]) : False :=
  not_duplicate_singleton x y h
/-
**List.duplicate_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：duplicate_cons_iff {y : α} : x in+ y :: l ↔ y = x ∧ x in l ∨ x in+ l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem duplicate_cons_iff {y : α} : x ∈+ y :: l ↔ y = x ∧ x ∈ l ∨ x ∈+ l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain hm | hm := h
    · exact Or.inl ⟨rfl, hm⟩
    · exact Or.inr hm
  · rcases h with (⟨rfl | h⟩ | h)
    · simpa
    · exact h.cons_duplicate
/-
**List.Duplicate.of_duplicate_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Duplicate`。
形式化陈述：∀ {α : Type u_1} {l : List α} {x y : α}, List.Duplicate x (y :: l) → x ≠ y
 → List.Duplicate x l
参数：y :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem Duplicate.of_duplicate_cons {y : α} (h : x ∈+ y :: l) (hx : x ≠ y) : x ∈+ l := by
  simpa [duplicate_cons_iff, hx.symm] using h
/-
**List.duplicate_cons_iff_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：duplicate_cons_iff_of_ne {y : α} (hne : x != y) : x in+ y :: l ↔ x in+ l
参数：hne : x != y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem duplicate_cons_iff_of_ne {y : α} (hne : x ≠ y) : x ∈+ y :: l ↔ x ∈+ l := by
  simp [duplicate_cons_iff, hne.symm]
/-
**List.Duplicate.mono_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List.Duplicate`。
形式化陈述：∀ {α : Type u_1} {l : List α} {x : α} {l' : List α}, List.Duplicate x l → 
l.Sublist l' → List.Duplicate x l'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Duplicate.duplicate_cons`：∀ {α : Type u_1} {l : List α} {x : α}, Li
st.Duplicate x l → ∀ (y : α), List.Duplicate x (y :: l)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.duplicate_cons_iff`：duplicate_cons_iff {y : α} : x in+ y :: l ↔ y =
 x ∧ x in l ∨ x in+ l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem Duplicate.mono_sublist {l' : List α} (hx : x ∈+ l) (h : l <+ l') : x ∈+ l' := by
  induction h with
  | slnil => exact hx
  | cons y _ IH => exact (IH hx).duplicate_cons _
  | cons_cons y h IH =>
    rw [duplicate_cons_iff] at hx ⊢
    rcases hx with (⟨rfl, hx⟩ | hx)
    · simp [h.subset hx]
    · simp [IH hx]

/-- The contrapositive of `List.nodup_iff_sublist`. -/
/-
**List.duplicate_iff_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：duplicate_iff_sublist : x in+ l ↔ [x, x] <+ l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.duplicate_cons_iff_of_ne`：duplicate_cons_iff_of_ne {y : α} (hne : x
 != y) : x in+ y :: l ↔ x in+ l
· 使用定理 `List.sublist_cons_of_sublist`：sublist_cons_of_sublist (a : α) (h : l₁ <+
 l₂) : l₁ <+ a :: l₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The contrapositive of `List.nodup_iff_sublist`.
-/
theorem duplicate_iff_sublist : x ∈+ l ↔ [x, x] <+ l := by
  induction l with
  | nil => simp
  | cons y l IH =>
    by_cases hx : x = y
    · simp [hx, cons_sublist_cons, singleton_sublist]
    · rw [duplicate_cons_iff_of_ne hx, IH]
      refine ⟨sublist_cons_of_sublist y, fun h => ?_⟩
      cases h
      · assumption
      · contradiction
/-
**List.nodup_iff_forall_not_duplicate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_iff_forall_not_duplicate : Nodup l ↔ forall x : α, ¬x in+ l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nodup_iff_forall_not_duplicate : Nodup l ↔ ∀ x : α, ¬x ∈+ l := by
  simp_rw [nodup_iff_sublist, duplicate_iff_sublist]
/-
**List.exists_duplicate_iff_not_nodup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：exists_duplicate_iff_not_nodup : (exists x : α, x in+ l) ↔ ¬Nodup l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_duplicate_iff_not_nodup : (∃ x : α, x ∈+ l) ↔ ¬Nodup l := by
  simp [nodup_iff_forall_not_duplicate]
/-
**List.Duplicate.not_nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.Duplicate`。
形式化陈述：∀ {α : Type u_1} {l : List α} {x : α}, List.Duplicate x l → ¬l.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_iff_forall_not_duplicate`：nodup_iff_forall_not_duplicate : No
dup l ↔ forall x : α, ¬x in+ l
-/
theorem Duplicate.not_nodup (h : x ∈+ l) : ¬Nodup l := fun H =>
  nodup_iff_forall_not_duplicate.mp H _ h
/-
**List.duplicate_iff_two_le_count** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：duplicate_iff_two_le_count [DecidableEq α] : x in+ l ↔ 2 <= count x l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem duplicate_iff_two_le_count [DecidableEq α] : x ∈+ l ↔ 2 ≤ count x l := by
  simp [replicate_succ, duplicate_iff_sublist, ← replicate_sublist_iff]
/-
**List.decidableDuplicate** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → (x : α) → (l : List α) → Decidable (Lis
t.Duplicate x l)
参数：x : α；l : List α；List.Duplicate x l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableDuplicate [DecidableEq α] (x : α) : ∀ l : List α, Decidable (x ∈+ l)
  | [] => isFalse (not_duplicate_nil x)
  | y :: l =>
    match decidableDuplicate x l with
    | isTrue h => isTrue (h.duplicate_cons y)
    | isFalse h =>
      if hx : y = x ∧ x ∈ l then isTrue (hx.left.symm ▸ List.Mem.duplicate_cons_self hx.right)
      else isFalse (by simpa [duplicate_cons_iff, h] using hx)

end List

