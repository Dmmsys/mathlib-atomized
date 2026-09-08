/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Rotate
public import Mathlib.GroupTheory.Perm.Support

/-!
# Permutations from a list

A list `l : List α` can be interpreted as an `Equiv.Perm α` where each element in the list
is permuted to the next one, defined as `formPerm`. When we have that `Nodup l`,
we prove that `Equiv.Perm.support (formPerm l) = l.toFinset`, and that
`formPerm l` is rotationally invariant, in `formPerm_rotate`.

When there are duplicate elements in `l`, how and in what arrangement with respect to the other
elements they appear in the list determines the formed permutation.
This is because `List.formPerm` is implemented as a product of `Equiv.swap`s.
That means that presence of a sublist of two adjacent duplicates like `[..., x, x, ...]`
will produce the same permutation as if the adjacent duplicates were not present.

The `List.formPerm` definition is meant to primarily be used with `Nodup l`, so that
the resulting permutation is cyclic (if `l` has at least two elements).
The presence of duplicates in a particular placement can lead `List.formPerm` to produce a
nontrivial permutation that is noncyclic.
-/

@[expose] public section


namespace List

variable {α β : Type*}

section FormPerm

variable [DecidableEq α] (l : List α)

open Equiv Equiv.Perm

/-- A list `l : List α` can be interpreted as an `Equiv.Perm α` where each element in the list
is permuted to the next one, defined as `formPerm`. When we have that `Nodup l`,
we prove that `Equiv.Perm.support (formPerm l) = l.toFinset`, and that
`formPerm l` is rotationally invariant, in `formPerm_rotate`.
-/
/-
**List.formPerm** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：formPerm : Equiv.Perm α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A list `l : List α` can be interpreted as an `Equiv.Perm α` where each element i
n the list
is permuted to the next one, defined as `formPerm`. When we have that `Nodup l`,
we prove that `Equiv.Perm.support (formPerm l) = l.toFinset`, and that
`formPerm l` is rotationally invariant, in `formPerm_rotate`.
-/
def formPerm : Equiv.Perm α :=
  (zipWith Equiv.swap l l.tail).prod

@[simp]
/-
**List.formPerm_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_nil : formPerm ([] : List α) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem formPerm_nil : formPerm ([] : List α) = 1 :=
  rfl

@[simp]
/-
**List.formPerm_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_singleton (x : α) : formPerm [x] = 1
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem formPerm_singleton (x : α) : formPerm [x] = 1 :=
  rfl

@[simp]
/-
**List.formPerm_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_cons_cons (x y : α) (l : List α) : formPerm (x :: y :: l) = Equiv
.swap x y * formPerm (y :: l)
参数：x y : α；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem formPerm_cons_cons (x y : α) (l : List α) :
    formPerm (x :: y :: l) = Equiv.swap x y * formPerm (y :: l) :=
  rfl
/-
**List.formPerm_pair** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_pair (x y : α) : formPerm [x, y] = Equiv.swap x y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem formPerm_pair (x y : α) : formPerm [x, y] = Equiv.swap x y :=
  rfl
/-
**List.mem_or_mem_of_zipWith_swap_prod_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_or_mem_of_zipWith_swap_prod_ne : forall {l l' : List α} {x : α}, (zipW
ith Equiv.swap l l').prod x != x -> x in l ∨ x in l' | [], _, _ => by simp | _, 
[], _ => by simp | a::l, b::l', x => fun hx => if h : (zipWith Equiv.swap l l').
prod x = x then (eq_or_eq_of_swap_apply_ne_self (a
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_or_mem_of_zipWith_swap_prod_ne : ∀ {l l' : List α} {x : α},
    (zipWith Equiv.swap l l').prod x ≠ x → x ∈ l ∨ x ∈ l'
  | [], _, _ => by simp
  | _, [], _ => by simp
  | a::l, b::l', x => fun hx ↦
    if h : (zipWith Equiv.swap l l').prod x = x then
      (eq_or_eq_of_swap_apply_ne_self (a := a) (b := b) (x := x) (by simpa [h] using hx)).imp
        (by rintro rfl; exact .head _) (by rintro rfl; exact .head _)
    else
     (mem_or_mem_of_zipWith_swap_prod_ne h).imp (.tail _) (.tail _)
/-
**List.zipWith_swap_prod_support'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipWith_swap_prod_support' (l l' : List α) : { x | (zipWith Equiv.swap l l
').prod x != x } <= l.toFinset ⊔ l'.toFinset
参数：l l' : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `List.mem_or_mem_of_zipWith_swap_prod_ne`：mem_or_mem_of_zipWith_swap_prod
_ne : forall {l l' : List α} {x : α}, (zipWith Equiv.swap l l').prod x != x -> x
 in l ∨ x in l' | [], _, _ =>…
-/
theorem zipWith_swap_prod_support' (l l' : List α) :
    { x | (zipWith Equiv.swap l l').prod x ≠ x } ≤ l.toFinset ⊔ l'.toFinset := fun _ h ↦ by
  simpa using mem_or_mem_of_zipWith_swap_prod_ne h
/-
**List.zipWith_swap_prod_support** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：zipWith_swap_prod_support [Fintype α] (l l' : List α) : (zipWith Equiv.swa
p l l').prod.support <= l.toFinset ⊔ l'.toFinset
参数：l l' : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `List.zipWith_swap_prod_support'`：zipWith_swap_prod_support' (l l' : List
 α) : { x | (zipWith Equiv.swap l l').prod x != x } <= l.toFinset ⊔ l'.toFinset
-/
theorem zipWith_swap_prod_support [Fintype α] (l l' : List α) :
    (zipWith Equiv.swap l l').prod.support ≤ l.toFinset ⊔ l'.toFinset := by
  intro x hx
  have hx' : x ∈ { x | (zipWith Equiv.swap l l').prod x ≠ x } := by simpa using hx
  simpa using zipWith_swap_prod_support' _ _ hx'
/-
**List.support_formPerm_le'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：support_formPerm_le' : { x | formPerm l x != x } <= l.toFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `List.zipWith_swap_prod_support'`：zipWith_swap_prod_support' (l l' : List
 α) : { x | (zipWith Equiv.swap l l').prod x != x } <= l.toFinset ⊔ l'.toFinset
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `List.tail_subset`：tail_subset (l : List α) : tail l subseteq l
-/
theorem support_formPerm_le' : { x | formPerm l x ≠ x } ≤ l.toFinset := by
  refine (zipWith_swap_prod_support' l l.tail).trans ?_
  simpa [Finset.subset_iff] using! tail_subset l
/-
**List.support_formPerm_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：support_formPerm_le [Fintype α] : support (formPerm l) <= l.toFinset
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `List.support_formPerm_le'`：support_formPerm_le' : { x | formPerm l x != 
x } <= l.toFinset
-/
theorem support_formPerm_le [Fintype α] : support (formPerm l) ≤ l.toFinset := by
  intro x hx
  have hx' : x ∈ { x | formPerm l x ≠ x } := by simpa using hx
  simpa using support_formPerm_le' _ hx'

variable {l} {x : α}
/-
**List.mem_of_formPerm_apply_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_of_formPerm_apply_ne (h : l.formPerm x != x) : x in l
参数：h : l.formPerm x != x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_iff_left_of_imp`：∀ {b a : Prop}, (b → a) → (a ∨ b ↔ a)
· 使用定理 `List.mem_of_mem_tail`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l.tail 
→ a ∈ l
· 使用定理 `List.mem_or_mem_of_zipWith_swap_prod_ne`：mem_or_mem_of_zipWith_swap_prod
_ne : forall {l l' : List α} {x : α}, (zipWith Equiv.swap l l').prod x != x -> x
 in l ∨ x in l' | [], _, _ =>…
-/
theorem mem_of_formPerm_apply_ne (h : l.formPerm x ≠ x) : x ∈ l := by
  simpa [or_iff_left_of_imp mem_of_mem_tail] using mem_or_mem_of_zipWith_swap_prod_ne h
/-
**List.formPerm_apply_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_of_notMem (h : x ∉ l) : formPerm l x = x
参数：h : x ∉ l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `List.mem_of_formPerm_apply_ne`：mem_of_formPerm_apply_ne (h : l.formPerm 
x != x) : x in l
-/
theorem formPerm_apply_of_notMem (h : x ∉ l) : formPerm l x = x :=
  not_imp_comm.1 mem_of_formPerm_apply_ne h
/-
**List.formPerm_apply_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_mem_of_mem (h : x in l) : formPerm l x in l
参数：h : x in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.formPerm_cons_cons`：formPerm_cons_cons (x y : α) (l : List α) : for
mPerm (x :: y :: l) = Equiv.swap x y * formPerm (y :: l)
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Equiv.swap_apply_def`：swap_apply_def (a b x : α) : swap a b x = if x = a
 then b else if x = b then a else x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.formPerm_apply_of_notMem`：formPerm_apply_of_notMem (h : x ∉ l) : fo
rmPerm l x = x
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
-/
theorem formPerm_apply_mem_of_mem (h : x ∈ l) : formPerm l x ∈ l := by
  rcases l with - | ⟨y, l⟩
  · simp at h
  induction l generalizing x y with
  | nil => simpa using h
  | cons z l IH =>
    by_cases hx : x ∈ z :: l
    · rw [formPerm_cons_cons, mul_apply, swap_apply_def]
      split_ifs
      · simp
      · simp
      · simp [*]
    · replace h : x = y := Or.resolve_right (mem_cons.1 h) hx
      simp [formPerm_apply_of_notMem hx, ← h]
/-
**List.mem_of_formPerm_apply_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_of_formPerm_apply_mem (h : l.formPerm x in l) : x in l
参数：h : l.formPerm x in l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.formPerm_apply_of_notMem`：formPerm_apply_of_notMem (h : x ∉ l) : fo
rmPerm l x = x
-/
theorem mem_of_formPerm_apply_mem (h : l.formPerm x ∈ l) : x ∈ l := by
  contrapose h
  rwa [formPerm_apply_of_notMem h]

@[simp]
/-
**List.formPerm_mem_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_mem_iff_mem : l.formPerm x in l ↔ x in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.mem_of_formPerm_apply_mem`：mem_of_formPerm_apply_mem (h : l.formPer
m x in l) : x in l
· 使用定理 `List.formPerm_apply_mem_of_mem`：formPerm_apply_mem_of_mem (h : x in l) :
 formPerm l x in l
-/
theorem formPerm_mem_iff_mem : l.formPerm x ∈ l ↔ x ∈ l :=
  ⟨l.mem_of_formPerm_apply_mem, l.formPerm_apply_mem_of_mem⟩

@[simp]
/-
**List.formPerm_cons_concat_apply_last** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_cons_concat_apply_last (x y : α) (xs : List α) : formPerm (x :: (
xs ++ [y])) y = x
参数：x y : α；xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem formPerm_cons_concat_apply_last (x y : α) (xs : List α) :
    formPerm (x :: (xs ++ [y])) y = x := by
  induction xs generalizing x y with
  | nil => simp
  | cons z xs IH => simp [IH]

@[simp]
/-
**List.formPerm_apply_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_getLast (x : α) (xs : List α) : formPerm (x :: xs) ((x :: x
s).getLast (cons_ne_nil x xs)) = x
参数：x : α；xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
· 使用定理 `List.getLast_append_of_ne_nil`：∀ {α : Type u_1} {l' l : List α} (h₁ : l 
++ l' ≠ []) (h₂ : l' ≠ []), (l ++ l').getLast h₁ = l'.getLast h₂
· 使用定理 `List.formPerm_cons_concat_apply_last`：formPerm_cons_concat_apply_last (x
 y : α) (xs : List α) : formPerm (x :: (xs ++ [y])) y = x
-/
theorem formPerm_apply_getLast (x : α) (xs : List α) :
    formPerm (x :: xs) ((x :: xs).getLast (cons_ne_nil x xs)) = x := by
  induction xs using List.reverseRecOn generalizing x <;> simp

@[simp]
/-
**List.formPerm_apply_getElem_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_getElem_length (x : α) (xs : List α) : formPerm (x :: xs) (
x :: xs)[xs.length] = x
参数：x : α；xs : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_cons_length`：∀ {α : Type u_1} {x : α} {xs : List α} {i : ℕ}
 (h : i = xs.length), (x :: xs)[i] = (x :: xs).getLast ⋯
· 使用定理 `List.formPerm_apply_getLast`：formPerm_apply_getLast (x : α) (xs : List α
) : formPerm (x :: xs) ((x :: xs).getLast (cons_ne_nil x xs)) = x
-/
theorem formPerm_apply_getElem_length (x : α) (xs : List α) :
    formPerm (x :: xs) (x :: xs)[xs.length] = x := by
  rw [getElem_cons_length rfl, formPerm_apply_getLast]
/-
**List.formPerm_apply_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_head (x y : α) (xs : List α) (h : Nodup (x :: y :: xs)) : f
ormPerm (x :: y :: xs) x = y
参数：x y : α；xs : List α；h : Nodup (x :: y :: xs)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.formPerm_apply_of_notMem`：formPerm_apply_of_notMem (h : x ∉ l) : fo
rmPerm l x = x
· 使用定理 `List.Nodup.notMem`：∀ {α : Type u} {l : List α} {a : α}, (a :: l).Nodup →
 a ∉ l
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem formPerm_apply_head (x y : α) (xs : List α) (h : Nodup (x :: y :: xs)) :
    formPerm (x :: y :: xs) x = y := by simp [formPerm_apply_of_notMem h.notMem]
/-
**List.formPerm_apply_getElem_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_getElem_zero (l : List α) (h : Nodup l) (hl : 1 < l.length)
 : formPerm l l[0] = l[1]
参数：l : List α；h : Nodup l；hl : 1 < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.getElem_cons_zero`：∀ {α : Type u_1} (a : α) (as : List α) (h : 0 < 
(a :: as).length), (a :: as)[0] = a
· 使用定理 `List.formPerm_apply_head`：formPerm_apply_head (x y : α) (xs : List α) (h
 : Nodup (x :: y :: xs)) : formPerm (x :: y :: xs) x = y
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `List.getElem_cons_succ`：∀ {α : Type u_1} (a : α) (as : List α) (i : ℕ) (
h : i + 1 < (a :: as).length), (a :: as)[i + 1] = as[i]
-/
theorem formPerm_apply_getElem_zero (l : List α) (h : Nodup l) (hl : 1 < l.length) :
    formPerm l l[0] = l[1] := by
  rcases l with (_ | ⟨x, _ | ⟨y, tl⟩⟩)
  · simp at hl
  · simp at hl
  · rw [getElem_cons_zero, formPerm_apply_head _ _ _ h, getElem_cons_succ, getElem_cons_zero]

variable (l)
/-
**List.formPerm_eq_head_iff_eq_getLast** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_eq_head_iff_eq_getLast (x y : α) : formPerm (y :: l) x = y ↔ x = 
getLast (y :: l) (cons_ne_nil _ _)
参数：x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.formPerm_apply_getLast`：formPerm_apply_getLast (x : α) (xs : List α
) : formPerm (x :: xs) ((x :: xs).getLast (cons_ne_nil x xs)) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem formPerm_eq_head_iff_eq_getLast (x y : α) :
    formPerm (y :: l) x = y ↔ x = getLast (y :: l) (cons_ne_nil _ _) :=
  Iff.trans (by rw [formPerm_apply_getLast]) (formPerm (y :: l)).injective.eq_iff
/-
**List.formPerm_apply_lt_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_lt_getElem (xs : List α) (h : Nodup xs) (n : Nat) (hn : n +
 1 < xs.length) : formPerm xs xs[n] = xs[n + 1]
参数：xs : List α；h : Nodup xs；n : Nat；hn : n + 1 < xs.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.formPerm_apply_getElem_zero`：formPerm_apply_getElem_zero (l : List 
α) (h : Nodup l) (hl : 1 < l.length) : formPerm l l[0] = l[1]
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `List.formPerm_singleton`：formPerm_singleton (x : α) : formPerm [x] = 1
· 使用定理 `List.getElem_singleton`：∀ {α : Type u_1} {a : α} {i : ℕ} (h : i < 1), [a
][i] = a
· 使用定理 `Equiv.Perm.one_apply`：one_apply (x) : (1 : Perm α) x = x
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Nodup.of_cons`：∀ {α : Type u} {l : List α} {a : α}, (a :: l).Nodup 
→ l.Nodup
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem formPerm_apply_lt_getElem (xs : List α) (h : Nodup xs) (n : ℕ) (hn : n + 1 < xs.length) :
    formPerm xs xs[n] = xs[n + 1] := by
  induction n generalizing xs with
  | zero => simpa using formPerm_apply_getElem_zero _ h _
  | succ n IH =>
    rcases xs with (_ | ⟨x, _ | ⟨y, l⟩⟩)
    · simp at hn
    · rw [formPerm_singleton, getElem_singleton, getElem_singleton, one_apply]
    · specialize IH (y :: l) h.of_cons _
      · simpa [Nat.succ_lt_succ_iff] using hn
      simp only [swap_apply_eq_iff, coe_mul, formPerm_cons_cons, Function.comp]
      simp only [getElem_cons_succ] at *
      rw [← IH, swap_apply_of_ne_of_ne] <;>
      · intro hx
        rw [← hx, IH] at h
        simp [getElem_mem] at h
/-
**List.formPerm_apply_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_getElem (xs : List α) (w : Nodup xs) (i : Nat) (h : i < xs.
length) : formPerm xs xs[i] = xs[(i + 1) % xs.length]'(Nat.mod_lt _ (i.zero_le.t
rans_lt h))
参数：xs : List α；w : Nodup xs；i : Nat；h : i < xs.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.formPerm_apply_getElem_length`：formPerm_apply_getElem_length (x : α
) (xs : List α) : formPerm (x :: xs) (x :: xs)[xs.length] = x
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `List.formPerm_apply_lt_getElem`：formPerm_apply_lt_getElem (xs : List α) 
(h : Nodup xs) (n : Nat) (hn : n + 1 < xs.length) : formPerm xs xs[n] = xs[n + 1
]
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
theorem formPerm_apply_getElem (xs : List α) (w : Nodup xs) (i : ℕ) (h : i < xs.length) :
    formPerm xs xs[i] =
      xs[(i + 1) % xs.length]'(Nat.mod_lt _ (i.zero_le.trans_lt h)) := by
  rcases xs with - | ⟨x, xs⟩
  · simp at h
  · have : i ≤ xs.length := by
      refine Nat.le_of_lt_succ ?_
      simpa using h
    rcases this.eq_or_lt with (rfl | hn')
    · simp
    · rw [formPerm_apply_lt_getElem (x :: xs) w _ (Nat.succ_lt_succ hn')]
      congr
      rw [Nat.mod_eq_of_lt]; simpa [Nat.succ_eq_add_one]
/-
**List.support_formPerm_of_nodup'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：support_formPerm_of_nodup' (l : List α) (h : Nodup l) (h' : forall x : α, 
l != [x]) : { x | formPerm l x != x } = l.toFinset
参数：l : List α；h : Nodup l；h' : forall x : α, l != [x]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `List.support_formPerm_le'`：support_formPerm_le' : { x | formPerm l x != 
x } <= l.toFinset
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `List.formPerm_apply_getElem`：formPerm_apply_getElem (xs : List α) (w : N
odup xs) (i : Nat) (h : i < xs.length) : formPerm xs xs[i] = xs[(i + 1) % xs.len
gth]'(Nat.mod_lt …
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_eq_one_iff`：∀ {α : Type u_1} {l : List α}, l.length = 1 ↔ ∃ 
a, l = [a]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `Fin.mk.inj_iff`：∀ {n a b : ℕ} {ha : a < n} {hb : b < n}, ⟨a, ha⟩ = ⟨b, h
b⟩ ↔ a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Function.Injective.eq_1`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), Fu
nction.Injective f = ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
· 使用定理 `List.nodup_iff_injective_get`：nodup_iff_injective_get {l : List α} : Nod
up l ↔ Function.Injective l.get
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Fin.mk.injEq`：∀ {n : ℕ} (val : ℕ) (isLt : val < n) (val_1 : ℕ) (isLt_1 :
 val_1 < n), (⟨val, isLt⟩ = ⟨val_1, isLt_1⟩) = (val = val_1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem support_formPerm_of_nodup' (l : List α) (h : Nodup l) (h' : ∀ x : α, l ≠ [x]) :
    { x | formPerm l x ≠ x } = l.toFinset := by
  apply _root_.le_antisymm
  · exact support_formPerm_le' l
  · intro x hx
    simp only [Finset.mem_coe, mem_toFinset] at hx
    obtain ⟨n, hn, rfl⟩ := getElem_of_mem hx
    rw [Set.mem_ofPred_eq, formPerm_apply_getElem _ h]
    intro H
    rw [nodup_iff_injective_get, Function.Injective] at h
    specialize h H
    rcases (Nat.succ_le_of_lt hn).eq_or_lt with hn' | hn'
    · simp only [← hn', Nat.mod_self] at h
      refine not_exists.mpr h' ?_
      rw [← length_eq_one_iff, ← hn', (Fin.mk.inj_iff.mp h).symm]
    · simp [Nat.mod_eq_of_lt hn'] at h
/-
**List.support_formPerm_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：support_formPerm_of_nodup [Fintype α] (l : List α) (h : Nodup l) (h' : for
all x : α, l != [x]) : support (formPerm l) = l.toFinset
参数：l : List α；h : Nodup l；h' : forall x : α, l != [x]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.support_formPerm_of_nodup'`：support_formPerm_of_nodup' (l : List α)
 (h : Nodup l) (h' : forall x : α, l != [x]) : { x | formPerm l x != x } = l.toF
inset
-/
theorem support_formPerm_of_nodup [Fintype α] (l : List α) (h : Nodup l) (h' : ∀ x : α, l ≠ [x]) :
    support (formPerm l) = l.toFinset := by
  rw [← Finset.coe_inj]
  convert! support_formPerm_of_nodup' _ h h'
  simp [Set.ext_iff]
/-
**List.formPerm_rotate_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_rotate_one (l : List α) (h : Nodup l) : formPerm (l.rotate 1) = f
ormPerm l
参数：l : List α；h : Nodup l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.formPerm_apply_getElem`：formPerm_apply_getElem (xs : List α) (w : N
odup xs) (i : Nat) (h : i < xs.length) : formPerm xs xs[i] = xs[(i + 1) % xs.len
gth]'(Nat.mod_lt …
· 使用定理 `List.length_rotate`：length_rotate (l : List α) (n : Nat) : (l.rotate n).
length = l.length
· 使用定理 `List.getElem_rotate`：getElem_rotate (l : List α) (n : Nat) (k : Nat) (h 
: k < (l.rotate n).length) : (l.rotate n)[k] = l[(k + n) % l.length]'(mod_lt _ (
length_ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.formPerm_apply_of_notMem`：formPerm_apply_of_notMem (h : x ∉ l) : fo
rmPerm l x = x
-/
theorem formPerm_rotate_one (l : List α) (h : Nodup l) : formPerm (l.rotate 1) = formPerm l := by
  have h' : Nodup (l.rotate 1) := by simpa using h
  ext x
  by_cases hx : x ∈ l.rotate 1
  · obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
    rw [formPerm_apply_getElem _ h', getElem_rotate l, getElem_rotate l, formPerm_apply_getElem _ h]
    simp
  · rw [formPerm_apply_of_notMem hx, formPerm_apply_of_notMem]
    simpa using hx
/-
**List.formPerm_rotate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_rotate (l : List α) (h : Nodup l) (n : Nat) : formPerm (l.rotate 
n) = formPerm l
参数：l : List α；h : Nodup l；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.rotate_zero`：rotate_zero (l : List α) : l.rotate 0 = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.rotate_rotate`：rotate_rotate (l : List α) (n m : Nat) : (l.rotate n
).rotate m = l.rotate (n + m)
· 使用定理 `List.formPerm_rotate_one`：formPerm_rotate_one (l : List α) (h : Nodup l)
 : formPerm (l.rotate 1) = formPerm l
· 使用定理 `List.IsRotated.nodup_iff`：∀ {α : Type u} {l l' : List α}, l ~r l' → (l.N
odup ↔ l'.Nodup)
· 使用定理 `List.IsRotated.forall`：∀ {α : Type u} (l : List α) (n : ℕ), l.rotate n ~
r l
-/
theorem formPerm_rotate (l : List α) (h : Nodup l) (n : ℕ) :
    formPerm (l.rotate n) = formPerm l := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [← rotate_rotate, formPerm_rotate_one, hn]
    rwa [IsRotated.nodup_iff]
    exact IsRotated.forall l n
/-
**List.formPerm_eq_of_isRotated** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_eq_of_isRotated {l l' : List α} (hd : Nodup l) (h : l ~r l') : fo
rmPerm l = formPerm l'
参数：hd : Nodup l；h : l ~r l'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.formPerm_rotate`：formPerm_rotate (l : List α) (h : Nodup l) (n : Na
t) : formPerm (l.rotate n) = formPerm l
-/
theorem formPerm_eq_of_isRotated {l l' : List α} (hd : Nodup l) (h : l ~r l') :
    formPerm l = formPerm l' := by
  obtain ⟨n, rfl⟩ := h
  exact (formPerm_rotate l hd n).symm
/-
**List.formPerm_append_pair** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (a b : α),   (l ++ [a
, b]).formPerm = (l ++ [a]).formPerm * Equiv.swap a b
参数：l : List α；a b : α；l ++ [a, b]；l ++ [a]。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem formPerm_append_pair : ∀ (l : List α) (a b : α),
    formPerm (l ++ [a, b]) = formPerm (l ++ [a]) * Equiv.swap a b
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | x::y::l, a, b => by
    simpa [mul_assoc] using formPerm_append_pair (y::l) a b
/-
**List.formPerm_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α), l.reverse.formPerm =
 l.formPerm⁻¹
参数：l : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem formPerm_reverse : ∀ l : List α, formPerm l.reverse = (formPerm l)⁻¹
  | [] => rfl
  | [_] => rfl
  | a::b::l => by
    simp [formPerm_append_pair, Equiv.swap_comm, ← formPerm_reverse (b::l)]
/-
**List.formPerm_pow_apply_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_pow_apply_getElem (l : List α) (w : Nodup l) (n : Nat) (i : Nat) 
(h : i < l.length) : (formPerm l ^ n) l[i] = l[(i + n) % l.length]'(Nat.mod_lt _
 (i.zero_le.trans_lt h))
参数：l : List α；w : Nodup l；n : Nat；i : Nat；h : i < l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `List.formPerm_apply_getElem`：formPerm_apply_getElem (xs : List α) (w : N
odup xs) (i : Nat) (h : i < xs.length) : formPerm xs xs[i] = xs[(i + 1) % xs.len
gth]'(Nat.mod_lt …
-/
theorem formPerm_pow_apply_getElem (l : List α) (w : Nodup l) (n : ℕ) (i : ℕ) (h : i < l.length) :
    (formPerm l ^ n) l[i] =
      l[(i + n) % l.length]'(Nat.mod_lt _ (i.zero_le.trans_lt h)) := by
  induction n with
  | zero => simp [Nat.mod_eq_of_lt h]
  | succ n hn =>
    simp [pow_succ', mul_apply, hn, formPerm_apply_getElem _ w,
      ← Nat.add_assoc]
/-
**List.formPerm_pow_apply_head** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_pow_apply_head (x : α) (l : List α) (h : Nodup (x :: l)) (n : Nat
) : (formPerm (x :: l) ^ n) x = (x :: l)[(n % (x :: l).length)]'(Nat.mod_lt _ (N
at.zero_lt_succ _))
参数：x : α；l : List α；h : Nodup (x :: l)；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `Nat.zero_lt_succ`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.formPerm_pow_apply_getElem`：formPerm_pow_apply_getElem (l : List α)
 (w : Nodup l) (n : Nat) (i : Nat) (h : i < l.length) : (formPerm l ^ n) l[i] = 
l[(i + n) % l.length]…
-/
theorem formPerm_pow_apply_head (x : α) (l : List α) (h : Nodup (x :: l)) (n : ℕ) :
    (formPerm (x :: l) ^ n) x =
      (x :: l)[(n % (x :: l).length)]'(Nat.mod_lt _ (Nat.zero_lt_succ _)) := by
  convert! formPerm_pow_apply_getElem _ h n 0 (Nat.succ_pos _)
  simp
/-
**List.formPerm_ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_ext_iff {x y x' y' : α} {l l' : List α} (hd : Nodup (x :: y :: l)
) (hd' : Nodup (x' :: y' :: l')) : formPerm (x :: y :: l) = formPerm (x' :: y' :
: l') ↔ (x :: y :: l) ~r (x' :: y' :: l')
参数：hd : Nodup (x :: y :: l)；hd' : Nodup (x' :: y' :: l')。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Equiv.Perm.ext_iff`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, σ = τ ↔ ∀ (x : 
α), σ x = τ x
· 使用定理 `List.formPerm_apply_head`：formPerm_apply_head (x y : α) (xs : List α) (h
 : Nodup (x :: y :: xs)) : formPerm (x :: y :: xs) x = y
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.toFinset_cons`：toFinset_cons : toFinset (a :: l) = insert a (toFins
et l)
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `List.support_formPerm_le'`：support_formPerm_le' : { x | formPerm l x != 
x } <= l.toFinset
· 使用定理 `List.get_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ n, l.g
et n = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.dedup_eq_self`：dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l
· 使用定理 `List.card_toFinset`：List.card_toFinset : #l.toFinset = l.dedup.length
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.coe_inj`：coe_inj {s₁ s₂ : Finset α} : (s₁ : Set α) = s₂ ↔ s₁ = s₂
· 使用定理 `List.support_formPerm_of_nodup'`：support_formPerm_of_nodup' (l : List α)
 (h : Nodup l) (h' : forall x : α, l != [x]) : { x | formPerm l x != x } = l.toF
inset
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 45 条，此处仅展示前 30 条）
-/
theorem formPerm_ext_iff {x y x' y' : α} {l l' : List α} (hd : Nodup (x :: y :: l))
    (hd' : Nodup (x' :: y' :: l')) :
    formPerm (x :: y :: l) = formPerm (x' :: y' :: l') ↔ (x :: y :: l) ~r (x' :: y' :: l') := by
  refine ⟨fun h => ?_, fun hr => formPerm_eq_of_isRotated hd hr⟩
  rw [Equiv.Perm.ext_iff] at h
  have hx : x' ∈ x :: y :: l := by
    have : x' ∈ { z | formPerm (x :: y :: l) z ≠ z } := by
      rw [Set.mem_ofPred_eq, h x', formPerm_apply_head _ _ _ hd']
      simp only [mem_cons, nodup_cons] at hd'
      push Not at hd'
      exact hd'.left.left.symm
    simpa using support_formPerm_le' _ this
  obtain ⟨⟨n, hn⟩, hx'⟩ := get_of_mem hx
  have hl : (x :: y :: l).length = (x' :: y' :: l').length := by
    rw [← dedup_eq_self.mpr hd, ← dedup_eq_self.mpr hd', ← card_toFinset, ← card_toFinset]
    refine congr_arg Finset.card ?_
    rw [← Finset.coe_inj, ← support_formPerm_of_nodup' _ hd (by simp), ←
      support_formPerm_of_nodup' _ hd' (by simp)]
    simp only [h]
  use n
  apply List.ext_getElem
  · rw [length_rotate, hl]
  · intro k hk hk'
    rw [getElem_rotate]
    induction k with
    | zero =>
      refine Eq.trans ?_ hx'
      congr
      simpa using hn
    | succ k IH =>
      conv => congr <;> · arg 2; (rw [← Nat.mod_eq_of_lt hk'])
      rw [← formPerm_apply_getElem _ hd' k (k.lt_succ_self.trans hk'),
        ← IH (k.lt_succ_self.trans hk), ← h, formPerm_apply_getElem _ hd]
      congr 1
      rw [hl, Nat.mod_eq_of_lt hk', add_right_comm]
      apply Nat.add_mod
/-
**List.formPerm_apply_mem_eq_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_mem_eq_self_iff (hl : Nodup l) (x : α) (hx : x in l) : form
Perm l x = x ↔ length l <= 1
参数：hl : Nodup l；x : α；hx : x in l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.formPerm_apply_getElem`：formPerm_apply_getElem (xs : List α) (w : N
odup xs) (i : Nat) (h : i < xs.length) : formPerm xs xs[i] = xs[(i + 1) % xs.len
gth]'(Nat.mod_lt …
· 使用定理 `List.Nodup.getElem_inj_iff`：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {i 
: ℕ} {hi : i < l.length} {j : ℕ} {hj : j < l.length}, l[i] = l[j] ↔ i = j
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
（共 34 条，此处仅展示前 30 条）
-/
theorem formPerm_apply_mem_eq_self_iff (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x = x ↔ length l ≤ 1 := by
  obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
  rw [formPerm_apply_getElem _ hl k hk, hl.getElem_inj_iff]
  cases hn : l.length
  · exact absurd k.zero_le (hk.trans_le hn.le).not_ge
  · rw [hn] at hk
    rcases (Nat.le_of_lt_succ hk).eq_or_lt with hk' | hk'
    · simp [← hk', eq_comm]
    · simpa [Nat.mod_eq_of_lt (Nat.succ_lt_succ hk'), Nat.succ_lt_succ_iff] using
        (k.zero_le.trans_lt hk').ne.symm
/-
**List.formPerm_apply_mem_ne_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_apply_mem_ne_self_iff (hl : Nodup l) (x : α) (hx : x in l) : form
Perm l x != x ↔ 2 <= l.length
参数：hl : Nodup l；x : α；hx : x in l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `List.formPerm_apply_mem_eq_self_iff`：formPerm_apply_mem_eq_self_iff (hl 
: Nodup l) (x : α) (hx : x in l) : formPerm l x = x ↔ length l <= 1
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `Nat.lt_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n < m
-/
theorem formPerm_apply_mem_ne_self_iff (hl : Nodup l) (x : α) (hx : x ∈ l) :
    formPerm l x ≠ x ↔ 2 ≤ l.length := by
  rw [Ne, formPerm_apply_mem_eq_self_iff _ hl x hx, not_le]
  exact ⟨Nat.succ_le_of_lt, Nat.lt_of_succ_le⟩
/-
**List.formPerm_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_eq_one_iff (hl : Nodup l) : formPerm l = 1 ↔ l.length <= 1
参数：hl : Nodup l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.formPerm_apply_mem_eq_self_iff`：formPerm_apply_mem_eq_self_iff (hl 
: Nodup l) (x : α) (hx : x in l) : formPerm l x = x ↔ length l <= 1
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
theorem formPerm_eq_one_iff (hl : Nodup l) : formPerm l = 1 ↔ l.length ≤ 1 := by
  rcases l with - | ⟨hd, tl⟩
  · simp
  · rw [← formPerm_apply_mem_eq_self_iff _ hl hd mem_cons_self]
    constructor
    · simp +contextual
    · intro h
      simp only [(hd :: tl).formPerm_apply_mem_eq_self_iff hl hd mem_cons_self,
        add_le_iff_nonpos_left, length, nonpos_iff_eq_zero, length_eq_zero_iff] at h
      simp [h]
/-
**List.formPerm_eq_formPerm_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_eq_formPerm_iff {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup) :
 l.formPerm = l'.formPerm ↔ l ~r l' ∨ l.length <= 1 ∧ l'.length <= 1
参数：hl : l.Nodup；hl' : l'.Nodup。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length
· 使用定理 `List.IsRotated.perm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l.Perm l'
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `List.formPerm_eq_one_iff`：formPerm_eq_one_iff (hl : Nodup l) : formPerm 
l = 1 ↔ l.length <= 1
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `List.formPerm_ext_iff`：formPerm_ext_iff {x y x' y' : α} {l l' : List α} 
(hd : Nodup (x :: y :: l)) (hd' : Nodup (x' :: y' :: l')) : formPerm (x :: y :: 
l) = formPe…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
（共 31 条，此处仅展示前 30 条）
-/
theorem formPerm_eq_formPerm_iff {l l' : List α} (hl : l.Nodup) (hl' : l'.Nodup) :
    l.formPerm = l'.formPerm ↔ l ~r l' ∨ l.length ≤ 1 ∧ l'.length ≤ 1 := by
  rcases l with (_ | ⟨x, _ | ⟨y, l⟩⟩)
  · suffices l'.length ≤ 1 ↔ l' = nil ∨ l'.length ≤ 1 by
      simpa [eq_comm, formPerm_eq_one_iff, hl, hl', length_eq_zero_iff]
    refine ⟨fun h => Or.inr h, ?_⟩
    rintro (rfl | h)
    · simp
    · exact h
  · suffices l'.length ≤ 1 ↔ [x] ~r l' ∨ l'.length ≤ 1 by
      simpa [eq_comm, formPerm_eq_one_iff, hl, hl', length_eq_zero_iff, le_rfl]
    refine ⟨fun h => Or.inr h, ?_⟩
    rintro (h | h)
    · simp [← h.perm.length_eq]
    · exact h
  · rcases l' with (_ | ⟨x', _ | ⟨y', l'⟩⟩)
    · simp [formPerm_eq_one_iff _ hl, -formPerm_cons_cons]
    · simp [formPerm_eq_one_iff _ hl, -formPerm_cons_cons]
    · simp [-formPerm_cons_cons, formPerm_ext_iff hl hl']
/-
**List.form_perm_zpow_apply_mem_imp_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：form_perm_zpow_apply_mem_imp_mem (l : List α) (x : α) (hx : x in l) (n : I
nt) : (formPerm l ^ n) x in l
参数：l : List α；x : α；hx : x in l；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.set_support_zpow_subset`：set_support_zpow_subset (n : Int) : 
{ x | (p ^ n) x != x } subseteq { x | p x != x }
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.set_support_apply_mem`：set_support_apply_mem {p : Perm α} {a 
: α} : p a in { x | p x != x } ↔ a in { x | p x != x }
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `List.support_formPerm_le'`：support_formPerm_le' : { x | formPerm l x != 
x } <= l.toFinset
-/
theorem form_perm_zpow_apply_mem_imp_mem (l : List α) (x : α) (hx : x ∈ l) (n : ℤ) :
    (formPerm l ^ n) x ∈ l := by
  by_cases h : (l.formPerm ^ n) x = x
  · simpa [h] using hx
  · have h : x ∈ { x | (l.formPerm ^ n) x ≠ x } := h
    rw [← set_support_apply_mem] at h
    replace h := set_support_zpow_subset _ _ h
    simpa using support_formPerm_le' _ h
/-
**List.formPerm_pow_length_eq_one_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：formPerm_pow_length_eq_one_of_nodup (hl : Nodup l) : formPerm l ^ length l
 = 1
参数：hl : Nodup l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.add_mod_right`：∀ (x z : ℕ), (x + z) % z = x % z
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.formPerm_pow_apply_getElem`：formPerm_pow_apply_getElem (l : List α)
 (w : Nodup l) (n : Nat) (i : Nat) (h : i < l.length) : (formPerm l ^ n) l[i] = 
l[(i + n) % l.length]…
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.set_support_zpow_subset`：set_support_zpow_subset (n : Int) : 
{ x | (p ^ n) x != x } subseteq { x | p x != x }
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `List.support_formPerm_le'`：support_formPerm_le' : { x | formPerm l x != 
x } <= l.toFinset
-/
theorem formPerm_pow_length_eq_one_of_nodup (hl : Nodup l) : formPerm l ^ length l = 1 := by
  ext x
  by_cases hx : x ∈ l
  · obtain ⟨k, hk, rfl⟩ := getElem_of_mem hx
    simp [formPerm_pow_apply_getElem _ hl, Nat.mod_eq_of_lt hk]
  · have : x ∉ { x | (l.formPerm ^ l.length) x ≠ x } := by
      intro H
      refine hx ?_
      replace H := set_support_zpow_subset l.formPerm l.length H
      simpa using support_formPerm_le' _ H
    simpa using this

end FormPerm

end List

