/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Pairwise
public import Mathlib.Logic.Function.Iterate

/-!
# Relation chain

This file provides basic results about `List.IsChain` from Batteries.
A list `[a₁, a₂, ..., aₙ]` satisfies `IsChain` with respect to the relation `r` if `r a₁ a₂`
and `r a₂ a₃` and ... and `r aₙ₋₁ aₙ`. We write it `IsChain r [a₁, a₂, ..., aₙ]`.
A graph-specialized version is in development and will hopefully be added under `combinatorics.`
sometime soon.
-/

public section

assert_not_imported Mathlib.Algebra.Order.Group.Nat

open Nat

variable {α β : Type*} {R r : α → α → Prop} {l l₁ l₂ : List α} {a b : α}

namespace List

mk_iff_of_inductive_prop List.IsChain List.isChain_iff

/-
**List.isChain_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_nil : IsChain R []
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_nil : IsChain R [] := .nil
/-
**List.isChain_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_singleton (a : α) : IsChain R [a]
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_singleton (a : α) : IsChain R [a] := .singleton _
/-
**List.isChain_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_iff (R : α -> α -> Prop) (a : α) (l : List α) : IsChain R (a 
:: l) ↔ l = [] ∨ exists (b : α) (l' : List α), R a b ∧ IsChain R (b :: l') ∧ l =
 b :: l'
参数：R : α -> α -> Prop；a : α；l : List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.isChain_iff`：∀ {α : Type u_1} (R : α → α → Prop) (a : List α),   Li
st.IsChain R a ↔ a = [] ∨ (∃ a_1, a = [a_1]) ∨ ∃ a_1 b l, R a_1 b ∧ List.IsChain
 R (b …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem isChain_cons_iff (R : α → α → Prop) (a : α) (l : List α) :
    IsChain R (a :: l) ↔ l = [] ∨
      ∃ (b : α) (l' : List α), R a b ∧ IsChain R (b :: l') ∧ l = b :: l' :=
  (isChain_iff _ _).trans <| by
    simp only [cons_ne_nil, List.cons_eq_cons, exists_and_right,
      exists_eq', true_and, exists_and_left, false_or]
    grind
/-
**List.IsChain.imp_of_mem_tail_imp** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α},   (∀ (a b : α), a ∈ l 
→ b ∈ l.tail → R a b → S a b) → List.IsChain R l → List.IsChain S l
参数：∀ (a b : α), a ∈ l → b ∈ l.tail → R a b → S a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsChain.imp_of_mem_tail_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l.tail → R a b → S a b) (p : IsChain R l) : IsChain S l := by
  induction p with grind
/-
**List.IsChain.imp_of_mem_imp** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α},   (∀ (a b : α), a ∈ l 
→ b ∈ l → R a b → S a b) → List.IsChain R l → List.IsChain S l
参数：∀ (a b : α), a ∈ l → b ∈ l → R a b → S a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.imp_of_mem_tail_imp`：∀ {α : Type u_1} {R S : α → α → Prop} 
{l : List α},   (∀ (a b : α), a ∈ l → b ∈ l.tail → R a b → S a b) → List.IsChain
 R l → List.IsChain S …
· 使用定理 `List.mem_of_mem_tail`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l.tail 
→ a ∈ l
-/
theorem IsChain.imp_of_mem_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l → R a b → S a b) (p : IsChain R l) : IsChain S l :=
  p.imp_of_mem_tail_imp (H · · · <| mem_of_mem_tail ·)
/-
**List.IsChain.iff** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ (a b : α), R a b ↔ S a b) → ∀ 
{l : List α}, List.IsChain R l ↔ List.IsChain S l
参数：∀ (a b : α), R a b ↔ S a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α}, (∀
 ⦃a b : α⦄, R a b → S a b) → List.IsChain R l → List.IsChain S l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsChain.iff {S : α → α → Prop} (H : ∀ a b, R a b ↔ S a b) {l : List α} :
    IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp fun a b => (H a b).1, IsChain.imp fun a b => (H a b).2⟩
/-
**List.IsChain.iff_of_mem_imp** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α},   (∀ (a b : α), a ∈ l 
→ b ∈ l → (R a b ↔ S a b)) → (List.IsChain R l ↔ List.IsChain S l)
参数：∀ (a b : α), a ∈ l → b ∈ l → (R a b ↔ S a b)；List.IsChain R l ↔ List.IsChain 
S l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.imp_of_mem_imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : 
List α},   (∀ (a b : α), a ∈ l → b ∈ l → R a b → S a b) → List.IsChain R l → Lis
t.IsChain S l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsChain.iff_of_mem_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l → (R a b ↔ S a b)) : IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp_of_mem_imp (Iff.mp <| H · · · ·), IsChain.imp_of_mem_imp (Iff.mpr <| H · · · ·)⟩
/-
**List.IsChain.iff_of_mem_tail_imp** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α},   (∀ (a b : α), a ∈ l 
→ b ∈ l.tail → (R a b ↔ S a b)) → (List.IsChain R l ↔ List.IsChain S l)
参数：∀ (a b : α), a ∈ l → b ∈ l.tail → (R a b ↔ S a b)；List.IsChain R l ↔ List.IsC
hain S l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.imp_of_mem_tail_imp`：∀ {α : Type u_1} {R S : α → α → Prop} 
{l : List α},   (∀ (a b : α), a ∈ l → b ∈ l.tail → R a b → S a b) → List.IsChain
 R l → List.IsChain S …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsChain.iff_of_mem_tail_imp {S : α → α → Prop} {l : List α}
    (H : ∀ a b : α, a ∈ l → b ∈ l.tail → (R a b ↔ S a b)) : IsChain R l ↔ IsChain S l :=
  ⟨IsChain.imp_of_mem_tail_imp (Iff.mp <| H · · · ·),
  IsChain.imp_of_mem_tail_imp (Iff.mpr <| H · · · ·)⟩
/-
**List.IsChain.iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, List.IsChain R l ↔ List.
IsChain (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l
参数：fun x y => x ∈ l ∧ y ∈ l ∧ R x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.iff_of_mem_imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : 
List α},   (∀ (a b : α), a ∈ l → b ∈ l → (R a b ↔ S a b)) → (List.IsChain R l ↔ 
List.IsChain S l)
-/
theorem IsChain.iff_mem {l : List α} :
    IsChain R l ↔ IsChain (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l :=
  IsChain.iff_of_mem_imp <| by grind
/-
**List.IsChain.iff_mem_mem_tail** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},   List.IsChain R l ↔ Lis
t.IsChain (fun x y => x ∈ l ∧ y ∈ l.tail ∧ R x y) l
参数：fun x y => x ∈ l ∧ y ∈ l.tail ∧ R x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.iff_of_mem_tail_imp`：∀ {α : Type u_1} {R S : α → α → Prop} 
{l : List α},   (∀ (a b : α), a ∈ l → b ∈ l.tail → (R a b ↔ S a b)) → (List.IsCh
ain R l ↔ List.IsChain…
-/
theorem IsChain.iff_mem_mem_tail {l : List α} :
    IsChain R l ↔ IsChain (fun x y => x ∈ l ∧ y ∈ l.tail ∧ R x y) l :=
  IsChain.iff_of_mem_tail_imp <| by grind
/-
**List.isChain_pair** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_pair {x y} : IsChain R [x, y] ↔ R x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isChain_pair {x y} : IsChain R [x, y] ↔ R x y := by
  simp only [IsChain.singleton, isChain_cons_cons, and_true]
/-
**List.isChain_isInfix** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α), List.IsChain (fun x y => [x, y] <:+: l) l
参数：l : List α；fun x y => [x, y] <:+: l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_isInfix : ∀ l : List α, IsChain (fun x y => [x, y] <:+: l) l
  | [] => .nil
  | [_] => .singleton _
  | a :: b :: l => .cons_cons ⟨[], l, by simp⟩
    ((isChain_isInfix (b :: l)).imp fun _ _ h => h.trans ⟨[a], [], by simp⟩)
/-
**List.isChain_split** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_split {c : α} {l₁ l₂ : List α} : IsChain R (l₁ ++ c :: l₂) ↔ IsCha
in R (l₁ ++ [c]) ∧ IsChain R (c :: l₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_split {c : α} {l₁ l₂ : List α} :
    IsChain R (l₁ ++ c :: l₂) ↔ IsChain R (l₁ ++ [c]) ∧ IsChain R (c :: l₂) := by
  induction l₁ using twoStepInduction generalizing l₂ with grind
/-
**List.isChain_cons_split** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_split {c : α} {l₁ l₂ : List α} : IsChain R (a :: (l₁ ++ c :: 
l₂)) ↔ IsChain R (a :: (l₁ ++ [c])) ∧ IsChain R (c :: l₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.isChain_split`：isChain_split {c : α} {l₁ l₂ : List α} : IsChain R (
l₁ ++ c :: l₂) ↔ IsChain R (l₁ ++ [c]) ∧ IsChain R (c :: l₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isChain_cons_split {c : α} {l₁ l₂ : List α} :
    IsChain R (a :: (l₁ ++ c :: l₂)) ↔ IsChain R (a :: (l₁ ++ [c])) ∧ IsChain R (c :: l₂) := by
  simp_rw [← cons_append, isChain_split (l₂ := l₂)]

@[simp]
/-
**List.isChain_append_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_append_cons_cons {b c : α} {l₁ l₂ : List α} : IsChain R (l₁ ++ b :
: c :: l₂) ↔ IsChain R (l₁ ++ [b]) ∧ R b c ∧ IsChain R (c :: l₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.isChain_split`：isChain_split {c : α} {l₁ l₂ : List α} : IsChain R (
l₁ ++ c :: l₂) ↔ IsChain R (l₁ ++ [c]) ∧ IsChain R (c :: l₂)
· 使用定理 `List.isChain_cons_cons`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l
 : List α},   List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isChain_append_cons_cons {b c : α} {l₁ l₂ : List α} :
    IsChain R (l₁ ++ b :: c :: l₂) ↔ IsChain R (l₁ ++ [b]) ∧ R b c ∧ IsChain R (c :: l₂) := by
  rw [isChain_split, isChain_cons_cons]

@[simp]
/-
**List.isChain_cons_append_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_append_cons_cons {a b c : α} {l₁ l₂ : List α} : IsChain R (a 
:: (l₁ ++ b :: c :: l₂)) ↔ IsChain R (a :: (l₁ ++ [b])) ∧ R b c ∧ IsChain R (c :
: l₂)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.isChain_cons_split`：isChain_cons_split {c : α} {l₁ l₂ : List α} : I
sChain R (a :: (l₁ ++ c :: l₂)) ↔ IsChain R (a :: (l₁ ++ [c])) ∧ IsChain R (c ::
 l₂)
· 使用定理 `List.isChain_cons_cons`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l
 : List α},   List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isChain_cons_append_cons_cons {a b c : α} {l₁ l₂ : List α} :
    IsChain R (a :: (l₁ ++ b :: c :: l₂)) ↔
    IsChain R (a :: (l₁ ++ [b])) ∧ R b c ∧ IsChain R (c :: l₂) := by
  rw [isChain_cons_split, isChain_cons_cons]
/-
**List.isChain_iff_forall_rel_of_append_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `Lis
t`。
形式化陈述：isChain_iff_forall_rel_of_append_cons_cons {l : List α} : IsChain R l ↔ fo
rall ⦃a b l₁ l₂⦄, l = l₁ ++ a :: b :: l₂ -> R a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_append_cons_cons`：isChain_append_cons_cons {b c : α} {l₁ l₂
 : List α} : IsChain R (l₁ ++ b :: c :: l₂) ↔ IsChain R (l₁ ++ [b]) ∧ R b c ∧ Is
Chain R (c :: l₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.isChain_cons_cons`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l
 : List α},   List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
-/
theorem isChain_iff_forall_rel_of_append_cons_cons {l : List α} :
    IsChain R l ↔ ∀ ⦃a b l₁ l₂⦄, l = l₁ ++ a :: b :: l₂ → R a b := by
  refine ⟨fun h _ _ _ _ eq => (isChain_append_cons_cons.mp (eq ▸ h)).2.1, ?_⟩
  induction l using twoStepInduction with
  | nil | singleton => grind
  | cons_cons head head' tail _ ih =>
    refine fun h ↦ isChain_cons_cons.mpr ⟨h (nil_append _).symm, ih _ fun ⦃a b l₁ l₂⦄ eq => ?_⟩
    apply h
    rw [eq, cons_append]
/-
**List.isChain_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_iff_forall₂ {l : List α} :
    IsChain R l ↔ Forall₂ R l.dropLast l.tail := by
  induction l using twoStepInduction <;> simp_all
/-
**List.isChain_cons_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_cons_iff_forall₂ : IsChain R (a :: l) ↔ l = [] ∨ Forall₂ R (a :: dropLast l) l := by
  cases l <;> simp [isChain_iff_forall₂]
/-
**List.isChain_cons_append_singleton_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `List`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_cons_append_singleton_iff_forall₂ :
    IsChain R (a :: l ++ [b]) ↔ Forall₂ R (a :: l) (l ++ [b]) := by
  simp_rw [isChain_iff_forall₂, dropLast_concat, cons_append, tail_cons]
/-
**List.isChain_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_map (f : β -> α) {l : List β} : IsChain R (map f l) ↔ IsChain (fun
 a b : β => R (f a) (f b)) l
参数：f : β -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_map (f : β → α) {l : List β} :
    IsChain R (map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) l := by
  induction l using twoStepInduction <;> grind
/-
**List.isChain_of_isChain_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_of_isChain_map {S : β -> β -> Prop} (f : α -> β) (H : forall a b :
 α, S (f a) (f b) -> R a b) {l : List α} (p : IsChain S (map f l)) : IsChain R l
参数：f : α -> β；H : forall a b : α, S (f a) (f b) -> R a b；p : IsChain S (map f l)
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α}, (∀
 ⦃a b : α⦄, R a b → S a b) → List.IsChain R l → List.IsChain S l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_map`：isChain_map (f : β -> α) {l : List β} : IsChain R (map
 f l) ↔ IsChain (fun a b : β => R (f a) (f b)) l
-/
theorem isChain_of_isChain_map {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, S (f a) (f b) → R a b)
    {l : List α} (p : IsChain S (map f l)) : IsChain R l :=
  ((isChain_map f).1 p).imp H
/-
**List.isChain_map_of_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_map_of_isChain {S : β -> β -> Prop} (f : α -> β) (H : forall a b :
 α, R a b -> S (f a) (f b)) {l : List α} (p : IsChain R l) : IsChain S (map f l)
参数：f : α -> β；H : forall a b : α, R a b -> S (f a) (f b)；p : IsChain R l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.isChain_map`：isChain_map (f : β -> α) {l : List β} : IsChain R (map
 f l) ↔ IsChain (fun a b : β => R (f a) (f b)) l
· 使用定理 `List.IsChain.imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α}, (∀
 ⦃a b : α⦄, R a b → S a b) → List.IsChain R l → List.IsChain S l
-/
theorem isChain_map_of_isChain {S : β → β → Prop} (f : α → β) (H : ∀ a b : α, R a b → S (f a) (f b))
    {l : List α} (p : IsChain R l) : IsChain S (map f l) :=
  (isChain_map f).2 <| p.imp H
/-
**List.isChain_cons_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_map (f : β -> α) {l : List β} {b : β} : IsChain R (f b :: map
 f l) ↔ IsChain (fun a b : β => R (f a) (f b)) (b :: l)
参数：f : β -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isChain_map`：isChain_map (f : β -> α) {l : List β} : IsChain R (map
 f l) ↔ IsChain (fun a b : β => R (f a) (f b)) l
-/
theorem isChain_cons_map (f : β → α) {l : List β} {b : β} :
    IsChain R (f b :: map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) (b :: l) :=
  isChain_map f (l := b :: l)
/-
**List.isChain_cons_of_isChain_cons_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_of_isChain_cons_map {S : β -> β -> Prop} (f : α -> β) (H : fo
rall a b : α, S (f a) (f b) -> R a b) {l : List α} (p : IsChain S (f a :: map f 
l)) : IsChain R (a :: l)
参数：f : α -> β；H : forall a b : α, S (f a) (f b) -> R a b；p : IsChain S (f a :: m
ap f l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α}, (∀
 ⦃a b : α⦄, R a b → S a b) → List.IsChain R l → List.IsChain S l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_cons_map`：isChain_cons_map (f : β -> α) {l : List β} {b : β
} : IsChain R (f b :: map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) (b :: l)
-/
theorem isChain_cons_of_isChain_cons_map {S : β → β → Prop} (f : α → β)
    (H : ∀ a b : α, S (f a) (f b) → R a b)
    {l : List α} (p : IsChain S (f a :: map f l)) : IsChain R (a :: l) :=
  ((isChain_cons_map f).1 p).imp H
/-
**List.isChain_cons_map_of_isChain_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_map_of_isChain_cons {S : β -> β -> Prop} (f : α -> β) (H : fo
rall a b : α, R a b -> S (f a) (f b)) {l : List α} (p : IsChain R (a :: l)) : Is
Chain S (f a :: map f l)
参数：f : α -> β；H : forall a b : α, R a b -> S (f a) (f b)；p : IsChain R (a :: l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.isChain_cons_map`：isChain_cons_map (f : β -> α) {l : List β} {b : β
} : IsChain R (f b :: map f l) ↔ IsChain (fun a b : β => R (f a) (f b)) (b :: l)
· 使用定理 `List.IsChain.imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α}, (∀
 ⦃a b : α⦄, R a b → S a b) → List.IsChain R l → List.IsChain S l
-/
theorem isChain_cons_map_of_isChain_cons {S : β → β → Prop} (f : α → β)
    (H : ∀ a b : α, R a b → S (f a) (f b))
    {l : List α} (p : IsChain R (a :: l)) : IsChain S (f a :: map f l) :=
  (isChain_cons_map f).2 <| p.imp H
/-
**List.isChain_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_pmap {S : β -> β -> Prop} {p : α -> Prop} (f : forall a, p a -> β)
 {l : List α} (hl : forall a in l, p a) : IsChain S (pmap f l hl) ↔ IsChain (fun
 a b => exists ha, exists hb, S (f a ha) (f b hb)) l
参数：f : forall a, p a -> β；hl : forall a in l, p a。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β) {l : List α}
    (hl : ∀ a ∈ l, p a) : IsChain S (pmap f l hl) ↔
    IsChain (fun a b => ∃ ha, ∃ hb, S (f a ha) (f b hb)) l := by
  induction l using twoStepInduction <;> grind
/-
**List.isChain_pmap_of_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_pmap_of_isChain {S : β -> β -> Prop} {p : α -> Prop} {f : forall a
, p a -> β} (H : forall a b ha hb, R a b -> S (f a ha) (f b hb)) {l : List α} (h
l₁ : IsChain R l) (hl₂ : forall a in l, p a) : IsChain S (pmap f l hl₂)
参数：H : forall a b ha hb, R a b -> S (f a ha) (f b hb)；hl₁ : IsChain R l；hl₂ : fo
rall a in l, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.isChain_pmap`：isChain_pmap {S : β -> β -> Prop} {p : α -> Prop} (f 
: forall a, p a -> β) {l : List α} (hl : forall a in l, p a) : IsChain S (pmap f
 l hl) …
· 使用定理 `List.IsChain.imp_of_mem_imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : 
List α},   (∀ (a b : α), a ∈ l → b ∈ l → R a b → S a b) → List.IsChain R l → Lis
t.IsChain S l
-/
theorem isChain_pmap_of_isChain {S : β → β → Prop} {p : α → Prop} {f : ∀ a, p a → β}
    (H : ∀ a b ha hb, R a b → S (f a ha) (f b hb)) {l : List α} (hl₁ : IsChain R l)
    (hl₂ : ∀ a ∈ l, p a) : IsChain S (pmap f l hl₂) := (isChain_pmap f _).2 <|
  hl₁.imp_of_mem_imp (by grind)
/-
**List.isChain_of_isChain_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_of_isChain_pmap {S : β -> β -> Prop} {p : α -> Prop} (f : forall a
, p a -> β) {l : List α} (hl₁ : forall a in l, p a) (hl₂ : IsChain S (pmap f l h
l₁)) (H : forall a b ha hb, S (f a ha) (f b hb) -> R a b) : IsChain R l
参数：f : forall a, p a -> β；hl₁ : forall a in l, p a；hl₂ : IsChain S (pmap f l hl₁
)；H : forall a b ha hb, S (f a ha) (f b hb) -> R a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α}, (∀
 ⦃a b : α⦄, R a b → S a b) → List.IsChain R l → List.IsChain S l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_pmap`：isChain_pmap {S : β -> β -> Prop} {p : α -> Prop} (f 
: forall a, p a -> β) {l : List α} (hl : forall a in l, p a) : IsChain S (pmap f
 l hl) …
-/
theorem isChain_of_isChain_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β) {l : List α}
    (hl₁ : ∀ a ∈ l, p a) (hl₂ : IsChain S (pmap f l hl₁))
    (H : ∀ a b ha hb, S (f a ha) (f b hb) → R a b) : IsChain R l :=
  ((isChain_pmap f _).1 hl₂).imp (by grind)
/-
**List.isChain_cons_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_pmap {p : β -> Prop} (f : forall b, p b -> α) {l : List β} (h
l : forall b in l, p b) {a} (ha) : IsChain R (f a ha :: pmap f l hl) ↔ IsChain (
fun a b => exists ha, exists hb, R (f a ha) (f b hb)) (a :: l)
参数：f : forall b, p b -> α；hl : forall b in l, p b；ha。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isChain_pmap`：isChain_pmap {S : β -> β -> Prop} {p : α -> Prop} (f 
: forall a, p a -> β) {l : List α} (hl : forall a in l, p a) : IsChain S (pmap f
 l hl) …
-/
theorem isChain_cons_pmap {p : β → Prop} (f : ∀ b, p b → α) {l : List β} (hl : ∀ b ∈ l, p b)
    {a} (ha) : IsChain R (f a ha :: pmap f l hl) ↔
    IsChain (fun a b => ∃ ha, ∃ hb, R (f a ha) (f b hb)) (a :: l) :=
  isChain_pmap (l := a :: _) f (by grind)
/-
**List.isChain_cons_pmap_of_isChain_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_pmap_of_isChain_cons {S : β -> β -> Prop} {p : α -> Prop} {f 
: forall a, p a -> β} (H : forall a b ha hb, R a b -> S (f a ha) (f b hb)) {l : 
List α} {a} (ha) (hl₁ : IsChain R (a :: l)) (hl₂ : forall a in l, p a) : IsChain
 S (f a ha :: pmap f l hl₂)
参数：H : forall a b ha hb, R a b -> S (f a ha) (f b hb)；ha；hl₁ : IsChain R (a :: l
)；hl₂ : forall a in l, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.isChain_cons_pmap`：isChain_cons_pmap {p : β -> Prop} (f : forall b,
 p b -> α) {l : List β} (hl : forall b in l, p b) {a} (ha) : IsChain R (f a ha :
: pmap f l h…
· 使用定理 `List.IsChain.imp_of_mem_imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : 
List α},   (∀ (a b : α), a ∈ l → b ∈ l → R a b → S a b) → List.IsChain R l → Lis
t.IsChain S l
-/
theorem isChain_cons_pmap_of_isChain_cons {S : β → β → Prop} {p : α → Prop} {f : ∀ a, p a → β}
    (H : ∀ a b ha hb, R a b → S (f a ha) (f b hb)) {l : List α} {a} (ha)
    (hl₁ : IsChain R (a :: l)) (hl₂ : ∀ a ∈ l, p a) : IsChain S (f a ha :: pmap f l hl₂) :=
    (isChain_cons_pmap f _ _).2 <| hl₁.imp_of_mem_imp (by grind)
/-
**List.isChain_cons_of_isChain_cons_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_of_isChain_cons_pmap {S : β -> β -> Prop} {p : α -> Prop} (f 
: forall a, p a -> β) {l : List α} (hl₁ : forall a in l, p a) {a} (ha) (hl₂ : Is
Chain S (f a ha :: pmap f l hl₁)) (H : forall a b ha hb, S (f a ha) (f b hb) -> 
R a b) : IsChain R (a :: l)
参数：f : forall a, p a -> β；hl₁ : forall a in l, p a；ha；hl₂ : IsChain S (f a ha ::
 pmap f l hl₁)；H : forall a b ha hb, S (f a ha) (f b hb) -> R a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.imp`：∀ {α : Type u_1} {R S : α → α → Prop} {l : List α}, (∀
 ⦃a b : α⦄, R a b → S a b) → List.IsChain R l → List.IsChain S l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_cons_pmap`：isChain_cons_pmap {p : β -> Prop} (f : forall b,
 p b -> α) {l : List β} (hl : forall b in l, p b) {a} (ha) : IsChain R (f a ha :
: pmap f l h…
-/
theorem isChain_cons_of_isChain_cons_pmap {S : β → β → Prop} {p : α → Prop} (f : ∀ a, p a → β)
    {l : List α} (hl₁ : ∀ a ∈ l, p a) {a} (ha) (hl₂ : IsChain S (f a ha :: pmap f l hl₁))
    (H : ∀ a b ha hb, S (f a ha) (f b hb) → R a b) : IsChain R (a :: l) :=
  ((isChain_cons_pmap f _ _).1 hl₂).imp (by grind)
/-
**List.IsChain.sublist** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α} [Trans R R R],   List
.IsChain R l₂ → l₁.Sublist l₂ → List.IsChain R l₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.isChain_iff_pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α} [Trans R R R], List.IsChain R l ↔ List.Pairwise R l
· 使用定理 `List.Pairwise.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α} {R : α → α → Pr
op}, l₁.Sublist l₂ → List.Pairwise R l₂ → List.Pairwise R l₁
-/
protected theorem IsChain.sublist [Trans R R R] (hl : l₂.IsChain R) (h : l₁ <+ l₂) :
    l₁.IsChain R := by
  rw [isChain_iff_pairwise] at hl ⊢
  exact hl.sublist h
/-
**List.IsChain.rel_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} {a b : α} [Trans R R R], 
List.IsChain R (a :: l) → b ∈ l → R a b
参数：a :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rel_of_pairwise_cons`：∀ {α : Type u_1} {a : α} {l : List α} {R : α 
→ α → Prop}, List.Pairwise R (a :: l) → ∀ {a' : α}, a' ∈ l → R a a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.isChain_iff_pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α} [Trans R R R], List.IsChain R l ↔ List.Pairwise R l
-/
protected theorem IsChain.rel_cons [Trans R R R] (hl : (a :: l).IsChain R) (hb : b ∈ l) :
    R a b := by
  rw [isChain_iff_pairwise] at hl
  exact rel_of_pairwise_cons hl hb
/-
**List.IsChain.tail** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, List.IsChain R l → List.
IsChain R l.tail
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsChain.tail {l : List α} (h : IsChain R l) : IsChain R l.tail := by
  grind +splitIndPred

@[deprecated (since := "2026-06-25")] alias IsChain.rel_head := IsChain.rel
/-
**List.IsChain.rel_head** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l : List α}, List.IsChain R
 (a :: b :: l) → R a b
参数：a :: b :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.rel`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l : Lis
t α}, List.IsChain R (a :: b :: l) → R a b
-/
theorem IsChain.rel_head? {x l} (h : IsChain R (x :: l)) ⦃y⦄ (hy : y ∈ head? l) : R x y := by
  rw [← cons_head?_tail hy] at h
  exact h.rel
/-
**List.IsChain.rel_getLast_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},   List.IsChain R l → ∀ (
hne : l.dropLast ≠ []), R (l.dropLast.getLast hne) (l.getLast ⋯)
参数：hne : l.dropLast ≠ []；l.dropLast.getLast hne；l.getLast ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem IsChain.rel_getLast_dropLast {l : List α} (h : l.IsChain R) (hne : l.dropLast ≠ []) :
    R (l.dropLast.getLast hne) (l.getLast <| by grind) :=
  match l with
  | [_, _] => h.rel
  | _ :: _ :: _ :: _ => h.tail.rel_getLast_dropLast <| by simp
/-
**List.IsChain.cons** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {x : α} {l : List α},   List.IsChain R
 l → (∀ y ∈ l.head?, R x y) → List.IsChain R (x :: l)
参数：∀ y ∈ l.head?, R x y；x :: l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsChain.cons {x} : ∀ {l : List α}, IsChain R l → (∀ y ∈ l.head?, R x y) →
    IsChain R (x :: l)
  | [], _, _ => .singleton x
  | _ :: _, hl, H => hl.cons_cons <| H _ rfl
/-
**List.IsChain.cons_of_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {x : α} {l : List α} (l_ne_nil : l ≠ [
]),   List.IsChain R l → R x (l.head l_ne_nil) → List.IsChain R (x :: l)
参数：l_ne_nil : l ≠ []；l.head l_ne_nil；x :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
-/
lemma IsChain.cons_of_ne_nil {x : α} {l : List α} (l_ne_nil : l ≠ [])
    (hl : IsChain R l) (h : R x (l.head l_ne_nil)) : IsChain R (x :: l) := by
  grind +splitIndPred
/-
**List.isChain_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons {x l} : IsChain R (x :: l) ↔ (forall y in head? l, R x y) ∧ I
sChain R l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.rel_head?`：∀ {α : Type u_1} {R : α → α → Prop} {x : α} {l :
 List α}, List.IsChain R (x :: l) → ∀ ⦃y : α⦄, y ∈ l.head? → R x y
· 使用定理 `List.IsChain.tail`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, Lis
t.IsChain R l → List.IsChain R l.tail
· 使用定理 `List.IsChain.cons`：∀ {α : Type u_1} {R : α → α → Prop} {x : α} {l : List
 α},   List.IsChain R l → (∀ y ∈ l.head?, R x y) → List.IsChain R (x :: l)
-/
theorem isChain_cons {x l} : IsChain R (x :: l) ↔ (∀ y ∈ head? l, R x y) ∧ IsChain R l :=
  ⟨fun h => ⟨h.rel_head?, h.tail⟩, fun ⟨h₁, h₂⟩ => h₂.cons h₁⟩
/-
**List.isChain_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α},   List.IsChain R (l₁
 ++ l₂) ↔ List.IsChain R l₁ ∧ List.IsChain R l₂ ∧ ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.he
ad?, R x y
参数：l₁ ++ l₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_append :
    ∀ {l₁ l₂ : List α},
      IsChain R (l₁ ++ l₂) ↔ IsChain R l₁ ∧ IsChain R l₂ ∧ ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y
  | [], l => by simp
  | [a], l => by simp [isChain_cons, and_comm]
  | a :: b :: l₁, l₂ => by
    rw [cons_append, cons_append, isChain_cons_cons, isChain_cons_cons,
      ← cons_append, isChain_append, and_assoc]
    simp
/-
**List.IsChain.append** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α},   List.IsChain R l₁ 
→ List.IsChain R l₂ → (∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) → List.IsChain 
R (l₁ ++ l₂)
参数：∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y；l₁ ++ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.isChain_append`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α
},   List.IsChain R (l₁ ++ l₂) ↔ List.IsChain R l₁ ∧ List.IsChain R l₂ ∧ ∀ x ∈ l
₁.getLast…
-/
theorem IsChain.append (h₁ : IsChain R l₁) (h₂ : IsChain R l₂)
    (h : ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) : IsChain R (l₁ ++ l₂) :=
  isChain_append.2 ⟨h₁, h₂, h⟩
/-
**List.IsChain.left_of_append** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α}, List.IsChain R (l₁ +
+ l₂) → List.IsChain R l₁
参数：l₁ ++ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_append`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α
},   List.IsChain R (l₁ ++ l₂) ↔ List.IsChain R l₁ ∧ List.IsChain R l₂ ∧ ∀ x ∈ l
₁.getLast…
-/
theorem IsChain.left_of_append (h : IsChain R (l₁ ++ l₂)) : IsChain R l₁ :=
  (isChain_append.1 h).1
/-
**List.IsChain.right_of_append** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α}, List.IsChain R (l₁ +
+ l₂) → List.IsChain R l₂
参数：l₁ ++ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_append`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α
},   List.IsChain R (l₁ ++ l₂) ↔ List.IsChain R l₁ ∧ List.IsChain R l₂ ∧ ∀ x ∈ l
₁.getLast…
-/
theorem IsChain.right_of_append (h : IsChain R (l₁ ++ l₂)) : IsChain R l₂ :=
  (isChain_append.1 h).2.1
/-
**List.IsChain.rel_getLast_head_of_append** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChai
n`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α},   List.IsChain R (l₁
 ++ l₂) → ∀ (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []), R (l₁.getLast h₁) (l₂.head h₂)
参数：l₁ ++ l₂；h₁ : l₁ ≠ []；h₂ : l₂ ≠ []；l₁.getLast h₁；l₂.head h₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
-/
theorem IsChain.rel_getLast_head_of_append {l₁ l₂ : List α} (h : (l₁ ++ l₂).IsChain R)
    (h₁ : l₁ ≠ []) (h₂ : l₂ ≠ []) : R (l₁.getLast h₁) (l₂.head h₂) :=
  match l₁, l₂ with
  | [_], _ :: _ => h.rel
  | _ :: _ :: _, _ :: _ => h.tail.rel_getLast_head_of_append (by simp) (by simp)
/-
**List.IsChain.infix** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l l₁ : List α}, List.IsChain R l → l₁
 <:+: l → List.IsChain R l₁
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.right_of_append`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂
 : List α}, List.IsChain R (l₁ ++ l₂) → List.IsChain R l₂
· 使用定理 `List.IsChain.left_of_append`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ 
: List α}, List.IsChain R (l₁ ++ l₂) → List.IsChain R l₁
-/
theorem IsChain.infix (h : IsChain R l) (h' : l₁ <:+: l) : IsChain R l₁ := by
  rcases h' with ⟨l₂, l₃, rfl⟩
  exact h.left_of_append.right_of_append
/-
**List.IsChain.suffix** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l l₁ : List α}, List.IsChain R l → l₁
 <:+ l → List.IsChain R l₁
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.infix`：∀ {α : Type u_1} {R : α → α → Prop} {l l₁ : List α},
 List.IsChain R l → l₁ <:+: l → List.IsChain R l₁
· 使用定理 `List.IsSuffix.isInfix`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁
 <:+: l₂
-/
theorem IsChain.suffix (h : IsChain R l) (h' : l₁ <:+ l) : IsChain R l₁ :=
  h.infix h'.isInfix
/-
**List.IsChain.prefix** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l l₁ : List α}, List.IsChain R l → l₁
 <+: l → List.IsChain R l₁
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.infix`：∀ {α : Type u_1} {R : α → α → Prop} {l l₁ : List α},
 List.IsChain R l → l₁ <:+: l → List.IsChain R l₁
· 使用定理 `List.IsPrefix.isInfix`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <+: l₂ → l₁
 <:+: l₂
-/
theorem IsChain.prefix (h : IsChain R l) (h' : l₁ <+: l) : IsChain R l₁ :=
  h.infix h'.isInfix
/-
**List.IsChain.drop** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, List.IsChain R l → ∀ (n 
: ℕ), List.IsChain R (List.drop n l)
参数：n : ℕ；List.drop n l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.suffix`：∀ {α : Type u_1} {R : α → α → Prop} {l l₁ : List α}
, List.IsChain R l → l₁ <:+ l → List.IsChain R l₁
· 使用定理 `List.drop_suffix`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.drop i l <
:+ l
-/
theorem IsChain.drop (h : IsChain R l) (n : ℕ) : IsChain R (drop n l) :=
  h.suffix (drop_suffix _ _)
/-
**List.IsChain.dropLast** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, List.IsChain R l → List.
IsChain R l.dropLast
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.prefix`：∀ {α : Type u_1} {R : α → α → Prop} {l l₁ : List α}
, List.IsChain R l → l₁ <+: l → List.IsChain R l₁
· 使用定理 `List.dropLast_prefix`：∀ {α : Type u_1} (l : List α), l.dropLast <+: l
-/
theorem IsChain.dropLast (h : IsChain R l) : IsChain R l.dropLast :=
  h.prefix l.dropLast_prefix
/-
**List.IsChain.take** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, List.IsChain R l → ∀ (n 
: ℕ), List.IsChain R (List.take n l)
参数：n : ℕ；List.take n l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.prefix`：∀ {α : Type u_1} {R : α → α → Prop} {l l₁ : List α}
, List.IsChain R l → l₁ <+: l → List.IsChain R l₁
· 使用定理 `List.take_prefix`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take i l <
+: l
-/
theorem IsChain.take (h : IsChain R l) (n : ℕ) : IsChain R (take n l) :=
  h.prefix (take_prefix _ _)
/-
**List.IsChain.imp_head** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {x y : α},   (∀ {z : α}, R x z → R y z
) → ∀ {l : List α}, List.IsChain R (x :: l) → List.IsChain R (y :: l)
参数：∀ {z : α}, R x z → R y z；x :: l；y :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.cons_of_imp`：∀ {α : Type u_1} {R : α → α → Prop} {a : α} {l
 : List α} {b : α},   (∀ (c : α), R a c → R b c) → List.IsChain R (a :: l) → Lis
t.IsChain R (b…
-/
theorem IsChain.imp_head {x y} (h : ∀ {z}, R x z → R y z) {l} (hl : IsChain R (x :: l)) :
    IsChain R (y :: l) :=
  IsChain.cons_of_imp @h hl
/-
**List.exists_not_getElem_of_not_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：exists_not_getElem_of_not_isChain (h : ¬List.IsChain R l) : exists n : Nat
, exists h : n + 1 < l.length, ¬R l[n] l[n + 1]
参数：h : ¬List.IsChain R l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem exists_not_getElem_of_not_isChain (h : ¬List.IsChain R l) :
    ∃ n : ℕ, ∃ h : n + 1 < l.length, ¬R l[n] l[n + 1] := by simp_all [isChain_iff_getElem]
/-
**List.isChain_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_reverse {l : List α} : l.reverse.IsChain R ↔ l.IsChain (fun a b =>
 R b a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.isChain_cons_cons`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l
 : List α},   List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.cons_append`：∀ {α : Type u} {a : α} {as bs : List α}, a :: as ++ bs
 = a :: (as ++ bs)
· 使用定理 `List.nil_append`：∀ {α : Type u} (as : List α), [] ++ as = as
· 使用定理 `List.isChain_split`：isChain_split {c : α} {l₁ l₂ : List α} : IsChain R (
l₁ ++ c :: l₂) ↔ IsChain R (l₁ ++ [c]) ∧ IsChain R (c :: l₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `List.isChain_pair`：isChain_pair {x y} : IsChain R [x, y] ↔ R x y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isChain_reverse {l : List α} : l.reverse.IsChain R ↔ l.IsChain (fun a b => R b a) := by
  induction l using twoStepInduction with
  | nil => grind
  | singleton a => grind
  | cons_cons a b l IH IH2 =>
    rw [isChain_cons_cons, reverse_cons, reverse_cons, append_assoc, cons_append, nil_append,
      isChain_split, ← reverse_cons, IH2, and_comm, isChain_pair]

/-- If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `IsChain R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []` -/
/-
**List.IsChain.append_overlap** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ l₃ : List α},   List.IsChain R 
(l₁ ++ l₂) → List.IsChain R (l₂ ++ l₃) → l₂ ≠ [] → List.IsChain R (l₁ ++ l₂ ++ l
₃)
参数：l₁ ++ l₂；l₂ ++ l₃；l₁ ++ l₂ ++ l₃。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.append`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α
},   List.IsChain R l₁ → List.IsChain R l₂ → (∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?,
 R x y) →…
· 使用定理 `List.IsChain.right_of_append`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂
 : List α}, List.IsChain R (l₁ ++ l₂) → List.IsChain R l₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getLast?_append_of_ne_nil`：∀ {α : Type u} (l₁ : List α) {l₂ : List 
α}, l₂ ≠ [] → (l₁ ++ l₂).getLast? = l₂.getLast?
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_append`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α
},   List.IsChain R (l₁ ++ l₂) ↔ List.IsChain R l₁ ∧ List.IsChain R l₂ ∧ ∀ x ∈ l
₁.getLast…

--- 原说明 ---
If `l₁ l₂` and `l₃` are lists and `l₁ ++ l₂` and `l₂ ++ l₃` both satisfy
  `IsChain R`, then so does `l₁ ++ l₂ ++ l₃` provided `l₂ ≠ []`
-/
theorem IsChain.append_overlap {l₁ l₂ l₃ : List α} (h₁ : IsChain R (l₁ ++ l₂))
    (h₂ : IsChain R (l₂ ++ l₃)) (hn : l₂ ≠ []) : IsChain R (l₁ ++ l₂ ++ l₃) :=
  h₁.append h₂.right_of_append <| by
    simpa only [getLast?_append_of_ne_nil _ hn] using (isChain_append.1 h₂).2.2
/-
**List.isChain_flatten** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {R : α → α → Prop} {L : List (List α)},   [] ∉ L →     (L
ist.IsChain R L.flatten ↔       (∀ l ∈ L, List.IsChain R l) ∧ List.IsChain (fun 
l₁ l₂ => ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) L)
参数：List α；List.IsChain R L.flatten ↔       (∀ l ∈ L, List.IsChain R l) ∧ List.Is
Chain (fun l₁ l₂ => ∀ x ∈ l₁.getLast?, ∀ y ∈ l₂.head?, R x y) L。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isChain_flatten : ∀ {L : List (List α)}, [] ∉ L →
    (IsChain R L.flatten ↔ (∀ l ∈ L, IsChain R l) ∧
    L.IsChain (fun l₁ l₂ => ∀ᵉ (x ∈ l₁.getLast?) (y ∈ l₂.head?), R x y))
| [], _ => by simp
| [l], _ => by simp [flatten]
| (l₁ :: l₂ :: L), hL => by
    rw [mem_cons, not_or, ← Ne] at hL
    rw [flatten_cons, isChain_append, isChain_flatten hL.2, forall_mem_cons, isChain_cons_cons]
    rw [mem_cons, not_or, ← Ne] at hL
    simp only [forall_mem_cons, and_assoc, flatten_cons, head?_append_of_ne_nil _ hL.2.1.symm]
    exact Iff.rfl.and (Iff.rfl.and <| Iff.rfl.and and_comm)
/-
**List.isChain_attachWith** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_attachWith {l : List α} {p : α -> Prop} (h : forall x in l, p x) {
r : {a // p a} -> {a // p a} -> Prop} : (l.attachWith p h).IsChain r ↔ l.IsChain
 fun a b => exists ha hb, r ⟨a, ha⟩ ⟨b, hb⟩
参数：h : forall x in l, p x。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_attachWith {l : List α} {p : α → Prop} (h : ∀ x ∈ l, p x)
    {r : {a // p a} → {a // p a} → Prop} :
    (l.attachWith p h).IsChain r ↔ l.IsChain fun a b ↦ ∃ ha hb, r ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction l with grind +splitIndPred
/-
**List.isChain_attach** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_attach {l : List α} {r : {a // a in l} -> {a // a in l} -> Prop} :
 l.attach.IsChain r ↔ l.IsChain fun a b => exists ha hb, r ⟨a, ha⟩ ⟨b, hb⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.isChain_attachWith`：isChain_attachWith {l : List α} {p : α -> Prop}
 (h : forall x in l, p x) {r : {a // p a} -> {a // p a} -> Prop} : (l.attachWith
 p h).IsChain…
-/
theorem isChain_attach {l : List α} {r : {a // a ∈ l} → {a // a ∈ l} → Prop} :
    l.attach.IsChain r ↔ l.IsChain fun a b ↦ ∃ ha hb, r ⟨a, ha⟩ ⟨b, hb⟩ :=
  isChain_attachWith fun _ ↦ id

/-- If `a` and `b` are related by the reflexive transitive closure of `r`, then there is an
`r`-chain starting from `a` and ending on `b`.
-/
/-
**List.exists_isChain_cons_of_relationReflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `Li
st`。
形式化陈述：exists_isChain_cons_of_relationReflTransGen (h : Relation.ReflTransGen r a
 b) : exists l, IsChain r (a :: l) ∧ getLast (a :: l) (cons_ne_nil _ _) = b
参数：h : Relation.ReflTransGen r a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.head_induction_on`：head_induction_on {motive : for
all a : α, ReflTransGen r a b -> Prop} {a : α} (h : ReflTransGen r a b) (refl : 
motive b refl) (head : forall…
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getLast_cons_cons`：∀ {α : Type u_1} {b a : α} {l : List α}, (a :: b
 :: l).getLast ⋯ = (b :: l).getLast ⋯

--- 原说明 ---
If `a` and `b` are related by the reflexive transitive closure of `r`, then ther
e is an
`r`-chain starting from `a` and ending on `b`.
-/
theorem exists_isChain_cons_of_relationReflTransGen (h : Relation.ReflTransGen r a b) :
    ∃ l, IsChain r (a :: l) ∧ getLast (a :: l) (cons_ne_nil _ _) = b := by
  refine Relation.ReflTransGen.head_induction_on h ?_ ?_
  · exact ⟨[], .singleton _, rfl⟩
  · intro c d e _ ih
    obtain ⟨l, hl₁, hl₂⟩ := ih
    refine ⟨d :: l, .cons_cons e hl₁, ?_⟩
    rwa [getLast_cons_cons]

/-- If `a` and `b` are related by the reflexive transitive closure of `r`, then there is an
`r`-chain starting from `a` and ending on `b`.
-/
/-
**List.exists_isChain_ne_nil_of_relationReflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `
List`。
形式化陈述：exists_isChain_ne_nil_of_relationReflTransGen (h : Relation.ReflTransGen r
 a b) : exists l, exists (hl : l != []), IsChain r l ∧ l.head hl = a ∧ getLast l
 hl = b
参数：h : Relation.ReflTransGen r a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.exists_isChain_cons_of_relationReflTransGen`：exists_isChain_cons_of
_relationReflTransGen (h : Relation.ReflTransGen r a b) : exists l, IsChain r (a
 :: l) ∧ getLast (a :: l) (cons_ne_nil…

--- 原说明 ---
If `a` and `b` are related by the reflexive transitive closure of `r`, then ther
e is an
`r`-chain starting from `a` and ending on `b`.
-/
theorem exists_isChain_ne_nil_of_relationReflTransGen (h : Relation.ReflTransGen r a b) :
    ∃ l, ∃ (hl : l ≠ []), IsChain r l ∧ l.head hl = a ∧ getLast l hl = b := by
  rcases exists_isChain_cons_of_relationReflTransGen h with ⟨l, _⟩; grind

/-- Given a chain `l`, such that a predicate `p` holds for its head if it is nonempty,
and if `r x y → p x → p y`, then the predicate is true everywhere in the chain.
That is, we can propagate the predicate down the chain.
-/
/-
**List.IsChain.induction** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (p : α → Prop) (l : List α),   List.Is
Chain r l → (∀ ⦃x y : α⦄, r x y → p x → p y) → (∀ (lne : l ≠ []), p (l.head lne)
) → ∀ i ∈ l, p i
参数：p : α → Prop；l : List α；∀ ⦃x y : α⦄, r x y → p x → p y；∀ (lne : l ≠ []), p (l
.head lne)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?

--- 原说明 ---
Given a chain `l`, such that a predicate `p` holds for its head if it is nonempt
y,
and if `r x y → p x → p y`, then the predicate is true everywhere in the chain.
That is, we can propagate the predicate down the chain.
-/
theorem IsChain.induction (p : α → Prop) (l : List α) (h : IsChain r l)
    (carries : ∀ ⦃x y : α⦄, r x y → p x → p y) (initial : (lne : l ≠ []) → p (l.head lne)) :
    ∀ i ∈ l, p i := by
  induction l using twoStepInduction with grind

/-- Given a chain from `a` to `b`, and a predicate true at `a`, if `r x y → p x → p y` then
the predicate is true everywhere in the chain.
That is, we can propagate the predicate down the chain.
-/
/-
**List.IsChain.cons_induction** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {a : α} (p : α → Prop) (l : List α),  
 List.IsChain r (a :: l) → (∀ ⦃x y : α⦄, r x y → p x → p y) → p a → ∀ i ∈ l, p i
参数：p : α → Prop；l : List α；a :: l；∀ ⦃x y : α⦄, r x y → p x → p y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.induction`：∀ {α : Type u_1} {r : α → α → Prop} (p : α → Pro
p) (l : List α),   List.IsChain r l → (∀ ⦃x y : α⦄, r x y → p x → p y) → (∀ (lne
 : l ≠ []), …
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l

--- 原说明 ---
Given a chain from `a` to `b`, and a predicate true at `a`, if `r x y → p x → p 
y` then
the predicate is true everywhere in the chain.
That is, we can propagate the predicate down the chain.
-/
theorem IsChain.cons_induction (p : α → Prop) (l : List α) (h : IsChain r (a :: l))
    (carries : ∀ ⦃x y : α⦄, r x y → p x → p y) (initial : p a) : ∀ i ∈ l, p i := fun _ hi =>
  h.induction _ _ carries (fun _ => initial) _ (mem_cons_of_mem _ hi)
/-
**List.IsChain.concat_induction** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
   List.IsChain r (l ++ [b]) → (l ++ [b]).head ⋯ = a → (∀ ⦃x y : α⦄, r x y → p x
 → p y) → p a → ∀ i ∈ l ++ [b], p i
参数：p : α → Prop；l : List α；l ++ [b]；l ++ [b]；∀ ⦃x y : α⦄, r x y → p x → p y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.concat_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), l ++ [a] ≠ []
· 使用定理 `List.IsChain.induction`：∀ {α : Type u_1} {r : α → α → Prop} (p : α → Pro
p) (l : List α),   List.IsChain r l → (∀ ⦃x y : α⦄, r x y → p x → p y) → (∀ (lne
 : l ≠ []), …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsChain.concat_induction (p : α → Prop) (l : List α) (h : IsChain r (l ++ [b]))
    (hb : head (l ++ [b]) (concat_ne_nil _ _) = a) (carries : ∀ ⦃x y : α⦄, r x y → p x → p y)
    (initial : p a) : ∀ i ∈ l ++ [b], p i :=
  h.induction _ _ carries (fun _ => hb ▸ initial)

@[elab_as_elim]
/-
**List.IsChain.concat_induction_head** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
   List.IsChain r (l ++ [b]) → (l ++ [b]).head ⋯ = a → (∀ ⦃x y : α⦄, r x y → p x
 → p y) → p a → p b
参数：p : α → Prop；l : List α；l ++ [b]；l ++ [b]；∀ ⦃x y : α⦄, r x y → p x → p y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.concat_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), l ++ [a] ≠ []
· 使用定理 `List.IsChain.concat_induction`：∀ {α : Type u_1} {r : α → α → Prop} {a b 
: α} (p : α → Prop) (l : List α),   List.IsChain r (l ++ [b]) → (l ++ [b]).head 
⋯ = a → (∀ ⦃x y : α…
· 使用定理 `List.mem_concat_self`：∀ {α : Type u_1} {xs : List α} {a : α}, a ∈ xs ++ 
[a]
-/
theorem IsChain.concat_induction_head (p : α → Prop) (l : List α) (h : IsChain r (l ++ [b]))
    (hb : head (l ++ [b]) (concat_ne_nil _ _) = a) (carries : ∀ ⦃x y : α⦄, r x y → p x → p y)
    (initial : p a) : p b :=
  (IsChain.concat_induction p l h hb carries initial) _ mem_concat_self

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
/-
**List.IsChain.backwards_induction** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} (p : α → Prop) (l : List α),   List.Is
Chain r l → (∀ ⦃x y : α⦄, r x y → p y → p x) → (∀ (lne : l ≠ []), p (l.getLast l
ne)) → ∀ i ∈ l, p i
参数：p : α → Prop；l : List α；∀ ⦃x y : α⦄, r x y → p y → p x；∀ (lne : l ≠ []), p (l
.getLast lne)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.IsChain.induction`：∀ {α : Type u_1} {r : α → α → Prop} (p : α → Pro
p) (l : List α),   List.IsChain r l → (∀ ⦃x y : α⦄, r x y → p x → p y) → (∀ (lne
 : l ≠ []), …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.isChain_reverse`：isChain_reverse {l : List α} : l.reverse.IsChain R
 ↔ l.IsChain (fun a b => R b a)

--- 原说明 ---
Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p 
x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
theorem IsChain.backwards_induction (p : α → Prop) (l : List α) (h : IsChain r l)
    (carries : ∀ ⦃x y : α⦄, r x y → p y → p x) (final : (lne : l ≠ []) → p (getLast l lne)) :
    ∀ i ∈ l, p i := by
  have H : IsChain (flip (flip r)) l := h
  replace H := (isChain_reverse.mpr H).induction _ _ (fun _ _ h ↦ carries h)
  grind

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
/-
**List.IsChain.backwards_concat_induction** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChai
n`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {b : α} (p : α → Prop) (l : List α),  
 List.IsChain r (l ++ [b]) → (∀ ⦃x y : α⦄, r x y → p y → p x) → p b → ∀ i ∈ l, p
 i
参数：p : α → Prop；l : List α；l ++ [b]；∀ ⦃x y : α⦄, r x y → p y → p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.backwards_induction`：∀ {α : Type u_1} {r : α → α → Prop} (p
 : α → Prop) (l : List α),   List.IsChain r l → (∀ ⦃x y : α⦄, r x y → p y → p x)
 → (∀ (lne : l ≠ []), …
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getLast_concat`：∀ {α : Type u_1} {a : α} {l : List α}, (l ++ [a]).g
etLast ⋯ = a
· 使用定理 `List.mem_append_left`：∀ {α : Type u} {a : α} {as : List α} (bs : List α)
, a ∈ as → a ∈ as ++ bs

--- 原说明 ---
Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p 
x` then
the predicate is true everywhere in the chain and at `a`.
That is, we can propagate the predicate up the chain.
-/
theorem IsChain.backwards_concat_induction (p : α → Prop) (l : List α) (h : IsChain r (l ++ [b]))
    (carries : ∀ ⦃x y : α⦄, r x y → p y → p x) (final : p b) : ∀ i ∈ l, p i := fun _ hi =>
  h.backwards_induction _ _ carries (fun _ => getLast_concat ▸ final) _ (mem_append_left _ hi)
/-
**List.IsChain.backwards_cons_induction** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`
。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
   List.IsChain r (a :: l) → (a :: l).getLast ⋯ = b → (∀ ⦃x y : α⦄, r x y → p y 
→ p x) → p b → ∀ i ∈ a :: l, p i
参数：p : α → Prop；l : List α；a :: l；a :: l；∀ ⦃x y : α⦄, r x y → p y → p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.IsChain.backwards_induction`：∀ {α : Type u_1} {r : α → α → Prop} (p
 : α → Prop) (l : List α),   List.IsChain r l → (∀ ⦃x y : α⦄, r x y → p y → p x)
 → (∀ (lne : l ≠ []), …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsChain.backwards_cons_induction (p : α → Prop) (l : List α) (h : IsChain r (a :: l))
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : ∀ ⦃x y : α⦄, r x y → p y → p x)
    (final : p b) : ∀ i ∈ a :: l, p i :=
  h.backwards_induction _ _ carries (fun _ => hb ▸ final)

/-- Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p x` then
the predicate is true at `a`.
That is, we can propagate the predicate all the way up the chain.
-/
@[elab_as_elim]
/-
**List.IsChain.backwards_cons_induction_head** 是 Mathlib 中的一个定理，位于命名空间 `List.IsC
hain`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {a b : α} (p : α → Prop) (l : List α),
   List.IsChain r (a :: l) → (a :: l).getLast ⋯ = b → (∀ ⦃x y : α⦄, r x y → p y 
→ p x) → p b → p a
参数：p : α → Prop；l : List α；a :: l；a :: l；∀ ⦃x y : α⦄, r x y → p y → p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.IsChain.backwards_cons_induction`：∀ {α : Type u_1} {r : α → α → Pro
p} {a b : α} (p : α → Prop) (l : List α),   List.IsChain r (a :: l) → (a :: l).g
etLast ⋯ = b → (∀ ⦃x y : α⦄…
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l

--- 原说明 ---
Given a chain from `a` to `b`, and a predicate true at `b`, if `r x y → p y → p 
x` then
the predicate is true at `a`.
That is, we can propagate the predicate all the way up the chain.
-/
theorem IsChain.backwards_cons_induction_head (p : α → Prop) (l : List α) (h : IsChain r (a :: l))
    (hb : getLast (a :: l) (cons_ne_nil _ _) = b) (carries : ∀ ⦃x y : α⦄, r x y → p y → p x)
    (final : p b) : p a :=
  (IsChain.backwards_cons_induction p l h hb carries final) _ mem_cons_self

/--
If there is a non-empty `r`-chain, its head and last element are related by the
reflexive transitive closure of `r`.
-/
/-
**List.relationReflTransGen_of_exists_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：relationReflTransGen_of_exists_isChain (l : List α) (hl₁ : IsChain r l) (h
ne : l != []) : Relation.ReflTransGen r (head l hne) (getLast l hne)
参数：l : List α；hl₁ : IsChain r l；hne : l != []。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.induction`：∀ {α : Type u_1} {r : α → α → Prop} (p : α → Pro
p) (l : List α),   List.IsChain r l → (∀ ⦃x y : α⦄, r x y → p x → p y) → (∀ (lne
 : l ≠ []), …
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l

--- 原说明 ---
If there is a non-empty `r`-chain, its head and last element are related by the
reflexive transitive closure of `r`.
-/
theorem relationReflTransGen_of_exists_isChain (l : List α) (hl₁ : IsChain r l) (hne : l ≠ []) :
    Relation.ReflTransGen r (head l hne) (getLast l hne) :=
  IsChain.induction (Relation.ReflTransGen r (head l hne) ·) l hl₁
  (fun _ _ h₁ h₂ => Trans.trans h₂ h₁) (fun _ => Relation.ReflTransGen.refl) _ (getLast_mem _)

/--
If there is an `r`-chain starting from `a` and ending at `b`, then `a` and `b` are related by the
reflexive transitive closure of `r`.
-/
/-
**List.relationReflTransGen_of_exists_isChain_cons** 是 Mathlib 中的一个定理，位于命名空间 `Li
st`。
形式化陈述：relationReflTransGen_of_exists_isChain_cons (l : List α) (hl₁ : IsChain r 
(a :: l)) (hl₂ : getLast (a :: l) (cons_ne_nil _ _) = b) : Relation.ReflTransGen
 r a b
参数：l : List α；hl₁ : IsChain r (a :: l)；hl₂ : getLast (a :: l) (cons_ne_nil _ _) 
= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.IsChain.backwards_cons_induction_head`：∀ {α : Type u_1} {r : α → α 
→ Prop} {a b : α} (p : α → Prop) (l : List α),   List.IsChain r (a :: l) → (a ::
 l).getLast ⋯ = b → (∀ ⦃x y : α⦄…
· 使用定理 `Relation.ReflTransGen.head`：head (hab : r a b) (hbc : ReflTransGen r b c
) : ReflTransGen r a c

--- 原说明 ---
If there is an `r`-chain starting from `a` and ending at `b`, then `a` and `b` a
re related by the
reflexive transitive closure of `r`.
-/
theorem relationReflTransGen_of_exists_isChain_cons (l : List α) (hl₁ : IsChain r (a :: l))
    (hl₂ : getLast (a :: l) (cons_ne_nil _ _) = b) : Relation.ReflTransGen r a b :=
  IsChain.backwards_cons_induction_head _ l hl₁ hl₂ (fun _ _ => Relation.ReflTransGen.head)
  Relation.ReflTransGen.refl
/-
**List.IsChain.cons_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {a : α} {as m : List α},   List.Is
Chain (fun x1 x2 => x1 > x2) (a :: as) →     List.IsChain (fun x1 x2 => x1 > x2)
 m → m ≤ as → List.IsChain (fun x1 x2 => x1 > x2) (a :: m)
参数：fun x1 x2 => x1 > x2；a :: as；fun x1 x2 => x1 > x2；fun x1 x2 => x1 > x2；a :: m
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.not_lt_nil`：∀ {α : Type u_1} [inst : LT α] (l : List α), ¬l < []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用引理 `le_iff_lt_or_eq`：le_iff_lt_or_eq : a <= b ↔ a < b ∨ a = b
· 使用定理 `List.head_le_of_lt`：head_le_of_lt [Preorder α] {a a' : α} {l l' : List α
} (h : (a' :: l') < (a :: l)) : a' <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.isChain_cons_cons`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l
 : List α},   List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)
-/
theorem IsChain.cons_of_le [LinearOrder α] {a : α} {as m : List α}
    (ha : List.IsChain (· > ·) (a :: as)) (hm : List.IsChain (· > ·) m) (hmas : m ≤ as) :
    List.IsChain (· > ·) (a :: m) := by
  cases m with
  | nil => grind
  | cons b bs =>
    apply hm.cons_cons
    cases as with
    | nil =>
      simp only [le_iff_lt_or_eq, reduceCtorEq, or_false] at hmas
      exact (List.not_lt_nil _ hmas).elim
    | cons a' as =>
      rw [List.isChain_cons_cons] at ha
      refine lt_of_le_of_lt ?_ ha.1
      rw [le_iff_lt_or_eq] at hmas
      rcases hmas with hmas | hmas
      · exact head_le_of_lt hmas
      · simp_all only [List.cons.injEq, le_refl]
/-
**List.IsChain.isChain_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_3} {R : α → α → Prop} {l : List α} {v : α},   List.IsChain R
 l → (∀ (lne : l ≠ []), R v (l.head lne)) → List.IsChain R (v :: l)
参数：∀ (lne : l ≠ []), R v (l.head lne)；v :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsChain.isChain_cons {α : Type*} {R : α → α → Prop} {l : List α} {v : α}
    (hl : l.IsChain R) (hv : (lne : l ≠ []) → R v (l.head lne)) : (v :: l).IsChain R := by
  cases l <;> grind
/-
**List.IsChain.iterate_eq_of_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.IsChain`。
形式化陈述：∀ {α : Type u_3} {f : α → α} {l : List α},   List.IsChain (fun x y => f x 
= y) l → ∀ (i : ℕ) (hi : i < l.length), f^[i] l[0] = l[i]
参数：fun x y => f x = y；i : ℕ；hi : i < l.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `List.isChain_iff_getElem`：∀ {α : Type u_1} {R : α → α → Prop} {l : List 
α}, List.IsChain R l ↔ ∀ (i : ℕ) (_hi : i + 1 < l.length), R l[i] l[i + 1]
-/
lemma IsChain.iterate_eq_of_apply_eq {α : Type*} {f : α → α} {l : List α}
    (hl : l.IsChain (fun x y ↦ f x = y)) (i : ℕ) (hi : i < l.length) :
    f^[i] l[0] = l[i] := by
  induction i with
  | zero => rfl
  | succ i h =>
    rw [Function.iterate_succ', Function.comp_apply, h (by lia)]
    rw [List.isChain_iff_getElem] at hl
    apply hl
/-
**List.isChain_replicate_of_rel** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_replicate_of_rel (n : Nat) {a : α} (h : r a a) : IsChain r (replic
ate n a)
参数：n : Nat；h : r a a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_replicate_of_rel (n : ℕ) {a : α} (h : r a a) : IsChain r (replicate n a) := by
  induction n using Nat.twoStepInduction <;> grind
/-
**List.isChain_eq_iff_eq_replicate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_eq_iff_eq_replicate {l : List α} : IsChain (· = ·) l ↔ forall a in
 l.head?, l = replicate l.length a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem isChain_eq_iff_eq_replicate {l : List α} :
    IsChain (· = ·) l ↔ ∀ a ∈ l.head?, l = replicate l.length a := by
  induction l using twoStepInduction with
  | nil | singleton => simp
  | cons_cons a b l IH IH2 =>
    simp +contextual [isChain_cons_cons, eq_comm, IH2, replicate_succ]
/-
**List.isChain_cons_eq_iff_eq_replicate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_cons_eq_iff_eq_replicate {a : α} {l : List α} : IsChain (· = ·) (a
 :: l) ↔ l = replicate l.length a
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
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isChain_cons_eq_iff_eq_replicate {a : α} {l : List α} :
    IsChain (· = ·) (a :: l) ↔ l = replicate l.length a := by
  simp [isChain_eq_iff_eq_replicate, replicate_succ]

end List

/-
**WellFoundedRelation.asymmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFoundedRelation.asymmetric {α : Sort*} [WellFoundedRelation α] {a b : 
α} : WellFoundedRelation.rel a b -> ¬ WellFoundedRelation.rel b a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedRelation.asymmetric._unary`：∀ {α : Sort u_1} [inst : WellFoun
dedRelation α]   (_x : (a : α) ×' (b : α) ×' (_ : WellFoundedRelation.rel a b) ×
' WellFoundedRelation.rel b…
-/
theorem WellFoundedRelation.asymmetricₙ [WellFoundedRelation α] {l : List α} (hne : l ≠ [])
    (h : l.IsChain WellFoundedRelation.rel) :
    ¬WellFoundedRelation.rel (l.getLast hne) (l.head hne) :=
  match l with
  | [x] => irrefl x
  | _ :: _ :: _ =>
    fun hr ↦ asymmetricₙ (List.cons_ne_nil _ _) (h.dropLast.cons_cons hr) (h.rel_getLast_dropLast _)
termination_by l.head hne
/-
**WellFounded.asymmetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.asymmetric {α : Sort*} {r : α -> α -> Prop} (h : WellFounded r
) (a b) : r a b -> ¬r b a
参数：h : WellFounded r；a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedRelation.asymmetric`：WellFoundedRelation.asymmetric {α : Sort
*} [WellFoundedRelation α] {a b : α} : WellFoundedRelation.rel a b -> ¬ WellFoun
dedRelation.rel b a
-/
theorem WellFounded.asymmetricₙ (wf : WellFounded r) (hne : l ≠ []) (h : l.IsChain r) :
    ¬r (l.getLast hne) (l.head hne) :=
  @WellFoundedRelation.asymmetricₙ α ⟨r, wf⟩ l hne h
/-
**WellFounded.listPairwise_reverse_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.listPairwise_reverse_compl (wf : WellFounded r) (h : l.IsChain
 r) : l.reverse.Pairwise rᶜ
参数：wf : WellFounded r；h : l.IsChain r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.pairwise_iff_forall_infix`：pairwise_iff_forall_infix {α : Type*} {l
 : List α} {R : α -> α -> Prop} : l.Pairwise R ↔ forall l', (h : 1 < l'.length) 
-> l' <:+: l -> R (l…
· 使用定理 `WellFounded.asymmetricₙ`：WellFounded.asymmetricₙ (wf : WellFounded r) (h
ne : l != []) (h : l.IsChain r) : ¬r (l.getLast hne) (l.head hne)
· 使用定理 `List.IsChain.infix`：∀ {α : Type u_1} {R : α → α → Prop} {l l₁ : List α},
 List.IsChain R l → l₁ <:+: l → List.IsChain R l₁
· 使用定理 `List.IsInfix.reverse`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₁
.reverse <:+: l₂.reverse
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.getLast_reverse`：∀ {α : Type u_1} {l : List α} (h : l.reverse ≠ [])
, l.reverse.getLast h = l.head ⋯
· 使用定理 `List.head_reverse`：∀ {α : Type u_1} {l : List α} (h : l.reverse ≠ []), l
.reverse.head h = l.getLast ⋯
-/
theorem WellFounded.listPairwise_reverse_compl (wf : WellFounded r) (h : l.IsChain r) :
    l.reverse.Pairwise rᶜ := by
  refine List.pairwise_iff_forall_infix.mpr fun l' hne hsub ↦ ?_
  have := wf.asymmetricₙ (by grind) <| h.infix <| l.reverse_reverse ▸ hsub.reverse
  simpa

/-! In this section, we consider the type of `r`-decreasing chains (`List.IsChain (flip r)`)
  equipped with lexicographic order `List.Lex r`. -/

variable (r)

/-- The type of `r`-decreasing chains -/
/-
**List.chains** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：List.chains
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of `r`-decreasing chains
-/
abbrev List.chains := { l : List α // l.IsChain (flip r) }

/-- The lexicographic order on the `r`-decreasing chains -/
/-
**List.lex_chains** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：List.lex_chains (l m : List.chains r) : Prop
参数：l m : List.chains r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographic order on the `r`-decreasing chains
-/
abbrev List.lex_chains (l m : List.chains r) : Prop := List.Lex r l.val m.val

variable {r}

/-- If an `r`-decreasing chain `l` is empty or its head is accessible by `r`, then
  `l` is accessible by the lexicographic order `List.Lex r`. -/
/-
**Acc.list_chain'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Acc.list_chain' {l : List.chains r} (acc : forall a in l.val.head?, Acc r 
a) : Acc (List.lex_chains r) l
参数：acc : forall a in l.val.head?, Acc r a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.isChain_cons`：isChain_cons {x l} : IsChain R (x :: l) ↔ (forall y i
n head? l, R x y) ∧ IsChain R l
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.isChain_cons_cons`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α} {l
 : List α},   List.IsChain R (a :: b :: l) ↔ R a b ∧ List.IsChain R (b :: l)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `List.head?_cons`：∀ {α : Type u} {a : α} {l : List α}, (a :: l).head? = s
ome a
· 使用定理 `Option.mem_some_iff`：∀ {α : Type u_1} {a b : α}, a ∈ some b ↔ b = a

--- 原说明 ---
If an `r`-decreasing chain `l` is empty or its head is accessible by `r`, then
  `l` is accessible by the lexicographic order `List.Lex r`.
-/
theorem Acc.list_chain' {l : List.chains r} (acc : ∀ a ∈ l.val.head?, Acc r a) :
    Acc (List.lex_chains r) l := by
  obtain ⟨_ | ⟨a, l⟩, hl⟩ := l
  · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
  specialize acc a _
  · rw [List.head?_cons, Option.mem_some_iff]
  /- For an r-decreasing chain of the form a :: l, apply induction on a -/
  induction acc generalizing l with
  | intro a _ ih =>
    /- Bundle l with a proof that it is r-decreasing to form l' -/
    have hl' := (List.isChain_cons.1 hl).2
    let l' : List.chains r := ⟨l, hl'⟩
    have : Acc (List.lex_chains r) l' := by
      rcases l with - | ⟨b, l⟩
      · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
      /- l' is accessible by induction hypothesis -/
      · apply ih b (List.isChain_cons_cons.1 hl).1
    /- make l' a free variable and induct on l' -/
    revert hl
    rw [(by rfl : l = l'.1)]
    clear_value l'
    induction this with
    | intro l _ ihl =>
      intro hl
      apply Acc.intro
      rintro ⟨_ | ⟨b, m⟩, hm⟩ (_ | hr | hr)
      · apply Acc.intro; rintro ⟨_⟩ ⟨_⟩
      · apply ih b hr
      · apply ihl ⟨m, (List.isChain_cons.1 hm).2⟩ hr

/-- If `r` is well-founded, the lexicographic order on `r`-decreasing chains is also. -/
/-
**WellFounded.list_chain'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：WellFounded.list_chain' (hwf : WellFounded r) : WellFounded (List.lex_chai
ns r)
参数：hwf : WellFounded r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Acc.list_chain'`：Acc.list_chain' {l : List.chains r} (acc : forall a in 
l.val.head?, Acc r a) : Acc (List.lex_chains r) l
· 使用定理 `WellFounded.apply`：∀ {α : Sort u} {r : α → α → Prop}, WellFounded r → ∀ 
(a : α), Acc r a

--- 原说明 ---
If `r` is well-founded, the lexicographic order on `r`-decreasing chains is also
.
-/
theorem WellFounded.list_chain' (hwf : WellFounded r) :
    WellFounded (List.lex_chains r) :=
  ⟨fun _ ↦ Acc.list_chain' (fun _ _ => hwf.apply _)⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hwf : IsWellFounded α r] :
    IsWellFounded (List.chains r) (List.lex_chains r) :=
  ⟨hwf.wf.list_chain'⟩
