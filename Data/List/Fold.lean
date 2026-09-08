/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Batteries.Tactic.Alias
public import Mathlib.Logic.OpClass

/-!
# Bird–Wadler duality of list folds

In their 1988 book _Introduction to Functional Programming_ [birdwadler],
Richard Bird and Philip Wadler stated three duality theorems between `foldl` and `foldr`.
Denoting the combining function as `f`, the theorems are:

1. If `α = β` and `f` is commutative and associative, `l.foldl = l.foldr`
2. If `f` is left-commutative, `l.foldl = l.foldr`
3. `l.reverse.foldl = l.foldr` and `l.reverse.foldr = l.foldl`

Note that `f`'s type differs between Lean's `foldl` (`β → α → β`) and `foldr` (`α → β → β`),
so `flip`s need to be inserted judiciously. For the history behind this type difference
see the appendix to [danvy], which uses a version of `foldl` where `f : α → β → β` to derive
among other things a slight generalisation of the first theorem:

1. If `α = β`, `f` is associative and `a` commutes with all `x : α`, `l.foldl f a = l.foldr f a`

## Main declarations

* `List.foldl_eq_foldr_of_commute`, `List.foldl_eq_foldr`: first duality theorem.
* `List.foldl_flip_eq_foldr`, `List.foldr_flip_eq_foldl`: second duality theorem.

The third duality theorem is in the standard library under the names
`List.foldl_reverse`, `List.foldr_eq_foldl_reverse`,
`List.foldr_reverse` and `List.foldl_eq_foldr_reverse`.
-/

public section

namespace List

variable {α β : Type*} {l : List α} {f : α → β → β} {v : β → α → β} {a : α} {b : β}

/-
**List.foldl_cons_nil** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：foldl_cons_nil : l.foldl (flip cons) [] = l.reverse
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldl_eq_foldr_reverse`：∀ {α : Type u_1} {β : Type u_2} {l : List α
} {f : β → α → β} {b : β},   List.foldl f b l = List.foldr (fun x y => f y x) b 
l.reverse
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.foldr_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {b : 
β} {l l' : List α},   List.foldr f b (l ++ l') = List.foldr f (List.foldr f b l'
) l
· 使用定理 `List.foldr_cons_eq_append'`：∀ {β : Type u_1} {l l' : List β}, List.foldr
 List.cons l' l = l ++ l'
-/
lemma foldl_cons_nil : l.foldl (flip cons) [] = l.reverse := by
  induction l <;> simp [flip, foldl_eq_foldr_reverse, -foldr_reverse]
/-
**List.foldl_cons_eq_apply_foldl** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：foldl_cons_eq_apply_foldl [hv : RightCommutative v] : (a :: l).foldl v b =
 v (l.foldl v b) a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldl_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : β
 → α → β} {b : β},   List.foldl f b (a :: l) = List.foldl f (f b a) l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RightCommutative.right_comm`：∀ {α : Sort u} {β : Sort v} {op : β → α → β
} [self : RightCommutative op] (b : β) (a₁ a₂ : α),   op (op b a₁) a₂ = op (op b
 a₂) a₁
-/
lemma foldl_cons_eq_apply_foldl [hv : RightCommutative v] :
    (a :: l).foldl v b = v (l.foldl v b) a := by
  rw [foldl_cons]
  induction l generalizing a b <;> simp [*, hv.right_comm]
/-
**List.foldr_cons_eq_foldr_apply** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：foldr_cons_eq_foldr_apply [hf : LeftCommutative f] : (a :: l).foldr f b = 
l.foldr f (f a b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldr_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : α
 → β → β} {b : β},   List.foldr f b (a :: l) = f a (List.foldr f b l)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LeftCommutative.left_comm`：∀ {α : Sort u} {β : Sort v} {op : α → β → β} 
[self : LeftCommutative op] (a₁ a₂ : α) (b : β),   op a₁ (op a₂ b) = op a₂ (op a
₁ b)
-/
lemma foldr_cons_eq_foldr_apply [hf : LeftCommutative f] :
    (a :: l).foldr f b = l.foldr f (f a b) := by
  rw [foldr_cons]
  induction l generalizing a b <;> simp [*, hf.left_comm]
/-
**List.foldl1_eq_foldr1** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：foldl1_eq_foldr1 {f : α -> α -> α} [ha : Std.Associative f] {a b : α} : f 
(l.foldl f a) b = f a (l.foldr f b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Std.Associative.assoc`：∀ {α : Sort u} {op : α → α → α} [self : Std.Assoc
iative op] (a b c : α), op (op a b) c = op a (op b c)
-/
lemma foldl1_eq_foldr1 {f : α → α → α} [ha : Std.Associative f] {a b : α} :
    f (l.foldl f a) b = f a (l.foldr f b) := by
  induction l generalizing a <;> simp [*, ha.assoc]

/-- **First Bird–Wadler duality theorem**. -/
/-
**List.foldl_eq_foldr_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_eq_foldr_of_commute {f : α -> α -> α} [Std.Associative f] (ha : fora
ll x, f a x = f x a) : l.foldl f a = l.foldr f a
参数：ha : forall x, f a x = f x a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldl_assoc`：∀ {α : Type u_1} {op : α → α → α} [ha : Std.Associativ
e op] {l : List α} {a₁ a₂ : α},   List.foldl op (op a₁ a₂) l = op a₁ (List.foldl
 op a₂…

--- 原说明 ---
**First Bird–Wadler duality theorem**.
-/
theorem foldl_eq_foldr_of_commute {f : α → α → α} [Std.Associative f] (ha : ∀ x, f a x = f x a) :
    l.foldl f a = l.foldr f a := by
  induction l <;> simp [*, foldl_assoc]

/-- **First Bird–Wadler duality theorem** for commutative functions. -/
/-
**List.foldl_eq_foldr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_eq_foldr {f : α -> α -> α} [hf : Std.Commutative f] [Std.Associative
 f] : l.foldl f a = l.foldr f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.foldl_eq_foldr_of_commute`：foldl_eq_foldr_of_commute {f : α -> α ->
 α} [Std.Associative f] (ha : forall x, f a x = f x a) : l.foldl f a = l.foldr f
 a
· 使用定理 `Std.Commutative.comm`：∀ {α : Sort u} {op : α → α → α} [self : Std.Commut
ative op] (a b : α), op a b = op b a

--- 原说明 ---
**First Bird–Wadler duality theorem** for commutative functions.
-/
theorem foldl_eq_foldr {f : α → α → α} [hf : Std.Commutative f] [Std.Associative f] :
    l.foldl f a = l.foldr f a :=
  foldl_eq_foldr_of_commute (hf.comm a)

/-- **Second Bird–Wadler duality theorem**. -/
/-
**List.foldl_flip_eq_foldr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldl_flip_eq_foldr [LeftCommutative f] : l.foldl (flip f) b = l.foldr f b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.foldr_cons_eq_foldr_apply`：foldr_cons_eq_foldr_apply [hf : LeftComm
utative f] : (a :: l).foldr f b = l.foldr f (f a b)

--- 原说明 ---
**Second Bird–Wadler duality theorem**.
-/
theorem foldl_flip_eq_foldr [LeftCommutative f] : l.foldl (flip f) b = l.foldr f b := by
  induction l generalizing b <;> simp [*, flip, foldr_cons_eq_foldr_apply, -foldr_cons]

/-- **Second Bird–Wadler duality theorem**. -/
/-
**List.foldr_flip_eq_foldl** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldr_flip_eq_foldl [RightCommutative v] : l.foldr (flip v) b = l.foldl v 
b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `List.foldl_cons_eq_apply_foldl`：foldl_cons_eq_apply_foldl [hv : RightCom
mutative v] : (a :: l).foldl v b = v (l.foldl v b) a

--- 原说明 ---
**Second Bird–Wadler duality theorem**.
-/
theorem foldr_flip_eq_foldl [RightCommutative v] : l.foldr (flip v) b = l.foldl v b := by
  induction l generalizing b <;> simp [*, flip, foldl_cons_eq_apply_foldl, -foldl_cons]

@[deprecated (since := "2026-04-02")] alias foldl_eq_of_comm' := foldl_cons_eq_apply_foldl
@[deprecated (since := "2026-04-02")] alias foldr_eq_of_comm' := foldr_cons_eq_foldr_apply
@[deprecated (since := "2026-04-02")] alias foldl_eq_foldr' := foldr_flip_eq_foldl
@[deprecated (since := "2026-04-02")] alias foldl_eq_of_comm_of_assoc := foldl_cons_eq_apply_foldl
@[deprecated (since := "2026-04-02")] alias foldl_op_eq_op_foldr_assoc := foldl1_eq_foldr1
@[deprecated (since := "2026-04-02")] alias foldl_assoc_comm_cons := foldl_cons_eq_apply_foldl

end List

