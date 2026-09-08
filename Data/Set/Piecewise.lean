/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Andrew Zipperer, Haitao Zhang, Minchao Wu, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Function

/-!
# Piecewise functions

This file contains basic results on piecewise defined functions.
-/

public section

variable {α β γ δ : Type*} {ι : Sort*} {π : α → Type*}

open Equiv Equiv.Perm Function

namespace Set

variable {δ : α → Sort*} (s : Set α) (f g : ∀ i, δ i)

@[simp]
/-
**Set.piecewise_empty** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_empty [forall i : α, Decidable (i in (∅ : Set α))] : piecewise ∅
 f g = g
参数：i in (∅ : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piecewise_empty [∀ i : α, Decidable (i ∈ (∅ : Set α))] : piecewise ∅ f g = g := by
  ext i
  simp [piecewise]

@[simp]
/-
**Set.piecewise_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_univ [forall i : α, Decidable (i in (Set.univ : Set α))] : piece
wise Set.univ f g = f
参数：i in (Set.univ : Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piecewise_univ [∀ i : α, Decidable (i ∈ (Set.univ : Set α))] :
    piecewise Set.univ f g = f := by
  ext i
  simp [piecewise]
/-
**Set.piecewise_insert_self** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_insert_self {j : α} [forall i, Decidable (i in insert j s)] : (i
nsert j s).piecewise f g j = f j
参数：i in insert j s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem piecewise_insert_self {j : α} [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g j = f j := by simp [piecewise]

variable [∀ j, Decidable (j ∈ s)]
/-
**Set.piecewise_insert** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_insert [DecidableEq α] (j : α) [forall i, Decidable (i in insert
 j s)] : (insert j s).piecewise f g = Function.update (s.piecewise f g) j (f j)
参数：j : α；i in insert j s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem piecewise_insert [DecidableEq α] (j : α) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g = Function.update (s.piecewise f g) j (f j) := by
  simp +unfoldPartialApp only [piecewise, mem_insert_iff]
  ext i
  by_cases h : i = j
  · rw [h]
    simp
  · by_cases h' : i ∈ s <;> simp [h, h']

@[simp]
/-
**Set.piecewise_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_eq_of_mem {i : α} (hi : i in s) : s.piecewise f g i = f i
参数：hi : i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem piecewise_eq_of_mem {i : α} (hi : i ∈ s) : s.piecewise f g i = f i :=
  if_pos hi

@[simp]
/-
**Set.piecewise_eq_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i
参数：hi : i ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem piecewise_eq_of_notMem {i : α} (hi : i ∉ s) : s.piecewise f g i = g i :=
  if_neg hi
/-
**Set.piecewise_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_singleton (x : α) [forall y, Decidable (y in ({x} : Set α))] [De
cidableEq α] (f g : α -> β) : piecewise {x} f g = Function.update g x (f x)
参数：x : α；y in ({x} : Set α)；f g : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem piecewise_singleton (x : α) [∀ y, Decidable (y ∈ ({x} : Set α))] [DecidableEq α]
    (f g : α → β) : piecewise {x} f g = Function.update g x (f x) := by
  ext y
  by_cases hy : y = x
  · subst y
    simp
  · simp [hy]
/-
**Set.piecewise_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_eqOn (f g : α -> β) : EqOn (s.piecewise f g) f s
参数：f g : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
-/
theorem piecewise_eqOn (f g : α → β) : EqOn (s.piecewise f g) f s := fun _ =>
  piecewise_eq_of_mem _ _ _
/-
**Set.piecewise_eqOn_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_eqOn_compl (f g : α -> β) : EqOn (s.piecewise f g) g sᶜ
参数：f g : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
-/
theorem piecewise_eqOn_compl (f g : α → β) : EqOn (s.piecewise f g) g sᶜ := fun _ =>
  piecewise_eq_of_notMem _ _ _
/-
**Set.piecewise_le** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_le {δ : α -> Type*} [forall i, Preorder (δ i)] {s : Set α} [fora
ll j, Decidable (j in s)] {f₁ f₂ g : forall i, δ i} (h₁ : forall i in s, f₁ i <=
 g i) (h₂ : forall i ∉ s, f₂ i <= g i) : s.piecewise f₁ f₂ <= g
参数：δ i；j in s；h₁ : forall i in s, f₁ i <= g i；h₂ : forall i ∉ s, f₂ i <= g i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem piecewise_le {δ : α → Type*} [∀ i, Preorder (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g : ∀ i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g i) (h₂ : ∀ i ∉ s, f₂ i ≤ g i) :
    s.piecewise f₁ f₂ ≤ g := fun i => if h : i ∈ s then by simp [*] else by simp [*]
/-
**Set.le_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：le_piecewise {δ : α -> Type*} [forall i, Preorder (δ i)] {s : Set α} [fora
ll j, Decidable (j in s)] {f₁ f₂ g : forall i, δ i} (h₁ : forall i in s, g i <= 
f₁ i) (h₂ : forall i ∉ s, g i <= f₂ i) : g <= s.piecewise f₁ f₂
参数：δ i；j in s；h₁ : forall i in s, g i <= f₁ i；h₂ : forall i ∉ s, g i <= f₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_le`：piecewise_le {δ : α -> Type*} [forall i, Preorder (δ i
)] {s : Set α} [forall j, Decidable (j in s)] {f₁ f₂ g : forall i, δ i} (h₁ : fo
rall i…
-/
theorem le_piecewise {δ : α → Type*} [∀ i, Preorder (δ i)] {s : Set α} [∀ j, Decidable (j ∈ s)]
    {f₁ f₂ g : ∀ i, δ i} (h₁ : ∀ i ∈ s, g i ≤ f₁ i) (h₂ : ∀ i ∉ s, g i ≤ f₂ i) :
    g ≤ s.piecewise f₁ f₂ :=
  @piecewise_le α (fun i => (δ i)ᵒᵈ) _ s _ _ _ _ h₁ h₂

@[gcongr]
/-
**Set.piecewise_mono** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_mono {δ : α -> Type*} [forall i, Preorder (δ i)] {s : Set α} [fo
rall j, Decidable (j in s)] {f₁ f₂ g₁ g₂ : forall i, δ i} (h₁ : forall i in s, f
₁ i <= g₁ i) (h₂ : forall i ∉ s, f₂ i <= g₂ i) : s.piecewise f₁ f₂ <= s.piecewis
e g₁ g₂
参数：δ i；j in s；h₁ : forall i in s, f₁ i <= g₁ i；h₂ : forall i ∉ s, f₂ i <= g₂ i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.piecewise_le`：piecewise_le {δ : α -> Type*} [forall i, Preorder (δ i
)] {s : Set α} [forall j, Decidable (j in s)] {f₁ f₂ g : forall i, δ i} (h₁ : fo
rall i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem piecewise_mono {δ : α → Type*} [∀ i, Preorder (δ i)] {s : Set α}
    [∀ j, Decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : ∀ i, δ i} (h₁ : ∀ i ∈ s, f₁ i ≤ g₁ i)
    (h₂ : ∀ i ∉ s, f₂ i ≤ g₂ i) : s.piecewise f₁ f₂ ≤ s.piecewise g₁ g₂ := by
  apply piecewise_le <;> intros <;> simp [*]

@[simp]
/-
**Set.piecewise_insert_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_insert_of_ne {i j : α} (h : i != j) [forall i, Decidable (i in i
nsert j s)] : (insert j s).piecewise f g i = s.piecewise f g i
参数：h : i != j；i in insert j s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem piecewise_insert_of_ne {i j : α} (h : i ≠ j) [∀ i, Decidable (i ∈ insert j s)] :
    (insert j s).piecewise f g i = s.piecewise f g i := by simp [piecewise, h]

@[simp]
/-
**Set.piecewise_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_compl [forall i, Decidable (i in sᶜ)] : sᶜ.piecewise f g = s.pie
cewise g f
参数：i in sᶜ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
theorem piecewise_compl [∀ i, Decidable (i ∈ sᶜ)] : sᶜ.piecewise f g = s.piecewise g f :=
  funext fun x => if hx : x ∈ s then by simp [hx] else by simp [hx]

@[simp]
/-
**Set.piecewise_range_comp** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_range_comp {ι : Sort*} (f : ι -> α) [forall j, Decidable (j in r
ange f)] (g₁ g₂ : α -> β) : (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f
参数：f : ι -> α；j in range f；g₁ g₂ : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.comp_eq`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_7} {f : ι 
→ α} {g₁ g₂ : α → β},   Set.EqOn g₁ g₂ (Set.range f) → g₁ ∘ f = g₂ ∘ f
· 使用定理 `Set.piecewise_eqOn`：piecewise_eqOn (f g : α -> β) : EqOn (s.piecewise f 
g) f s
-/
theorem piecewise_range_comp {ι : Sort*} (f : ι → α) [∀ j, Decidable (j ∈ range f)]
    (g₁ g₂ : α → β) : (range f).piecewise g₁ g₂ ∘ f = g₁ ∘ f :=
  (piecewise_eqOn ..).comp_eq
/-
**Set.piecewise_comp** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：piecewise_comp (f g : α -> γ) (h : β -> α) : letI : DecidablePred (· in h 
⁻¹' s)
参数：f g : α -> γ；h : β -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma piecewise_comp (f g : α → γ) (h : β → α) :
    letI : DecidablePred (· ∈ h ⁻¹' s) := @instDecidablePredComp _ (· ∈ s) _ h _;
    (s.piecewise f g) ∘ h = (h ⁻¹' s).piecewise (f ∘ h) (g ∘ h) := rfl
/-
**Set.MapsTo.piecewise_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set.MapsTo`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {f₁ f₂
 : α → β}   [inst : (i : α) → Decidable (i ∈ s)],   Set.MapsTo f₁ (s₁ ∩ s) (t₁ ∩
 t) →     Set.MapsTo f₂ (s₂ ∩ sᶜ) (t₂ ∩ tᶜ) → Set.MapsTo (s.piecewise f₁ f₂) (s.
ite s₁ s₂) (t.ite t₁ t₂)
参数：i : α；i ∈ s；s₁ ∩ s；t₁ ∩ t；s₂ ∩ sᶜ；t₂ ∩ tᶜ；s.piecewise f₁ f₂；s.ite s₁ s₂；t.ite
 t₁ t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.MapsTo.union_union`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → Set.MapsTo f s₂ t₂ → Set.Map
sTo f (s₁ ∪ …
· 使用定理 `Set.MapsTo.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f₁ f₂ : α → β},   Set.MapsTo f₁ s t → Set.EqOn f₁ f₂ s → Set.MapsTo f₂ s t
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用定理 `Set.piecewise_eqOn`：piecewise_eqOn (f g : α -> β) : EqOn (s.piecewise f 
g) f s
· 使用定理 `Set.piecewise_eqOn_compl`：piecewise_eqOn_compl (f g : α -> β) : EqOn (s.
piecewise f g) g sᶜ
-/
theorem MapsTo.piecewise_ite {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {f₁ f₂ : α → β}
    [∀ i, Decidable (i ∈ s)] (h₁ : MapsTo f₁ (s₁ ∩ s) (t₁ ∩ t))
    (h₂ : MapsTo f₂ (s₂ ∩ sᶜ) (t₂ ∩ tᶜ)) :
    MapsTo (s.piecewise f₁ f₂) (s.ite s₁ s₂) (t.ite t₁ t₂) := by
  refine (h₁.congr ?_).union_union (h₂.congr ?_)
  exacts [(piecewise_eqOn s f₁ f₂).symm.mono inter_subset_right,
    (piecewise_eqOn_compl s f₁ f₂).symm.mono inter_subset_right]
/-
**Set.eqOn_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：eqOn_piecewise {f f' g : α -> β} {t} : EqOn (s.piecewise f f') g t ↔ EqOn 
f g (t inter s) ∧ EqOn f' g (t inter sᶜ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem eqOn_piecewise {f f' g : α → β} {t} :
    EqOn (s.piecewise f f') g t ↔ EqOn f g (t ∩ s) ∧ EqOn f' g (t ∩ sᶜ) := by
  simp only [EqOn, ← forall_and]
  refine forall_congr' fun a => ?_; by_cases a ∈ s <;> simp [*]
/-
**Set.EqOn.piecewise_ite'** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (s : Set α) [inst : (j : α) → Decidable (j
 ∈ s)] {f f' g : α → β} {t t' : Set α},   Set.EqOn f g (t ∩ s) → Set.EqOn f' g (
t' ∩ sᶜ) → Set.EqOn (s.piecewise f f') g (s.ite t t')
参数：s : Set α；j : α；j ∈ s；t ∩ s；t' ∩ sᶜ；s.piecewise f f'；s.ite t t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ite_inter_self`：ite_inter_self (t s s' : Set α) : t.ite s s' inter t
 = s inter t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.ite_inter_compl_self`：ite_inter_compl_self (t s s' : Set α) : t.ite 
s s' inter tᶜ = s' inter tᶜ
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem EqOn.piecewise_ite' {f f' g : α → β} {t t'} (h : EqOn f g (t ∩ s))
    (h' : EqOn f' g (t' ∩ sᶜ)) : EqOn (s.piecewise f f') g (s.ite t t') := by
  simp [eqOn_piecewise, *]
/-
**Set.EqOn.piecewise_ite** 是 Mathlib 中的一个定理，位于命名空间 `Set.EqOn`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (s : Set α) [inst : (j : α) → Decidable (j
 ∈ s)] {f f' g : α → β} {t t' : Set α},   Set.EqOn f g t → Set.EqOn f' g t' → Se
t.EqOn (s.piecewise f f') g (s.ite t t')
参数：s : Set α；j : α；j ∈ s；s.piecewise f f'；s.ite t t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.EqOn.piecewise_ite'`：∀ {α : Type u_1} {β : Type u_2} (s : Set α) [in
st : (j : α) → Decidable (j ∈ s)] {f f' g : α → β} {t t' : Set α},   Set.EqOn f 
g (t ∩ s) → S…
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem EqOn.piecewise_ite {f f' g : α → β} {t t'} (h : EqOn f g t) (h' : EqOn f' g t') :
    EqOn (s.piecewise f f') g (s.ite t t') :=
  (h.mono inter_subset_left).piecewise_ite' s (h'.mono inter_subset_left)
/-
**Set.piecewise_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_preimage (f g : α -> β) (t) : s.piecewise f g ⁻¹' t = s.ite (f ⁻
¹' t) (g ⁻¹' t)
参数：f g : α -> β；t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem piecewise_preimage (f g : α → β) (t) : s.piecewise f g ⁻¹' t = s.ite (f ⁻¹' t) (g ⁻¹' t) :=
  ext fun x => by by_cases x ∈ s <;> simp [*, Set.ite]
/-
**Set.apply_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：apply_piecewise {δ' : α -> Sort*} (h : forall i, δ i -> δ' i) {x : α} : h 
x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) (fun x => h x (g x)) x
参数：h : forall i, δ i -> δ' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem apply_piecewise {δ' : α → Sort*} (h : ∀ i, δ i → δ' i) {x : α} :
    h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) (fun x => h x (g x)) x := by
  by_cases hx : x ∈ s <;> simp [hx]
/-
**Set.apply_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：apply_piecewise {δ' : α -> Sort*} (h : forall i, δ i -> δ' i) {x : α} : h 
x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) (fun x => h x (g x)) x
参数：h : forall i, δ i -> δ' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem apply_piecewise₂ {δ' δ'' : α → Sort*} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i)
    {x : α} :
    h x (s.piecewise f g x) (s.piecewise f' g' x) =
      s.piecewise (fun x => h x (f x) (f' x)) (fun x => h x (g x) (g' x)) x := by
  by_cases hx : x ∈ s <;> simp [hx]
/-
**Set.piecewise_op** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_op {δ' : α -> Sort*} (h : forall i, δ i -> δ' i) : (s.piecewise 
(fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.piecewise f g x)
参数：h : forall i, δ i -> δ' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.apply_piecewise`：apply_piecewise {δ' : α -> Sort*} (h : forall i, δ 
i -> δ' i) {x : α} : h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) 
(fun x =>…
-/
theorem piecewise_op {δ' : α → Sort*} (h : ∀ i, δ i → δ' i) :
    (s.piecewise (fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.piecewise f g x) :=
  funext fun _ => (apply_piecewise _ _ _ _).symm
/-
**Set.piecewise_op** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_op {δ' : α -> Sort*} (h : forall i, δ i -> δ' i) : (s.piecewise 
(fun x => h x (f x)) fun x => h x (g x)) = fun x => h x (s.piecewise f g x)
参数：h : forall i, δ i -> δ' i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.apply_piecewise`：apply_piecewise {δ' : α -> Sort*} (h : forall i, δ 
i -> δ' i) {x : α} : h x (s.piecewise f g x) = s.piecewise (fun x => h x (f x)) 
(fun x =>…
-/
theorem piecewise_op₂ {δ' δ'' : α → Sort*} (f' g' : ∀ i, δ' i) (h : ∀ i, δ i → δ' i → δ'' i) :
    (s.piecewise (fun x => h x (f x) (f' x)) fun x => h x (g x) (g' x)) = fun x =>
      h x (s.piecewise f g x) (s.piecewise f' g' x) :=
  funext fun _ => (apply_piecewise₂ _ _ _ _ _ _).symm

@[simp]
/-
**Set.piecewise_same** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_same : s.piecewise f f = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem piecewise_same : s.piecewise f f = f := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]
/-
**Set.range_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：range_piecewise (f g : α -> β) : range (s.piecewise f g) = f '' s union g 
'' sᶜ
参数：f g : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem range_piecewise (f g : α → β) : range (s.piecewise f g) = f '' s ∪ g '' sᶜ := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    by_cases h : x ∈ s <;> [left; right] <;> use x <;> simp [h]
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) <;> use x <;> simp_all
/-
**Set.injective_piecewise_iff** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：injective_piecewise_iff {f g : α -> β} : Injective (s.piecewise f g) ↔ Inj
On f s ∧ InjOn g sᶜ ∧ forall x in s, forall y ∉ s, f x != g y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.injOn_univ`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.InjOn f
 Set.univ ↔ Function.Injective f
· 使用定理 `Set.union_compl_self`：union_compl_self (s : Set α) : s union sᶜ = univ
· 使用定理 `Set.injOn_union`：injOn_union (h : Disjoint s₁ s₂) : InjOn f (s₁ union s₂
) ↔ InjOn f s₁ ∧ InjOn f s₂ ∧ forall x in s₁, forall y in s₂, f x != f y
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Set.EqOn.injOn_iff`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ :
 α → β}, Set.EqOn f₁ f₂ s → (Set.InjOn f₁ s ↔ Set.InjOn f₂ s)
· 使用定理 `Set.piecewise_eqOn`：piecewise_eqOn (f g : α -> β) : EqOn (s.piecewise f 
g) f s
· 使用定理 `Set.piecewise_eqOn_compl`：piecewise_eqOn_compl (f g : α -> β) : EqOn (s.
piecewise f g) g sᶜ
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `forall₄_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {δ : (a : α) → (b : β a) → γ a b → Sort u_4}   {p q : (a : α) → (b : β
 a)…
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
-/
theorem injective_piecewise_iff {f g : α → β} :
    Injective (s.piecewise f g) ↔
      InjOn f s ∧ InjOn g sᶜ ∧ ∀ x ∈ s, ∀ y ∉ s, f x ≠ g y := by
  rw [← injOn_univ, ← union_compl_self s, injOn_union (@disjoint_compl_right _ _ s),
    (piecewise_eqOn s f g).injOn_iff, (piecewise_eqOn_compl s f g).injOn_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl <| forall₄_congr fun x hx y hy => ?_)
  rw [piecewise_eq_of_mem s f g hx, piecewise_eq_of_notMem s f g hy]
/-
**Set.piecewise_mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：piecewise_mem_pi {δ : α -> Type*} {t : Set α} {t' : forall i, Set (δ i)} {
f g} (hf : f in pi t t') (hg : g in pi t t') : s.piecewise f g in pi t t'
参数：δ i；hf : f in pi t t'；hg : g in pi t t'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem piecewise_mem_pi {δ : α → Type*} {t : Set α} {t' : ∀ i, Set (δ i)} {f g} (hf : f ∈ pi t t')
    (hg : g ∈ pi t t') : s.piecewise f g ∈ pi t t' := by
  intro i ht
  by_cases hs : i ∈ s <;> simp [hf i ht, hg i ht, hs]

@[simp]
/-
**Set.pi_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pi_piecewise {ι : Type*} {α : ι -> Type*} (s s' : Set ι) (t t' : forall i,
 Set (α i)) [forall x, Decidable (x in s')] : pi s (s'.piecewise t t') = pi (s i
nter s') t inter pi (s \ s') t'
参数：s s' : Set ι；t t' : forall i, Set (α i)；x in s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pi_if`：pi_if {p : ι -> Prop} [h : DecidablePred p] (s : Set ι) (t₁ t
₂ : forall i, Set (α i)) : (pi s fun i => if p i then t₁ i else t₂ i) = pi ({ i…
-/
theorem pi_piecewise {ι : Type*} {α : ι → Type*} (s s' : Set ι) (t t' : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s')] : pi s (s'.piecewise t t') = pi (s ∩ s') t ∩ pi (s \ s') t' :=
  pi_if _ _ _
/-
**Set.univ_pi_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_piecewise {ι : Type*} {α : ι -> Type*} (s : Set ι) (t t' : forall 
i, Set (α i)) [forall x, Decidable (x in s)] : pi univ (s.piecewise t t') = pi s
 t inter pi sᶜ t'
参数：s : Set ι；t t' : forall i, Set (α i)；x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pi_piecewise`：pi_piecewise {ι : Type*} {α : ι -> Type*} (s s' : Set 
ι) (t t' : forall i, Set (α i)) [forall x, Decidable (x in s')] : pi s (s'.piece
wise t…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Set.compl_eq_univ_sdiff`：compl_eq_univ_sdiff (s : Set α) : sᶜ = univ \ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_pi_piecewise {ι : Type*} {α : ι → Type*} (s : Set ι) (t t' : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s)] : pi univ (s.piecewise t t') = pi s t ∩ pi sᶜ t' := by
  simp [compl_eq_univ_sdiff]
/-
**Set.univ_pi_piecewise_univ** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：univ_pi_piecewise_univ {ι : Type*} {α : ι -> Type*} (s : Set ι) (t : foral
l i, Set (α i)) [forall x, Decidable (x in s)] : pi univ (s.piecewise t fun _ =>
 univ) = pi s t
参数：s : Set ι；t : forall i, Set (α i)；x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.pi_piecewise`：pi_piecewise {ι : Type*} {α : ι -> Type*} (s s' : Set 
ι) (t t' : forall i, Set (α i)) [forall x, Decidable (x in s')] : pi s (s'.piece
wise t…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem univ_pi_piecewise_univ {ι : Type*} {α : ι → Type*} (s : Set ι) (t : ∀ i, Set (α i))
    [∀ x, Decidable (x ∈ s)] : pi univ (s.piecewise t fun _ => univ) = pi s t := by simp

end Set

