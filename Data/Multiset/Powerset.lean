/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Sublists
public import Mathlib.Data.List.Zip
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Range

/-!
# The powerset of a multiset
-/

@[expose] public section

namespace Multiset

open List

variable {α : Type*}

/-! ### powerset -/

-- TODO: Write a more efficient version (this is slightly slower due to the `map (↑)`).
/-- A helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` as multisets. -/
/-
**Multiset.powersetAux** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：powersetAux (l : List α) : List (Multiset α)
参数：l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper function for the powerset of a multiset. Given a list `l`, returns a li
st
of sublists of `l` as multisets.
-/
def powersetAux (l : List α) : List (Multiset α) :=
  (sublists l).map (↑)
/-
**Multiset.powersetAux_eq_map_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetAux_eq_map_coe {l : List α} : powersetAux l = (sublists l).map (↑)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powersetAux_eq_map_coe {l : List α} : powersetAux l = (sublists l).map (↑) :=
  rfl

@[simp]
/-
**Multiset.mem_powersetAux** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_powersetAux {l : List α} {s} : s in powersetAux l ↔ s <= ↑l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mem_powersetAux {l : List α} {s} : s ∈ powersetAux l ↔ s ≤ ↑l :=
  Quotient.inductionOn s <| by simp [powersetAux_eq_map_coe, Subperm, and_comm]

/-- Helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists'`), as multisets. -/
/-
**Multiset.powersetAux'** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：powersetAux' (l : List α) : List (Multiset α)
参数：l : List α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]

--- 原说明 ---
Helper function for the powerset of a multiset. Given a list `l`, returns a list
of sublists of `l` (using `sublists'`), as multisets.
-/
def powersetAux' (l : List α) : List (Multiset α) :=
  (sublists' l).map (↑)
/-
**Multiset.powersetAux_perm_powersetAux'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetAux_perm_powersetAux' {l : List α} : powersetAux l ~ powersetAux' 
l
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetAux_eq_map_coe`：powersetAux_eq_map_coe {l : List α} : p
owersetAux l = (sublists l).map (↑)
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `List.sublists_perm_sublists'`：sublists_perm_sublists' (l : List α) : sub
lists l ~ sublists' l
-/
theorem powersetAux_perm_powersetAux' {l : List α} : powersetAux l ~ powersetAux' l := by
  rw [powersetAux_eq_map_coe]; exact (sublists_perm_sublists' _).map _

@[simp]
/-
**Multiset.powersetAux'_nil** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1}, Multiset.powersetAux' [] = [0]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powersetAux'_nil : powersetAux' (@nil α) = [0] :=
  rfl

@[simp]
/-
**Multiset.powersetAux'_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (a : α) (l : List α),   Multiset.powersetAux' (a :: l) = 
Multiset.powersetAux' l ++ List.map (Multiset.cons a) (Multiset.powersetAux' l)
参数：a : α；l : List α；a :: l；Multiset.cons a；Multiset.powersetAux' l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists'_cons`：∀ {α : Type u} (a : α) (l : List α), (a :: l).subli
sts' = l.sublists' ++ List.map (List.cons a) l.sublists'
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.append_cancel_left_eq`：∀ {α : Type u_1} (as bs cs : List α), (as ++
 bs = as ++ cs) = (bs = cs)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem powersetAux'_cons (a : α) (l : List α) :
    powersetAux' (a :: l) = powersetAux' l ++ List.map (cons a) (powersetAux' l) := by
  simp [powersetAux']
/-
**Multiset.powerset_aux'_perm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (Multiset.powersetAux' l₁)
.Perm (Multiset.powersetAux' l₂)
参数：Multiset.powersetAux' l₁；Multiset.powersetAux' l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetAux'_cons`：∀ {α : Type u_1} (a : α) (l : List α),   Mul
tiset.powersetAux' (a :: l) = Multiset.powersetAux' l ++ List.map (Multiset.cons
 a) (Multiset.po…
· 使用定理 `List.Perm.append`：∀ {α : Type u_1} {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → 
t₁.Perm t₂ → (l₁ ++ t₁).Perm (l₂ ++ t₂)
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.Perm.append_left`：∀ {α : Type u_1} {t₁ t₂ : List α} (l : List α), t
₁.Perm t₂ → (l ++ t₁).Perm (l ++ t₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.cons_swap`：cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s
 = b ::ₘ a ::ₘ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.Perm.append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} (t₁ : List α),
 l₁.Perm l₂ → (l₁ ++ t₁).Perm (l₂ ++ t₁)
· 使用定理 `List.perm_append_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, (l₁ ++ l₂).Per
m (l₂ ++ l₁)
-/
theorem powerset_aux'_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux' l₁ ~ powersetAux' l₂ := by
  induction p with
  | nil => simp
  | cons _ _ IH =>
    simp only [powersetAux'_cons]
    exact IH.append (IH.map _)
  | swap a b =>
    simp only [powersetAux'_cons, map_append, List.map_map, append_assoc]
    apply Perm.append_left
    rw [← append_assoc, ← append_assoc,
      (by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂
/-
**Multiset.powersetAux_perm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux l₁ ~ powerse
tAux l₂
参数：p : l₁ ~ l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.powersetAux_perm_powersetAux'`：powersetAux_perm_powersetAux' {l
 : List α} : powersetAux l ~ powersetAux' l
· 使用定理 `Multiset.powerset_aux'_perm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm 
l₂ → (Multiset.powersetAux' l₁).Perm (Multiset.powersetAux' l₂)
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
-/
theorem powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux l₁ ~ powersetAux l₂ :=
  powersetAux_perm_powersetAux'.trans <|
    (powerset_aux'_perm p).trans powersetAux_perm_powersetAux'.symm

/-- The power set of a multiset. -/
/-
**Multiset.powerset** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：powerset (s : Multiset α) : Multiset (Multiset α)
参数：s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The power set of a multiset.
-/
def powerset (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s
    (fun l => (powersetAux l : Multiset (Multiset α)))
    (fun _ _ h => Quot.sound (powersetAux_perm h))
/-
**Multiset.powerset_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powerset_coe (l : List α) : @powerset α l = ((sublists l).map (↑) : List (
Multiset α))
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.powersetAux_eq_map_coe`：powersetAux_eq_map_coe {l : List α} : p
owersetAux l = (sublists l).map (↑)
-/
theorem powerset_coe (l : List α) : @powerset α l = ((sublists l).map (↑) : List (Multiset α)) :=
  congr_arg ((↑) : List (Multiset α) → Multiset (Multiset α)) powersetAux_eq_map_coe

@[simp]
/-
**Multiset.powerset_coe'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powerset_coe' (l : List α) : @powerset α l = ((sublists' l).map (↑) : List
 (Multiset α))
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `Multiset.powersetAux_perm_powersetAux'`：powersetAux_perm_powersetAux' {l
 : List α} : powersetAux l ~ powersetAux' l
-/
theorem powerset_coe' (l : List α) : @powerset α l = ((sublists' l).map (↑) : List (Multiset α)) :=
  Quot.sound powersetAux_perm_powersetAux'

@[simp]
/-
**Multiset.powerset_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powerset_zero : @powerset α 0 = {0}
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powerset_zero : @powerset α 0 = {0} :=
  rfl

@[simp]
/-
**Multiset.powerset_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powerset_cons (a : α) (s) : powerset (a ::ₘ s) = powerset s + map (cons a)
 (powerset s)
参数：a : α；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powerset_coe'`：powerset_coe' (l : List α) : @powerset α l = ((s
ublists' l).map (↑) : List (Multiset α))
· 使用定理 `List.sublists'_cons`：∀ {α : Type u} (a : α) (l : List α), (a :: l).subli
sts' = l.sublists' ++ List.map (List.cons a) l.sublists'
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powerset_cons (a : α) (s) : powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s) :=
  Quotient.inductionOn s fun l => by simp [Function.comp_def]

@[simp]
/-
**Multiset.mem_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_powerset {s t : Multiset α} : s in powerset t ↔ s <= t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.powerset_coe'`：powerset_coe' (l : List α) : @powerset α l = ((s
ublists' l).map (↑) : List (Multiset α))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mem_powerset {s t : Multiset α} : s ∈ powerset t ↔ s ≤ t :=
  Quotient.inductionOn₂ s t <| by simp [Subperm, and_comm]
/-
**Multiset.map_single_le_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_single_le_powerset (s : Multiset α) : s.map singleton <= powerset s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powerset_coe`：powerset_coe (l : List α) : @powerset α l = ((sub
lists l).map (↑) : List (Multiset α))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
· 使用定理 `List.map_pure_sublist_sublists`：map_pure_sublist_sublists (l : List α) :
 map pure l <+ sublists l
-/
theorem map_single_le_powerset (s : Multiset α) : s.map singleton ≤ powerset s :=
  Quotient.inductionOn s fun l => by
    simp only [powerset_coe, quot_mk_to_coe, coe_le, map_coe]
    change l.map (((↑) : List α → Multiset α) ∘ pure) <+~ (sublists l).map (↑)
    rw [← List.map_map]
    exact ((map_pure_sublist_sublists _).map _).subperm
/-
**Multiset.zero_mem_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_mem_powerset (s : Multiset α) : 0 in s.powerset
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_powerset`：mem_powerset {s t : Multiset α} : s in powerset t
 ↔ s <= t
· 使用定理 `Multiset.zero_le`：zero_le (s : Multiset α) : 0 <= s
-/
theorem zero_mem_powerset (s : Multiset α) : 0 ∈ s.powerset :=
  Multiset.mem_powerset.mpr s.zero_le
/-
**Multiset.self_mem_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：self_mem_powerset (s : Multiset α) : s in s.powerset
参数：s : Multiset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_powerset`：mem_powerset {s t : Multiset α} : s in powerset t
 ↔ s <= t
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem self_mem_powerset (s : Multiset α) : s ∈ s.powerset :=
  Multiset.mem_powerset.mpr le_rfl

@[simp]
/-
**Multiset.card_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_powerset (s : Multiset α) : card (powerset s) = 2 ^ card s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `Multiset.powerset_coe'`：powerset_coe' (l : List α) : @powerset α l = ((s
ublists' l).map (↑) : List (Multiset α))
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_sublists'`：∀ {α : Type u} (l : List α), l.sublists'.length =
 2 ^ l.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem card_powerset (s : Multiset α) : card (powerset s) = 2 ^ card s :=
  Quotient.inductionOn s <| by simp

@[simp]
/-
**Multiset.powerset_eq_singleton_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powerset_eq_singleton_zero_iff (s : Multiset α) : powerset s = {0} ↔ s = 0
 where mpr
参数：s : Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_powerset`：card_powerset (s : Multiset α) : card (powerset 
s) = 2 ^ card s
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Multiset.powerset_zero`：powerset_zero : @powerset α 0 = {0}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem powerset_eq_singleton_zero_iff (s : Multiset α) : powerset s = {0} ↔ s = 0 where
  mpr := by
    intro rfl
    exact powerset_zero
  mp powerset := by
    simpa using congr(card $powerset)
/-
**Multiset.revzip_powersetAux** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：revzip_powersetAux {l : List α} ⦃x⦄ (h : x in revzip (powersetAux l)) : x.
1 + x.2 = ↑l
参数：h : x in revzip (powersetAux l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.revzip.eq_1`：∀ {α : Type u_1} (l : List α), l.revzip = l.zip l.reve
rse
· 使用定理 `List.zip_map`：∀ {α : Type u_1} {γ : Type u_2} {β : Type u_3} {δ : Type u
_4} {f : α → γ} {g : β → δ} {l₁ : List α} {l₂ : List β},   (List.map f l₁).zip (
Li…
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `Multiset.powersetAux_eq_map_coe`：powersetAux_eq_map_coe {l : List α} : p
owersetAux l = (sublists l).map (↑)
· 使用定理 `List.revzip_sublists`：revzip_sublists (l l₁ l₂ : List α) (h : (l₁, l₂) i
n revzip l.sublists) : l₁ ++ l₂ ~ l
-/
theorem revzip_powersetAux {l : List α} ⦃x⦄ (h : x ∈ revzip (powersetAux l)) : x.1 + x.2 = ↑l := by
  rw [revzip, powersetAux_eq_map_coe, ← map_reverse, zip_map, ← revzip, List.mem_map] at h
  simp only [Prod.map_apply, Prod.exists] at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists _ _ _ h)
/-
**Multiset.revzip_powersetAux'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：revzip_powersetAux' {l : List α} ⦃x⦄ (h : x in revzip (powersetAux' l)) : 
x.1 + x.2 = ↑l
参数：h : x in revzip (powersetAux' l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.revzip.eq_1`：∀ {α : Type u_1} (l : List α), l.revzip = l.zip l.reve
rse
· 使用定理 `List.zip_map`：∀ {α : Type u_1} {γ : Type u_2} {β : Type u_3} {δ : Type u
_4} {f : α → γ} {g : β → δ} {l₁ : List α} {l₂ : List β},   (List.map f l₁).zip (
Li…
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `Multiset.powersetAux'.eq_1`：∀ {α : Type u_1} (l : List α), Multiset.powe
rsetAux' l = List.map Multiset.ofList l.sublists'
· 使用定理 `List.revzip_sublists'`：revzip_sublists' (l l₁ l₂ : List α) (h : (l₁, l₂)
 in revzip l.sublists') : l₁ ++ l₂ ~ l
-/
theorem revzip_powersetAux' {l : List α} ⦃x⦄ (h : x ∈ revzip (powersetAux' l)) :
    x.1 + x.2 = ↑l := by
  rw [revzip, powersetAux', ← map_reverse, zip_map, ← revzip, List.mem_map] at h
  simp only [Prod.map_apply, Prod.exists] at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists' _ _ _ h)
/-
**Multiset.revzip_powersetAux_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：revzip_powersetAux_lemma {α : Type*} [DecidableEq α] (l : List α) {l' : Li
st (Multiset α)} (H : forall ⦃x : _ × _⦄, x in revzip l' -> x.1 + x.2 = ↑l) : re
vzip l' = l'.map fun x => (x, (l : Multiset α) - x)
参数：l : List α；Multiset α；H : forall ⦃x : _ × _⦄, x in revzip l' -> x.1 + x.2 = ↑
l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.forall₂_map_right_iff`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_
3} {R : α → β → Prop} {f : γ → β} {l : List α} {u : List γ},   List.Forall₂ R l 
(List.map f u) ↔…
· 使用定理 `List.forall₂_same`：∀ {α : Type u_1} {Rₐ : α → α → Prop} {l : List α}, Li
st.Forall₂ Rₐ l l ↔ ∀ x ∈ l, Rₐ x x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `Multiset.instOrderedSub`：∀ {α : Type u_1} [inst : DecidableEq α], Ordere
dSub (Multiset α)
· 使用定理 `List.forall₂_eq_eq_eq`：forall₂_eq_eq_eq : Forall₂ ((· = ·) : α -> α -> P
rop) = Eq
· 使用定理 `List.revzip_map_fst`：revzip_map_fst (l : List α) : (revzip l).map Prod.f
st = l
-/
theorem revzip_powersetAux_lemma {α : Type*} [DecidableEq α] (l : List α) {l' : List (Multiset α)}
    (H : ∀ ⦃x : _ × _⦄, x ∈ revzip l' → x.1 + x.2 = ↑l) :
    revzip l' = l'.map fun x => (x, (l : Multiset α) - x) := by
  have :
    Forall₂ (fun (p : Multiset α × Multiset α) (s : Multiset α) => p = (s, ↑l - s)) (revzip l')
      ((revzip l').map Prod.fst) := by
    rw [forall₂_map_right_iff, forall₂_same]
    rintro ⟨s, t⟩ h
    dsimp
    rw [← H h, add_tsub_cancel_left]
  rw [← forall₂_eq_eq_eq, forall₂_map_right_iff]
  simpa using this
/-
**Multiset.revzip_powersetAux_perm_aux'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：revzip_powersetAux_perm_aux' {l : List α} : revzip (powersetAux l) ~ revzi
p (powersetAux' l)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.revzip_powersetAux_lemma`：revzip_powersetAux_lemma {α : Type*} 
[DecidableEq α] (l : List α) {l' : List (Multiset α)} (H : forall ⦃x : _ × _⦄, x
 in revzip l' -> x.1 + …
· 使用定理 `Multiset.revzip_powersetAux`：revzip_powersetAux {l : List α} ⦃x⦄ (h : x 
in revzip (powersetAux l)) : x.1 + x.2 = ↑l
· 使用定理 `Multiset.revzip_powersetAux'`：revzip_powersetAux' {l : List α} ⦃x⦄ (h : 
x in revzip (powersetAux' l)) : x.1 + x.2 = ↑l
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `Multiset.powersetAux_perm_powersetAux'`：powersetAux_perm_powersetAux' {l
 : List α} : powersetAux l ~ powersetAux' l
-/
theorem revzip_powersetAux_perm_aux' {l : List α} :
    revzip (powersetAux l) ~ revzip (powersetAux' l) := by
  have := Classical.decEq α
  rw [revzip_powersetAux_lemma l revzip_powersetAux, revzip_powersetAux_lemma l revzip_powersetAux']
  exact powersetAux_perm_powersetAux'.map _
/-
**Multiset.revzip_powersetAux_perm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：revzip_powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : revzip (powersetA
ux l₁) ~ revzip (powersetAux l₂)
参数：p : l₁ ~ l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.revzip_powersetAux_lemma`：revzip_powersetAux_lemma {α : Type*} 
[DecidableEq α] (l : List α) {l' : List (Multiset α)} (H : forall ⦃x : _ × _⦄, x
 in revzip l' -> x.1 + …
· 使用定理 `Multiset.revzip_powersetAux`：revzip_powersetAux {l : List α} ⦃x⦄ (h : x 
in revzip (powersetAux l)) : x.1 + x.2 = ↑l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l
₂ ↔ l₁ ~ l₂
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `Multiset.powersetAux_perm`：powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l
₂) : powersetAux l₁ ~ powersetAux l₂
-/
theorem revzip_powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    revzip (powersetAux l₁) ~ revzip (powersetAux l₂) := by
  have := Classical.decEq α
  simp only [fun l : List α => revzip_powersetAux_lemma l revzip_powersetAux, coe_eq_coe.2 p]
  exact (powersetAux_perm p).map _

@[simp]
/-
**Multiset.powerset_le_powerset_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powerset_le_powerset_iff_le {s t : Multiset α} : s.powerset <= t.powerset 
↔ s <= t where mp powerset
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_powerset`：mem_powerset {s t : Multiset α} : s in powerset t
 ↔ s <= t
· 使用定理 `Multiset.mem_of_le`：mem_of_le (h : s <= t) : a in s -> a in t
· 使用定理 `Multiset.self_mem_powerset`：self_mem_powerset (s : Multiset α) : s in s.
powerset
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powerset_coe'`：powerset_coe' (l : List α) : @powerset α l = ((s
ublists' l).map (↑) : List (Multiset α))
· 使用定理 `Multiset.coe_le`：coe_le {l₁ l₂ : List α} : (l₁ : Multiset α) <= l₂ ↔ l₁ 
<+~ l₂
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
· 使用定理 `List.Sublist.sublists'`：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.sublists'.Sublist l₂.sublists'
-/
theorem powerset_le_powerset_iff_le {s t : Multiset α} :
    s.powerset ≤ t.powerset ↔ s ≤ t where
  mp powerset := Multiset.mem_powerset.mp <| Multiset.mem_of_le powerset (self_mem_powerset s)
  mpr le :=
    leInductionOn le fun hsub => by
      rw [powerset_coe', powerset_coe', coe_le]
      apply Sublist.subperm
      apply Sublist.map
      exact Sublist.sublists' hsub
/-
**Multiset.powerset_injective** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：powerset_injective : Function.Injective (@Multiset.powerset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.powerset_le_powerset_iff_le`：powerset_le_powerset_iff_le {s t :
 Multiset α} : s.powerset <= t.powerset ↔ s <= t where mp powerset
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma powerset_injective : Function.Injective (@Multiset.powerset α) := by
  intro a₁ a₂ a
  exact le_antisymm
    (powerset_le_powerset_iff_le.mp (le_of_eq a))
    (powerset_le_powerset_iff_le.mp (le_of_eq a.symm))
/-
**Multiset.powerset_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：powerset_strictMono : StrictMono (@Multiset.powerset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `strictMono_of_le_iff_le`：strictMono_of_le_iff_le [Preorder α] [Preorder 
β] {f : α -> β} (h : forall x y, x <= y ↔ f x <= f y) : StrictMono f
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Multiset.powerset_le_powerset_iff_le`：powerset_le_powerset_iff_le {s t :
 Multiset α} : s.powerset <= t.powerset ↔ s <= t where mp powerset
-/
lemma powerset_strictMono : StrictMono (@Multiset.powerset α) :=
  strictMono_of_le_iff_le (fun _ _ ↦ powerset_le_powerset_iff_le.symm)
/-
**Multiset.powerset_mono** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：powerset_mono : Monotone (@Multiset.powerset α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用引理 `Multiset.powerset_strictMono`：powerset_strictMono : StrictMono (@Multise
t.powerset α)
-/
lemma powerset_mono : Monotone (@Multiset.powerset α) :=
  powerset_strictMono.monotone

/-! ### powersetCard -/


/-- Helper function for `powersetCard`. Given a list `l`, `powersetCardAux n l` is the list
of sublists of length `n`, as multisets. -/
/-
**Multiset.powersetCardAux** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：powersetCardAux (n : Nat) (l : List α) : List (Multiset α)
参数：n : Nat；l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function for `powersetCard`. Given a list `l`, `powersetCardAux n l` is t
he list
of sublists of length `n`, as multisets.
-/
def powersetCardAux (n : ℕ) (l : List α) : List (Multiset α) :=
  sublistsLenAux n l (↑) []
/-
**Multiset.powersetCardAux_eq_map_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCardAux_eq_map_coe {n} {l : List α} : powersetCardAux n l = (subli
stsLen n l).map (↑)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCardAux.eq_1`：∀ {α : Type u_1} (n : ℕ) (l : List α), Mu
ltiset.powersetCardAux n l = List.sublistsLenAux n l Multiset.ofList []
· 使用定理 `List.sublistsLenAux_eq`：sublistsLenAux_eq (l : List α) (n) (f : List α -
> β) (r) : sublistsLenAux n l f r = (sublistsLen n l).map f ++ r
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
-/
theorem powersetCardAux_eq_map_coe {n} {l : List α} :
    powersetCardAux n l = (sublistsLen n l).map (↑) := by
  rw [powersetCardAux, sublistsLenAux_eq, append_nil]

@[simp]
/-
**Multiset.mem_powersetCardAux** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_powersetCardAux {n} {l : List α} {s} : s in powersetCardAux n l ↔ s <=
 ↑l ∧ card s = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.powersetCardAux_eq_map_coe`：powersetCardAux_eq_map_coe {n} {l :
 List α} : powersetCardAux n l = (sublistsLen n l).map (↑)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
-/
theorem mem_powersetCardAux {n} {l : List α} {s} : s ∈ powersetCardAux n l ↔ s ≤ ↑l ∧ card s = n :=
  Quotient.inductionOn s <| by
    simp only [quot_mk_to_coe, powersetCardAux_eq_map_coe, List.mem_map, mem_sublistsLen,
      coe_eq_coe, coe_le, Subperm, coe_card]
    exact fun l₁ =>
      ⟨fun ⟨l₂, ⟨s, e⟩, p⟩ => ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩,
       fun ⟨⟨l₂, p, s⟩, e⟩ => ⟨_, ⟨s, p.length_eq.trans e⟩, p⟩⟩

@[simp]
/-
**Multiset.powersetCardAux_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCardAux_zero (l : List α) : powersetCardAux 0 l = [0]
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCardAux_eq_map_coe`：powersetCardAux_eq_map_coe {n} {l :
 List α} : powersetCardAux n l = (sublistsLen n l).map (↑)
· 使用定理 `List.sublistsLen_zero`：sublistsLen_zero (l : List α) : sublistsLen 0 l =
 [[]]
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powersetCardAux_zero (l : List α) : powersetCardAux 0 l = [0] := by
  simp [powersetCardAux_eq_map_coe]

@[simp]
/-
**Multiset.powersetCardAux_nil** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCardAux_nil (n : Nat) : powersetCardAux (n + 1) (@nil α) = []
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powersetCardAux_nil (n : ℕ) : powersetCardAux (n + 1) (@nil α) = [] :=
  rfl

@[simp]
/-
**Multiset.powersetCardAux_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCardAux_cons (n : Nat) (a : α) (l : List α) : powersetCardAux (n +
 1) (a :: l) = powersetCardAux (n + 1) l ++ List.map (cons a) (powersetCardAux n
 l)
参数：n : Nat；a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCardAux_eq_map_coe`：powersetCardAux_eq_map_coe {n} {l :
 List α} : powersetCardAux n l = (sublistsLen n l).map (↑)
· 使用定理 `List.sublistsLen_succ_cons`：sublistsLen_succ_cons (n) (a : α) (l) : subl
istsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons 
a)
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.append_cancel_left_eq`：∀ {α : Type u_1} (as bs cs : List α), (as ++
 bs = as ++ cs) = (bs = cs)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem powersetCardAux_cons (n : ℕ) (a : α) (l : List α) :
    powersetCardAux (n + 1) (a :: l) =
      powersetCardAux (n + 1) l ++ List.map (cons a) (powersetCardAux n l) := by
  simp [powersetCardAux_eq_map_coe]
/-
**Multiset.powersetCardAux_perm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCardAux_perm {n} {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetCardAux 
n l₁ ~ powersetCardAux n l₂
参数：p : l₁ ~ l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCardAux_zero`：powersetCardAux_zero (l : List α) : power
setCardAux 0 l = [0]
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `Multiset.powersetCardAux_cons`：powersetCardAux_cons (n : Nat) (a : α) (l
 : List α) : powersetCardAux (n + 1) (a :: l) = powersetCardAux (n + 1) l ++ Lis
t.map (cons a) (pow…
· 使用定理 `List.Perm.append`：∀ {α : Type u_1} {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → 
t₁.Perm t₂ → (l₁ ++ t₁).Perm (l₂ ++ t₂)
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.Perm.append_left`：∀ {α : Type u_1} {t₁ t₂ : List α} (l : List α), t
₁.Perm t₂ → (l ++ t₁).Perm (l ++ t₂)
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.cons_swap`：cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s
 = b ::ₘ a ::ₘ s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.Perm.append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} (t₁ : List α),
 l₁.Perm l₂ → (l₁ ++ t₁).Perm (l₂ ++ t₁)
· 使用定理 `List.perm_append_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, (l₁ ++ l₂).Per
m (l₂ ++ l₁)
-/
theorem powersetCardAux_perm {n} {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    powersetCardAux n l₁ ~ powersetCardAux n l₂ := by
  induction n generalizing l₁ l₂ with | zero => simp | succ n IHn => ?_
  induction p with
  | nil => rfl
  | cons _ p IH =>
    simp only [powersetCardAux_cons]
    exact IH.append ((IHn p).map _)
  | swap a b =>
    simp only [powersetCardAux_cons, append_assoc]
    apply Perm.append_left
    cases n
    · simp [Perm.swap]
    simp only [powersetCardAux_cons, map_append, List.map_map]
    rw [← append_assoc, ← append_assoc,
      (by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂

/-- `powersetCard n s` is the multiset of all submultisets of `s` of length `n`. -/
/-
**Multiset.powersetCard** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：powersetCard (n : Nat) (s : Multiset α) : Multiset (Multiset α)
参数：n : Nat；s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`powersetCard n s` is the multiset of all submultisets of `s` of length `n`.
-/
def powersetCard (n : ℕ) (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => (powersetCardAux n l : Multiset (Multiset α))) fun _ _ h =>
    Quot.sound (powersetCardAux_perm h)
/-
**Multiset.powersetCard_coe'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_coe' (n) (l : List α) : @powersetCard α n l = powersetCardAux
 n l
参数：n；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powersetCard_coe' (n) (l : List α) : @powersetCard α n l = powersetCardAux n l :=
  rfl
/-
**Multiset.powersetCard_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_coe (n) (l : List α) : @powersetCard α n l = ((sublistsLen n 
l).map (↑) : List (Multiset α))
参数：n；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.powersetCardAux_eq_map_coe`：powersetCardAux_eq_map_coe {n} {l :
 List α} : powersetCardAux n l = (sublistsLen n l).map (↑)
-/
theorem powersetCard_coe (n) (l : List α) :
    @powersetCard α n l = ((sublistsLen n l).map (↑) : List (Multiset α)) :=
  congr_arg ((↑) : List (Multiset α) → Multiset (Multiset α)) powersetCardAux_eq_map_coe

@[simp]
/-
**Multiset.powersetCard_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_zero_left (s : Multiset α) : powersetCard 0 s = {0}
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCardAux_zero`：powersetCardAux_zero (l : List α) : power
setCardAux 0 l = [0]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powersetCard_zero_left (s : Multiset α) : powersetCard 0 s = {0} :=
  Quotient.inductionOn s fun l => by simp [powersetCard_coe']
/-
**Multiset.powersetCard_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_zero_right (n : Nat) : @powersetCard α (n + 1) 0 = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem powersetCard_zero_right (n : ℕ) : @powersetCard α (n + 1) 0 = 0 :=
  rfl

@[simp]
/-
**Multiset.powersetCard_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_cons (n : Nat) (a : α) (s) : powersetCard (n + 1) (a ::ₘ s) =
 powersetCard (n + 1) s + map (cons a) (powersetCard n s)
参数：n : Nat；a : α；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCardAux_cons`：powersetCardAux_cons (n : Nat) (a : α) (l
 : List α) : powersetCardAux (n + 1) (a :: l) = powersetCardAux (n + 1) l ++ Lis
t.map (cons a) (pow…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powersetCard_cons (n : ℕ) (a : α) (s) :
    powersetCard (n + 1) (a ::ₘ s) = powersetCard (n + 1) s + map (cons a) (powersetCard n s) :=
  Quotient.inductionOn s fun l => by simp [powersetCard_coe']
/-
**Multiset.powersetCard_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_one (s : Multiset α) : powersetCard 1 s = s.map singleton
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCard_coe`：powersetCard_coe (n) (l : List α) : @powerset
Card α n l = ((sublistsLen n l).map (↑) : List (Multiset α))
· 使用定理 `List.sublistsLen_one`：sublistsLen_one (l : List α) : sublistsLen 1 l = l
.reverse.map ([·])
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Multiset.coe_reverse`：coe_reverse (l : List α) : (reverse l : Multiset α
) = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powersetCard_one (s : Multiset α) : powersetCard 1 s = s.map singleton :=
  Quotient.inductionOn s fun l ↦ by
    simp [powersetCard_coe, sublistsLen_one, map_reverse, Function.comp_def]

@[simp]
/-
**Multiset.mem_powersetCard** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_powersetCard {n : Nat} {s t : Multiset α} : s in powersetCard n t ↔ s 
<= t ∧ card s = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_powersetCard {n : ℕ} {s t : Multiset α} : s ∈ powersetCard n t ↔ s ≤ t ∧ card s = n :=
  Quotient.inductionOn t fun l => by simp [powersetCard_coe']

@[simp]
/-
**Multiset.card_powersetCard** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_powersetCard (n : Nat) (s : Multiset α) : card (powersetCard n s) = N
at.choose (card s) n
参数：n : Nat；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCard_coe`：powersetCard_coe (n) (l : List α) : @powerset
Card α n l = ((sublistsLen n l).map (↑) : List (Multiset α))
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_sublistsLen`：∀ {α : Type u} (n : ℕ) (l : List α), (List.subl
istsLen n l).length = l.length.choose n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem card_powersetCard (n : ℕ) (s : Multiset α) :
    card (powersetCard n s) = Nat.choose (card s) n :=
  Quotient.inductionOn s <| by simp [powersetCard_coe]
/-
**Multiset.powersetCard_le_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_le_powerset (n : Nat) (s : Multiset α) : powersetCard n s <= 
powerset s
参数：n : Nat；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCard_coe`：powersetCard_coe (n) (l : List α) : @powerset
Card α n l = ((sublistsLen n l).map (↑) : List (Multiset α))
· 使用定理 `Multiset.powerset_coe'`：powerset_coe' (l : List α) : @powerset α l = ((s
ublists' l).map (↑) : List (Multiset α))
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
· 使用定理 `List.sublistsLen_sublist_sublists'`：∀ {α : Type u} (n : ℕ) (l : List α),
 (List.sublistsLen n l).Sublist l.sublists'
-/
theorem powersetCard_le_powerset (n : ℕ) (s : Multiset α) : powersetCard n s ≤ powerset s :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, powersetCard_coe, powerset_coe', coe_le]
    exact ((sublistsLen_sublist_sublists' _ _).map _).subperm
/-
**Multiset.powersetCard_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_mono (n : Nat) {s t : Multiset α} (h : s <= t) : powersetCard
 n s <= powersetCard n t
参数：n : Nat；h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCard_coe`：powersetCard_coe (n) (l : List α) : @powerset
Card α n l = ((sublistsLen n l).map (↑) : List (Multiset α))
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
· 使用定理 `List.sublistsLen_sublist_of_sublist`：sublistsLen_sublist_of_sublist (n) 
{l₁ l₂ : List α} (h : l₁ <+ l₂) : sublistsLen n l₁ <+ sublistsLen n l₂
-/
theorem powersetCard_mono (n : ℕ) {s t : Multiset α} (h : s ≤ t) :
    powersetCard n s ≤ powersetCard n t :=
  leInductionOn h fun {l₁ l₂} h => by
    simp only [powersetCard_coe, coe_le]
    exact ((sublistsLen_sublist_of_sublist _ h).map _).subperm

@[simp]
/-
**Multiset.powersetCard_eq_empty** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_eq_empty {α : Type*} (n : Nat) {s : Multiset α} (h : card s <
 n) : powersetCard n s = 0
参数：n : Nat；h : card s < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.card_eq_zero`：card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 
0
· 使用定理 `Multiset.card_powersetCard`：card_powersetCard (n : Nat) (s : Multiset α)
 : card (powersetCard n s) = Nat.choose (card s) n
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
-/
theorem powersetCard_eq_empty {α : Type*} (n : ℕ) {s : Multiset α} (h : card s < n) :
    powersetCard n s = 0 :=
  card_eq_zero.mp (Nat.choose_eq_zero_of_lt h ▸ card_powersetCard _ _)
/-
**Multiset.powersetCard_card_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_card_add (s : Multiset α) {i : Nat} (hi : 0 < i) : s.powerset
Card (card s + i) = 0
参数：s : Multiset α；hi : 0 < i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCard_eq_empty`：powersetCard_eq_empty {α : Type*} (n : N
at) {s : Multiset α} (h : card s < n) : powersetCard n s = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem powersetCard_card_add (s : Multiset α) {i : ℕ} (hi : 0 < i) :
    s.powersetCard (card s + i) = 0 := by
  simp [hi]

@[simp]
/-
**Multiset.powersetCard_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_self (s : Multiset α) : powersetCard s.card s = {s}
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCard_zero_left`：powersetCard_zero_left (s : Multiset α)
 : powersetCard 0 s = {0}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.card_cons`：card_cons (a : α) (s : Multiset α) : card (a ::ₘ s) 
= card s + 1
· 使用定理 `Multiset.powersetCard_cons`：powersetCard_cons (n : Nat) (a : α) (s) : po
wersetCard (n + 1) (a ::ₘ s) = powersetCard (n + 1) s + map (cons a) (powersetCa
rd n s)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.powersetCard_eq_empty`：powersetCard_eq_empty {α : Type*} (n : N
at) {s : Multiset α} (h : card s < n) : powersetCard n s = 0
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
-/
theorem powersetCard_self (s : Multiset α) : powersetCard s.card s = {s} := by
  induction s using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

set_option backward.isDefEq.respectTransparency false in
/-
**Multiset.powersetCard_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：powersetCard_map {β : Type*} (f : α -> β) (n : Nat) (s : Multiset α) : pow
ersetCard n (s.map f) = (powersetCard n s).map (map f)
参数：f : α -> β；n : Nat；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powersetCard_zero_left`：powersetCard_zero_left (s : Multiset α)
 : powersetCard 0 s = {0}
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.powersetCard_eq_empty`：powersetCard_eq_empty {α : Type*} (n : N
at) {s : Multiset α} (h : card s < n) : powersetCard n s = 0
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.powersetCard_cons`：powersetCard_cons (n : Nat) (a : α) (s) : po
wersetCard (n + 1) (a ::ₘ s) = powersetCard (n + 1) s + map (cons a) (powersetCa
rd n s)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
-/
theorem powersetCard_map {β : Type*} (f : α → β) (n : ℕ) (s : Multiset α) :
    powersetCard n (s.map f) = (powersetCard n s).map (map f) := by
  induction s using Multiset.induction generalizing n with
  | empty => cases n <;> simp [powersetCard_zero_left]
  | cons t s ih => cases n <;> simp [ih]
/-
**Multiset.pairwise_disjoint_powersetCard** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pairwise_disjoint_powersetCard (s : Multiset α) : _root_.Pairwise fun i j 
=> Disjoint (s.powersetCard i) (s.powersetCard j)
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.disjoint_left`：disjoint_left {s t : Multiset α} : Disjoint s t 
↔ forall {a}, a in s -> a ∉ t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_powersetCard`：mem_powersetCard {n : Nat} {s t : Multiset α}
 : s in powersetCard n t ↔ s <= t ∧ card s = n
-/
theorem pairwise_disjoint_powersetCard (s : Multiset α) :
    _root_.Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j) :=
  fun _ _ h ↦ disjoint_left.mpr fun hi hj ↦
    h ((Multiset.mem_powersetCard.mp hi).2.symm.trans (Multiset.mem_powersetCard.mp hj).2)
/-
**Multiset.bind_powerset_len** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_powerset_len {α : Type*} (S : Multiset α) : (bind (Multiset.range (ca
rd S + 1)) fun k => S.powersetCard k) = S.powerset
参数：S : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powerset_coe'`：powerset_coe' (l : List α) : @powerset α l = ((s
ublists' l).map (↑) : List (Multiset α))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Multiset.powersetCard_coe`：powersetCard_coe (n) (l : List α) : @powerset
Card α n l = ((sublistsLen n l).map (↑) : List (Multiset α))
· 使用定理 `Multiset.coe_bind`：coe_bind (l : List α) (f : α -> List β) : (@bind α β 
l fun a => f a) = l.flatMap f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l
₂ ↔ l₁ ~ l₂
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `List.range_bind_sublistsLen_perm`：range_bind_sublistsLen_perm (l : List 
α) : ((List.range (l.length + 1)).flatMap fun n => sublistsLen n l) ~ sublists' 
l
-/
theorem bind_powerset_len {α : Type*} (S : Multiset α) :
    (bind (Multiset.range (card S + 1)) fun k => S.powersetCard k) = S.powerset := by
  induction S using Quotient.inductionOn
  simp_rw [quot_mk_to_coe, powerset_coe', powersetCard_coe, ← coe_range, coe_bind,
    ← List.map_flatMap, coe_card]
  exact coe_eq_coe.mpr ((List.range_bind_sublistsLen_perm _).map _)

@[simp]
/-
**Multiset.nodup_powerset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_powerset {s : Multiset α} : Nodup (powerset s) ↔ Nodup s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.of_map`：∀ {α : Type u_1} {β : Type v} {s : Multiset α} (f
 : α → β), (Multiset.map f s).Nodup → s.Nodup
· 使用定理 `Multiset.nodup_of_le`：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodu
p t -> Nodup s
· 使用定理 `Multiset.map_single_le_powerset`：map_single_le_powerset (s : Multiset α)
 : s.map singleton <= powerset s
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.powerset_coe'`：powerset_coe' (l : List α) : @powerset α l = ((s
ublists' l).map (↑) : List (Multiset α))
· 使用定理 `List.Nodup.map_on`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β},
   (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (List.map f l).Nodup
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Nodup.perm_iff_eq_of_sublist`：∀ {α : Type u_1} {l₁ l₂ l : List α}, 
l.Nodup → l₁.Sublist l → l₂.Sublist l → (l₁.Perm l₂ ↔ l₁ = l₂)
· 使用定理 `List.mem_sublists'`：mem_sublists' {s t : List α} : s in sublists' t ↔ s 
<+ t
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_sublists'`：nodup_sublists' {l : List α} : Nodup (sublists' l)
 ↔ Nodup l
-/
theorem nodup_powerset {s : Multiset α} : Nodup (powerset s) ↔ Nodup s :=
  ⟨fun h => (nodup_of_le (map_single_le_powerset _) h).of_map _,
    Quotient.inductionOn s fun l h => by
      simp only [quot_mk_to_coe, powerset_coe', coe_nodup]
      refine (nodup_sublists'.2 h).map_on ?_
      exact fun x sx y sy e =>
        (h.perm_iff_eq_of_sublist (mem_sublists'.1 sx) (mem_sublists'.1 sy)).1 (Quotient.exact e)⟩

alias ⟨Nodup.ofPowerset, Nodup.powerset⟩ := nodup_powerset
/-
**Multiset.Nodup.powersetCard** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {n : ℕ} {s : Multiset α}, s.Nodup → (Multiset.powersetCar
d n s).Nodup
参数：Multiset.powersetCard n s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.nodup_of_le`：nodup_of_le {s t : Multiset α} (h : s <= t) : Nodu
p t -> Nodup s
· 使用定理 `Multiset.powersetCard_le_powerset`：powersetCard_le_powerset (n : Nat) (s
 : Multiset α) : powersetCard n s <= powerset s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.nodup_powerset`：nodup_powerset {s : Multiset α} : Nodup (powers
et s) ↔ Nodup s
-/
protected theorem Nodup.powersetCard {n : ℕ} {s : Multiset α} (h : Nodup s) :
    Nodup (powersetCard n s) :=
  nodup_of_le (powersetCard_le_powerset _ _) (nodup_powerset.2 h)

end Multiset

