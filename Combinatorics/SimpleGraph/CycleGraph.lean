/-
Copyright (c) 2024 Iván Renison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# Definition of cycle graphs

This file defines and proves several fact about cycle graphs on `n` vertices and the cycle around
the cycle graph when `n ≥ 3`.

## Main declarations

* `SimpleGraph.cycleGraph n`: the cycle graph over `Fin n`.
* `(SimpleGraph.cycleGraph n).cycle`: the cycle around `cycleGraph (n + 3)` starting at 0.
-/

@[expose] public section

namespace SimpleGraph

open Walk

/-- Cycle graph over `Fin n` -/
/-
**SimpleGraph.cycleGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph : (n : Nat) -> SimpleGraph (Fin n) | 0 | 1 => ⊥ | _ + 2 => { Ad
j a b
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cycle graph over `Fin n`
-/
def cycleGraph : (n : ℕ) → SimpleGraph (Fin n)
  | 0 | 1 => ⊥
  | _ + 2 => {
    Adj a b := a - b = 1 ∨ b - a = 1
  }
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (n : ℕ) → DecidableRel (cycleGraph n).Adj
  | 0 | 1 => fun _ _ => inferInstanceAs (Decidable False)
  | _ + 2 => by unfold cycleGraph; infer_instance
/-
**SimpleGraph.cycleGraph_zero_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_zero_adj {u v : Fin 0} : ¬(cycleGraph 0).Adj u v
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cycleGraph_zero_adj {u v : Fin 0} : ¬(cycleGraph 0).Adj u v := id
/-
**SimpleGraph.cycleGraph_zero_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_zero_eq_bot : cycleGraph 0 = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Fin.subsingleton_zero`：Subsingleton (Fin 0)
-/
theorem cycleGraph_zero_eq_bot : cycleGraph 0 = ⊥ := Subsingleton.elim _ _
/-
**SimpleGraph.cycleGraph_one_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_one_eq_bot : cycleGraph 1 = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
-/
theorem cycleGraph_one_eq_bot : cycleGraph 1 = ⊥ := Subsingleton.elim _ _
/-
**SimpleGraph.cycleGraph_zero_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_zero_eq_top : cycleGraph 0 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Fin.subsingleton_zero`：Subsingleton (Fin 0)
-/
theorem cycleGraph_zero_eq_top : cycleGraph 0 = ⊤ := Subsingleton.elim _ _
/-
**SimpleGraph.cycleGraph_one_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_one_eq_top : cycleGraph 1 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
-/
theorem cycleGraph_one_eq_top : cycleGraph 1 = ⊤ := Subsingleton.elim _ _
/-
**SimpleGraph.cycleGraph_two_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_two_eq_top : cycleGraph 2 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem cycleGraph_two_eq_top : cycleGraph 2 = ⊤ := by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide
/-
**SimpleGraph.cycleGraph_three_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_three_eq_top : cycleGraph 3 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem cycleGraph_three_eq_top : cycleGraph 3 = ⊤ := by
  simp only [SimpleGraph.ext_iff, funext_iff]
  decide
/-
**SimpleGraph.cycleGraph_one_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_one_adj {u v : Fin 1} : ¬(cycleGraph 1).Adj u v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.cycleGraph_one_eq_bot`：cycleGraph_one_eq_bot : cycleGraph 1 
= ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem cycleGraph_one_adj {u v : Fin 1} : ¬(cycleGraph 1).Adj u v := by
  simp [cycleGraph_one_eq_bot]
/-
**SimpleGraph.cycleGraph_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_adj {n : Nat} {u v : Fin (n + 2)} : (cycleGraph (n + 2)).Adj u 
v ↔ u - v = 1 ∨ v - u = 1
参数：n + 2。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cycleGraph_adj {n : ℕ} {u v : Fin (n + 2)} :
    (cycleGraph (n + 2)).Adj u v ↔ u - v = 1 ∨ v - u = 1 := Iff.rfl
/-
**SimpleGraph.cycleGraph_adj'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_adj' {n : Nat} {u v : Fin n} : (cycleGraph n).Adj u v ↔ (u - v)
.val = 1 ∨ (v - u).val = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
-/
theorem cycleGraph_adj' {n : ℕ} {u v : Fin n} :
    (cycleGraph n).Adj u v ↔ (u - v).val = 1 ∨ (v - u).val = 1 := by
  match n with
  | 0 => exact u.elim0
  | 1 => simp [cycleGraph_one_adj]
  | n + 2 => simp [cycleGraph_adj, Fin.ext_iff]
/-
**SimpleGraph.cycleGraph_neighborSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_neighborSet {n : Nat} {v : Fin (n + 2)} : (cycleGraph (n + 2)).
neighborSet v = {v - 1, v + 1}
参数：n + 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.cycleGraph_adj`：cycleGraph_adj {n : Nat} {u v : Fin (n + 2)}
 : (cycleGraph (n + 2)).Adj u v ↔ u - v = 1 ∨ v - u = 1
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cycleGraph_neighborSet {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).neighborSet v = {v - 1, v + 1} := by
  ext w
  simp only [mem_neighborSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [cycleGraph_adj, sub_eq_iff_eq_add', sub_eq_iff_eq_add', eq_sub_iff_add_eq, eq_comm]
/-
**SimpleGraph.cycleGraph_neighborFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_neighborFinset {n : Nat} {v : Fin (n + 2)} : (cycleGraph (n + 2
)).neighborFinset v = {v - 1, v + 1}
参数：n + 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `SimpleGraph.cycleGraph_neighborSet`：cycleGraph_neighborSet {n : Nat} {v 
: Fin (n + 2)} : (cycleGraph (n + 2)).neighborSet v = {v - 1, v + 1}
· 使用定理 `Set.toFinset_insert`：toFinset_insert [DecidableEq α] {a : α} {s : Set α}
 [Fintype (insert a s : Set α)] [Fintype s] : (insert a s).toFinset = insert a s
.toFinset
· 使用定理 `Set.toFinset_singleton`：toFinset_singleton (a : α) [Fintype ({a} : Set α
)] : ({a} : Set α).toFinset = {a}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleGraph_neighborFinset {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).neighborFinset v = {v - 1, v + 1} := by
  simp [neighborFinset, cycleGraph_neighborSet]
/-
**SimpleGraph.cycleGraph_degree_two_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_degree_two_le {n : Nat} {v : Fin (n + 2)} : (cycleGraph (n + 2)
).degree v = Finset.card {v - 1, v + 1}
参数：n + 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.degree.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (v : V) [i
nst : Fintype ↑(G.neighborSet v)], G.degree v = (G.neighborFinset v).card
· 使用定理 `SimpleGraph.cycleGraph_neighborFinset`：cycleGraph_neighborFinset {n : Na
t} {v : Fin (n + 2)} : (cycleGraph (n + 2)).neighborFinset v = {v - 1, v + 1}
-/
theorem cycleGraph_degree_two_le {n : ℕ} {v : Fin (n + 2)} :
    (cycleGraph (n + 2)).degree v = Finset.card {v - 1, v + 1} := by
  rw [SimpleGraph.degree, cycleGraph_neighborFinset]
/-
**SimpleGraph.cycleGraph_degree_three_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`
。
形式化陈述：cycleGraph_degree_three_le {n : Nat} {v : Fin (n + 3)} : (cycleGraph (n + 
3)).degree v = 2
参数：n + 3。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.cycleGraph_degree_two_le`：cycleGraph_degree_two_le {n : Nat}
 {v : Fin (n + 2)} : (cycleGraph (n + 2)).degree v = Finset.card {v - 1, v + 1}
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `ne_of_beq_false`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] {a b : α}, 
(a == b) = false → a ≠ b
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `Std.LawfulBEqOrd.equivBEq`：∀ {α : Type u} [inst : BEq α] [inst_1 : Ord α
] [Std.LawfulBEqOrd α] [Std.TransOrd α], EquivBEq α
· 使用定理 `Std.LawfulBCmp.toLawfulBEqCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : 
LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   S
td.LawfulBEqCmp cmp
· 使用定理 `instLawfulBCmpCompare_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], 
Std.LawfulBCmp compare
· 使用定理 `Fin.instTransOrd`：∀ (n : ℕ), Std.TransOrd (Fin n)
-/
theorem cycleGraph_degree_three_le {n : ℕ} {v : Fin (n + 3)} :
    (cycleGraph (n + 3)).degree v = 2 := by
  rw [cycleGraph_degree_two_le, Finset.card_pair]
  simp only [ne_eq, sub_eq_iff_eq_add, add_assoc v, left_eq_add]
  exact ne_of_beq_false rfl
/-
**SimpleGraph.pathGraph_le_cycleGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：pathGraph_le_cycleGraph {n : Nat} : pathGraph n <= cycleGraph n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Fin.subsingleton_zero`：Subsingleton (Fin 0)
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.cycleGraph_adj'`：cycleGraph_adj' {n : Nat} {u v : Fin n} : (
cycleGraph n).Adj u v ↔ (u - v).val = 1 ∨ (v - u).val = 1
· 使用定理 `SimpleGraph.pathGraph_adj`：pathGraph_adj {n : Nat} {u v : Fin n} : (path
Graph n).Adj u v ↔ u.val + 1 = v.val ∨ v.val + 1 = u.val
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.eq_sub_of_add_eq'`：∀ {a b c : ℕ}, b + c = a → c = a - b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.coe_sub_iff_le`：∀ {n : ℕ} {a b : Fin n}, ↑(a - b) = ↑a - ↑b ↔ b ≤ a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n < m
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem pathGraph_le_cycleGraph {n : ℕ} : pathGraph n ≤ cycleGraph n := by
  match n with
  | 0 | 1 => simp
  | n + 2 =>
    intro u v h
    rw [pathGraph_adj] at h
    rw [cycleGraph_adj']
    cases h with
    | inl h | inr h =>
      simp [Fin.coe_sub_iff_le.mpr (Nat.lt_of_succ_le h.le).le, Nat.eq_sub_of_add_eq' h]
/-
**SimpleGraph.cycleGraph_preconnected** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_preconnected {n : Nat} : (cycleGraph n).Preconnected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Preconnected.mono`：∀ {V : Type u} {G G' : SimpleGraph V}, G 
≤ G' → G.Preconnected → G'.Preconnected
· 使用定理 `SimpleGraph.pathGraph_le_cycleGraph`：pathGraph_le_cycleGraph {n : Nat} :
 pathGraph n <= cycleGraph n
· 使用定理 `SimpleGraph.pathGraph_preconnected`：pathGraph_preconnected (n : Nat) : (
pathGraph n).Preconnected
-/
theorem cycleGraph_preconnected {n : ℕ} : (cycleGraph n).Preconnected :=
  (pathGraph_preconnected n).mono pathGraph_le_cycleGraph
/-
**SimpleGraph.cycleGraph_connected** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：cycleGraph_connected {n : Nat} : (cycleGraph (n + 1)).Connected
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.mono`：∀ {V : Type u} {G G' : SimpleGraph V}, G ≤ G
' → G.Connected → G'.Connected
· 使用定理 `SimpleGraph.pathGraph_le_cycleGraph`：pathGraph_le_cycleGraph {n : Nat} :
 pathGraph n <= cycleGraph n
· 使用定理 `SimpleGraph.pathGraph_connected`：pathGraph_connected (n : Nat) : (pathGr
aph (n + 1)).Connected
-/
theorem cycleGraph_connected {n : ℕ} : (cycleGraph (n + 1)).Connected :=
  (pathGraph_connected n).mono pathGraph_le_cycleGraph

section cycle

set_option backward.privateInPublic true in
/-
**SimpleGraph.cycleGraph.cycleCons** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def cycleGraph.cycleCons (n : ℕ) : ∀ m : Fin (n + 3), (cycleGraph (n + 3)).Walk m 0
  | ⟨0, h⟩ => Walk.nil
  | ⟨m + 1, h⟩ =>
    have hadj : (cycleGraph (n + 3)).Adj ⟨m + 1, h⟩ ⟨m, Nat.lt_of_succ_lt h⟩ := by
      simp [cycleGraph_adj, Fin.ext_iff, Fin.sub_val_of_le]
    Walk.cons hadj (cycleGraph.cycleCons n ⟨m, Nat.lt_of_succ_lt h⟩)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The Eulerian cycle of `cycleGraph (n + 3)` -/
/-
**SimpleGraph.cycleGraph.cycle** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.cycleGraph
`。
形式化陈述：(n : ℕ) → (SimpleGraph.cycleGraph (n + 3)).Walk 0 0
参数：n + 3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Eulerian cycle of `cycleGraph (n + 3)`
-/
def cycleGraph.cycle (n : ℕ) : (cycleGraph (n + 3)).Walk 0 0 :=
  have hadj : (cycleGraph (n + 3)).Adj 0 (Fin.last (n + 2)) := by
    simp [cycleGraph_adj]
  Walk.cons hadj (cycleGraph.cycleCons n (Fin.last (n + 2)))

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit := cycleGraph.cycle
/-
**SimpleGraph.cycleGraph.length_cycle_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem cycleGraph.length_cycle_cons (n : ℕ) :
    ∀ m : Fin (n + 3), (cycleGraph.cycleCons n m).length = m.val
  | ⟨0, h⟩ => by
    unfold cycleGraph.cycleCons
    rfl
  | ⟨m + 1, h⟩ => by
    unfold cycleGraph.cycleCons
    simp only [Walk.length_cons]
    rw [cycleGraph.length_cycle_cons n]

variable {n : ℕ}

@[simp, grind =]
/-
**SimpleGraph.cycleGraph.length_cycle** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.cyc
leGraph`。
形式化陈述：∀ {n : ℕ}, (SimpleGraph.cycleGraph.cycle n).length = n + 3
参数：SimpleGraph.cycleGraph.cycle n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.CycleGraph.0.SimpleGraph.cycl
eGraph.length_cycle_cons`：∀ (n : ℕ) (m : Fin (n + 3)), (SimpleGraph.cycleGraph.c
ycleCons✝ n m).length = ↑m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cycleGraph.length_cycle : (cycleGraph.cycle n).length = n + 3 := by
  unfold cycleGraph.cycle
  simp [cycleGraph.length_cycle_cons]

@[deprecated (since := "2026-02-15")]
alias cycleGraph_EulerianCircuit_length := cycleGraph.length_cycle
/-
**SimpleGraph.cycleGraph.getVert_cycleCons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem cycleGraph.getVert_cycleCons (m : Fin (n + 3)) (i : ℕ) (hi : i ≤ m.val) :
    (cycleGraph.cycleCons n m).getVert i = (m - i) % (n + 3) := by
  obtain ⟨m, hm⟩ := m
  induction i generalizing m
  · simp [Nat.mod_eq_of_lt hm]
  · cases m <;> grind +locals [getVert_cons_succ]
/-
**SimpleGraph.cycleGraph.getVert_cycle** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.cy
cleGraph`。
形式化陈述：∀ {n m : ℕ}, m ≤ n + 3 → (SimpleGraph.cycleGraph.cycle n).getVert m = ⟨(n 
+ 3 - m) % (n + 3), ⋯⟩
参数：SimpleGraph.cycleGraph.cycle n；n + 3 - m；n + 3。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.mod_lt`：∀ (x : ℕ) {y : ℕ}, 0 < y → x % y < y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Nat.mod_self`：∀ (n : ℕ), n % n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cycleGraph.getVert_cycle {m : ℕ} (hm : m ≤ n + 3) :
    (cycleGraph.cycle n).getVert m = ⟨(n + 3 - m) % (n + 3), Nat.mod_lt _ (by lia)⟩ := by
  cases m
  · simp
  · grind +locals [getVert_cons_succ, cycleGraph.getVert_cycleCons]
/-
**SimpleGraph.cycleGraph.isPath_tail_cycle** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.cycleGraph`。
形式化陈述：∀ {n : ℕ}, (SimpleGraph.cycleGraph.cycle n).tail.IsPath
参数：SimpleGraph.cycleGraph.cycle n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.Walk.isPath_iff_injective_get_support`：isPath_iff_injective_
get_support {u v : V} (p : G.Walk u v) : p.IsPath ↔ (p.support.get ·).Injective
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.support_tail_of_not_nil`：support_tail_of_not_nil (p : G
.Walk u v) (hp : ¬ p.Nil) : p.tail.support = p.support.tail
· 使用定理 `of_decide_eq_false`：∀ {p : Prop} [inst : Decidable p], decide p = false 
→ ¬p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用引理 `SimpleGraph.Walk.support_getElem_eq_getVert`：support_getElem_eq_getVert 
{u v : V} {n : Nat} (p : G.Walk u v) (h) : p.support[n]'h = p.getVert n
· 使用定理 `SimpleGraph.Walk.getVert_tail`：∀ {V : Type u} {G : SimpleGraph V} {u v :
 V} {n : ℕ} (p : G.Walk u v), p.tail.getVert n = p.getVert (n + 1)
-/
theorem cycleGraph.isPath_tail_cycle : (cycleGraph.cycle n).tail.IsPath := by
  refine isPath_iff_injective_get_support _ |>.mpr fun ⟨i, hi⟩ ⟨j, hj⟩ hij ↦ ?_
  rw [support_tail_of_not_nil _ (of_decide_eq_false rfl)] at hi hj
  simp only [List.get_eq_getElem, support_getElem_eq_getVert, getVert_tail] at hij
  grind [← Nat.mod_eq_of_lt, cycleGraph.getVert_cycle]
/-
**SimpleGraph.cycleGraph.isCycle_cycle** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.cy
cleGraph`。
形式化陈述：∀ {n : ℕ}, (SimpleGraph.cycleGraph.cycle n).IsCycle
参数：SimpleGraph.cycleGraph.cycle n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length`：isCycle_iff_isPa
th_tail_and_le_length {p : G.Walk u u} : p.IsCycle ↔ p.tail.IsPath ∧ 3 <= p.leng
th
· 使用定理 `SimpleGraph.cycleGraph.isPath_tail_cycle`：∀ {n : ℕ}, (SimpleGraph.cycleG
raph.cycle n).tail.IsPath
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.cycleGraph.length_cycle`：∀ {n : ℕ}, (SimpleGraph.cycleGraph.
cycle n).length = n + 3
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem cycleGraph.isCycle_cycle : (cycleGraph.cycle n).IsCycle :=
  isCycle_iff_isPath_tail_and_le_length.mpr ⟨cycleGraph.isPath_tail_cycle, by simp⟩

end cycle

section IsContained

variable {V : Type*} {G : SimpleGraph V}

/-
**SimpleGraph.cycleGraph_isContained_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`
。
形式化陈述：cycleGraph_isContained_iff {n : Nat} (hn : 2 < n) : cycleGraph n ⊑ G ↔ exi
sts (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n
参数：hn : 2 < n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.isCycle_map_iff_of_injective`：isCycle_map_iff_of_inject
ive {p : G.Walk u u} (hinj : Function.Injective f) : (p.map f).IsCycle ↔ p.IsCyc
le
· 使用引理 `SimpleGraph.Copy.injective`：injective (f : Copy A B) : Injective f.toHom
· 使用定理 `SimpleGraph.cycleGraph.isCycle_cycle`：∀ {n : ℕ}, (SimpleGraph.cycleGraph
.cycle n).IsCycle
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `SimpleGraph.Walk.length_map`：length_map : (p.map f).length = p.length
· 使用定理 `SimpleGraph.cycleGraph.length_cycle`：∀ {n : ℕ}, (SimpleGraph.cycleGraph.
cycle n).length = n + 3
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.cycleGraph_adj'`：cycleGraph_adj' {n : Nat} {u v : Fin n} : (
cycleGraph n).Adj u v ↔ (u - v).val = 1 ∨ (v - u).val = 1
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `List.IsChain.getElem`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, 
List.IsChain R l → ∀ (i : ℕ) (hi : i + 1 < l.length), R l[i] l[i + 1]
· 使用定理 `SimpleGraph.Walk.isChain_adj_support`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} (p : G.Walk u v), List.IsChain G.Adj p.support
· 使用定理 `Fin.coe_sub_iff_lt`：∀ {n : ℕ} {a b : Fin n}, ↑(a - b) = n + ↑a - ↑b ↔ a 
< b
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `SimpleGraph.Walk.support_getElem_length`：support_getElem_length (p : G.W
alk u v) : p.support[p.length] = v
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `SimpleGraph.Walk.support_getElem_one`：support_getElem_one {p : G.Walk u 
v} (hp) : p.support[1]'hp = p.snd
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
（共 41 条，此处仅展示前 30 条）
-/
lemma cycleGraph_isContained_iff {n : ℕ} (hn : 2 < n) :
    cycleGraph n ⊑ G ↔ ∃ (v : V) (p : G.Walk v v), p.IsCycle ∧ p.length = n := by
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h' ↦ ?_⟩
  · have : n = n - 3 + 3 := by lia
    rw [this] at h
    refine ⟨h.toHom ⟨0, by lia⟩, Walk.map h.toHom <| cycleGraph.cycle (n - 3), ?_, ?_⟩
    · exact (isCycle_map_iff_of_injective h.injective).mpr cycleGraph.isCycle_cycle
    · simp [cycleGraph.length_cycle, ← this]
  · obtain ⟨a, p, hp₁, hp₂⟩ := h'
    refine ⟨⟨⟨fun n ↦ p.support[n.succ]'(?_), ?_⟩, ?_⟩⟩
    · grind [hp₁.three_le_length, length_tail_add_one, not_nil_iff_lt_length]
    · intro ⟨x, hx⟩ ⟨y, hy⟩ hab
      have hne : x ≠ y := fun _ ↦ by simp_all
      wlog hle : x > y
      · exact this hn a p hp₁ hp₂ y hy x hx hab.symm hne.symm (by lia) |>.symm
      rcases cycleGraph_adj'.mp hab with hab | hab
      · simp_rw [show x = y + 1 by grind [Fin.sub_val_of_le]]
        exact p.isChain_adj_support.getElem _ _ |>.symm
      · rw [Fin.coe_sub_iff_lt.mpr hle] at hab
        simp_rw [show x = n - 1 by lia, show y = 0 by lia, Fin.succ_mk, show n - 1 + 1 = n by lia]
        simp [← hp₂, p.adj_snd hp₁.not_nil]
    · have hlen : p.tail.support.length = n := by
        grind [length_tail_add_one, not_nil_iff_lt_length]
      have (m : Fin n) : p.support[m.succ]'(by grind) = p.tail.support[m] := by
        simp [p.support_tail_of_not_nil hp₁.not_nil]
      simp_rw [this]
      have := IsPath.mk' <| (support_tail_of_not_nil _ hp₁.not_nil) ▸ hp₁.support_nodup
      exact hlen ▸ (isPath_iff_injective_get_support _ |>.mp this)

end IsContained

end SimpleGraph

