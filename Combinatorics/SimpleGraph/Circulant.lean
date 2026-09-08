/-
Copyright (c) 2024 Iván Renison, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# Definition of circulant graphs

This file defines and proves several fact about circulant graphs.
A circulant graph over type `G` with jumps `s : Set G` is a graph in which two vertices `u` and `v`
are adjacent if and only if `u - v ∈ s` or `v - u ∈ s`. The elements of `s` are called jumps.

## Main declarations

* `SimpleGraph.circulantGraph s`: the circulant graph over `G` with jumps `s`.
-/

@[expose] public section

namespace SimpleGraph

/-- Circulant graph over additive group `G` with jumps `s` -/
@[simps!]
/-
**SimpleGraph.circulantGraph** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：circulantGraph {G : Type*} [AddGroup G] (s : Set G) : SimpleGraph G
参数：s : Set G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Circulant graph over additive group `G` with jumps `s`
-/
def circulantGraph {G : Type*} [AddGroup G] (s : Set G) : SimpleGraph G :=
  fromRel (· - · ∈ s)

variable {G : Type*} [AddGroup G] (s : Set G)
/-
**SimpleGraph.circulantGraph_eq_erase_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：circulantGraph_eq_erase_zero : circulantGraph s = circulantGraph (s \ {0})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem circulantGraph_eq_erase_zero : circulantGraph s = circulantGraph (s \ {0}) := by
  ext (u v : G)
  simp only [circulantGraph, fromRel_adj, and_congr_right_iff]
  intro (h : u ≠ v)
  apply Iff.intro
  · intro h1
    cases h1 with
      | inl h1 => exact Or.inl ⟨h1, sub_ne_zero_of_ne h⟩
      | inr h1 => exact Or.inr ⟨h1, sub_ne_zero_of_ne h.symm⟩
  · intro h1
    cases h1 with
      | inl h1 => exact Or.inl h1.left
      | inr h1 => exact Or.inr h1.left
/-
**SimpleGraph.circulantGraph_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：circulantGraph_eq_symm : circulantGraph s = circulantGraph (s union (-s))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.circulantGraph_adj`：∀ {G : Type u_1} [inst : AddGroup G] (s 
: Set G) (a b : G),   (SimpleGraph.circulantGraph s).Adj a b = (¬a = b ∧ (a - b 
∈ s ∨ b - a ∈ s))
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem circulantGraph_eq_symm : circulantGraph s = circulantGraph (s ∪ (-s)) := by
  ext
  simp only [circulantGraph_adj, Set.mem_union, Set.mem_neg, neg_sub]
  grind
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq G] [DecidablePred (· ∈ s)] : DecidableRel (circulantGraph s).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))
/-
**SimpleGraph.circulantGraph_adj_translate** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：circulantGraph_adj_translate {s : Set G} {u v d : G} : (circulantGraph s).
Adj (u + d) (v + d) ↔ (circulantGraph s).Adj u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.circulantGraph_adj`：∀ {G : Type u_1} [inst : AddGroup G] (s 
: Set G) (a b : G),   (SimpleGraph.circulantGraph s).Adj a b = (¬a = b ∧ (a - b 
∈ s ∨ b - a ∈ s))
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem circulantGraph_adj_translate {s : Set G} {u v d : G} :
    (circulantGraph s).Adj (u + d) (v + d) ↔ (circulantGraph s).Adj u v := by simp
/-
**SimpleGraph.cycleGraph_eq_circulantGraph** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h`。
形式化陈述：cycleGraph_eq_circulantGraph (n : Nat) : cycleGraph (n + 1) = circulantGra
ph {1}
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.edgeFinset_inj`：edgeFinset_inj : G₁.edgeFinset = G₂.edgeFins
et ↔ G₁ = G₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.ext`：∀ {V : Type u} {x y : SimpleGraph V}, x.Adj = y.Adj → x
 = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.circulantGraph_adj`：∀ {G : Type u_1} [inst : AddGroup G] (s 
: Set G) (a b : G),   (SimpleGraph.circulantGraph s).Adj a b = (¬a = b ∧ (a - b 
∈ s ∨ b - a ∈ s))
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
-/
theorem cycleGraph_eq_circulantGraph (n : ℕ) : cycleGraph (n + 1) = circulantGraph {1} := by
  cases n
  · exact edgeFinset_inj.mp rfl
  · aesop

end SimpleGraph

