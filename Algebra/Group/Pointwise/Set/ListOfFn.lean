/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.List.OfFn
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-!
# Pointwise operations with lists of sets

This file proves some lemmas about pointwise algebraic operations with lists of sets.
-/

public section

namespace Set

variable {α : Type*} [Monoid α] {s : Set α} {n : ℕ}

open scoped Pointwise

@[to_additive]
/-
**Set.mem_prod_list_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_prod_list_ofFn {a : α} {s : Fin n -> Set α} : a in (List.ofFn s).prod 
↔ exists f : forall i : Fin n, s i, (List.ofFn fun i => (f i : α)).prod = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.ofFn_zero`：∀ {α : Type u_1} {f : Fin 0 → α}, List.ofFn f = []
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem mem_prod_list_ofFn {a : α} {s : Fin n → Set α} :
    a ∈ (List.ofFn s).prod ↔ ∃ f : ∀ i : Fin n, s i, (List.ofFn fun i ↦ (f i : α)).prod = a := by
  induction n generalizing a with
  | zero => simp_rw [List.ofFn_zero, List.prod_nil, Fin.exists_fin_zero_pi, eq_comm, Set.mem_one]
  | succ n ih =>
    simp_rw [List.ofFn_succ, List.prod_cons, Fin.exists_fin_succ_pi, Fin.cons_zero, Fin.cons_succ,
      mem_mul, @ih, exists_exists_eq_and, SetCoe.exists, exists_prop]

@[to_additive]
/-
**Set.mem_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_list_prod {l : List (Set α)} {a : α} : a in l.prod ↔ exists l' : List 
(Σ s : Set α, ↥s), List.prod (l'.map fun x => (Sigma.snd x : α)) = a ∧ l'.map Si
gma.fst = l
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_ofFn`：∀ {n : ℕ} {α : Type u_1} {β : Type u_2} {f : Fin n → α} {
g : α → β}, List.map g (List.ofFn f) = List.ofFn (g ∘ f)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
-/
theorem mem_list_prod {l : List (Set α)} {a : α} :
    a ∈ l.prod ↔
      ∃ l' : List (Σ s : Set α, ↥s),
        List.prod (l'.map fun x ↦ (Sigma.snd x : α)) = a ∧ l'.map Sigma.fst = l := by
  induction l using List.ofFnRec with | _ n f
  simp only [mem_prod_list_ofFn, List.exists_iff_exists_tuple, List.map_ofFn, List.ofFn_inj',
    Sigma.mk.inj_iff, and_left_comm, exists_and_left, exists_eq_left, heq_eq_eq]
  constructor
  · rintro ⟨fi, rfl⟩
    exact ⟨fun i ↦ ⟨_, fi i⟩, rfl, rfl⟩
  · rintro ⟨fi, rfl, rfl⟩
    exact ⟨fun i ↦ _, rfl⟩

@[to_additive (attr := push)]
/-
**Set.mem_pow** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：mem_pow {a : α} {n : Nat} : a in s ^ n ↔ exists f : Fin n -> s, (List.ofFn
 fun i => (f i : α)).prod = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_prod_list_ofFn`：mem_prod_list_ofFn {a : α} {s : Fin n -> Set α} 
: a in (List.ofFn s).prod ↔ exists f : forall i : Fin n, s i, (List.ofFn fun i =
> (f i : α))…
· 使用定理 `List.ofFn_const`：∀ {α : Type u} (n : ℕ) (c : α), (List.ofFn fun x => c) 
= List.replicate n c
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_pow {a : α} {n : ℕ} :
    a ∈ s ^ n ↔ ∃ f : Fin n → s, (List.ofFn fun i ↦ (f i : α)).prod = a := by
  rw [← mem_prod_list_ofFn, List.ofFn_const, List.prod_replicate]

end Set

