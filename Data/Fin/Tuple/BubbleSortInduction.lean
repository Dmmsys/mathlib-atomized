/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.WellFounded
public import Mathlib.Order.PiLex
public import Mathlib.Data.Finite.Prod

/-!
# "Bubble sort" induction

We implement the following induction principle `Tuple.bubble_sort_induction`
on tuples with values in a linear order `α`.

Let `f : Fin n → α` and let `P` be a predicate on `Fin n → α`. Then we can show that
`f ∘ sort f` satisfies `P` if `f` satisfies `P`, and whenever some `g : Fin n → α`
satisfies `P` and `g i > g j` for some `i < j`, then `g ∘ swap i j` also satisfies `P`.

We deduce it from a stronger variant `Tuple.bubble_sort_induction'`, which
requires the assumption only for `g` that are permutations of `f`.

The latter is proved by well-founded induction via `WellFounded.induction_bot'`
with respect to the lexicographic ordering on the finite set of all permutations of `f`.
-/

public section


namespace Tuple

/-- *Bubble sort induction*: Prove that the sorted version of `f` has some property `P`
if `f` satisfies `P` and `P` is preserved on permutations of `f` when swapping two
antitone values. -/
/-
**Tuple.bubble_sort_induction'** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：bubble_sort_induction' {n : Nat} {α : Type*} [LinearOrder α] {f : Fin n ->
 α} {P : (Fin n -> α) -> Prop} (hf : P f) (h : forall (σ : Equiv.Perm (Fin n)) (
i j : Fin n), i < j -> (f ∘ σ) j < (f ∘ σ) i -> P (f ∘ σ) -> P (f ∘ σ ∘ Equiv.sw
ap i j)) : P (f ∘ sort f)
参数：Fin n -> α；hf : P f；h : forall (σ : Equiv.Perm (Fin n)) (i j : Fin n), i < j 
-> (f ∘ σ) j < (f ∘ σ) i -> P (f ∘ σ) -> P (f ∘ σ ∘ Equiv.swap i j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.induction_bot'`：WellFounded.induction_bot' {α β} {r : α -> α
 -> Prop} (hwf : WellFounded r) {a bot : α} {C : β -> Prop} {f : α -> β} (ih : f
orall b, f b != …
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `Finite.to_wellFoundedLT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedLT α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Tuple.antitone_pair_of_not_sorted'`：antitone_pair_of_not_sorted' (h : f 
∘ σ != f ∘ sort f) : exists i j, i < j ∧ (f ∘ σ) j < (f ∘ σ) i
· 使用定理 `Pi.lex_desc`：lex_desc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι -> 
α} {i j : ι} (h₁ : i <= j) (h₂ : f j < f i) : toLex (f ∘ Equiv.swap i j) < toLex
 …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
*Bubble sort induction*: Prove that the sorted version of `f` has some property 
`P`
if `f` satisfies `P` and `P` is preserved on permutations of `f` when swapping t
wo
antitone values.
-/
theorem bubble_sort_induction' {n : ℕ} {α : Type*} [LinearOrder α] {f : Fin n → α}
    {P : (Fin n → α) → Prop} (hf : P f)
    (h : ∀ (σ : Equiv.Perm (Fin n)) (i j : Fin n),
      i < j → (f ∘ σ) j < (f ∘ σ) i → P (f ∘ σ) → P (f ∘ σ ∘ Equiv.swap i j)) :
    P (f ∘ sort f) := by
  let := @Preorder.lift _ (Lex (Fin n → α)) _ fun σ : Equiv.Perm (Fin n) => toLex (f ∘ σ)
  refine
    @WellFounded.induction_bot' _ _ _ (IsWellFounded.wf : WellFounded (· < ·))
      (Equiv.refl _) (sort f) P (fun σ => f ∘ σ) (fun σ hσ hfσ => ?_) hf
  obtain ⟨i, j, hij₁, hij₂⟩ := antitone_pair_of_not_sorted' hσ
  exact ⟨σ * Equiv.swap i j, Pi.lex_desc hij₁.le hij₂, h σ i j hij₁ hij₂ hfσ⟩

/-- *Bubble sort induction*: Prove that the sorted version of `f` has some property `P`
if `f` satisfies `P` and `P` is preserved when swapping two antitone values. -/
/-
**Tuple.bubble_sort_induction** 是 Mathlib 中的一个定理，位于命名空间 `Tuple`。
形式化陈述：bubble_sort_induction {n : Nat} {α : Type*} [LinearOrder α] {f : Fin n -> 
α} {P : (Fin n -> α) -> Prop} (hf : P f) (h : forall (g : Fin n -> α) (i j : Fin
 n), i < j -> g j < g i -> P g -> P (g ∘ Equiv.swap i j)) : P (f ∘ sort f)
参数：Fin n -> α；hf : P f；h : forall (g : Fin n -> α) (i j : Fin n), i < j -> g j <
 g i -> P g -> P (g ∘ Equiv.swap i j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Tuple.bubble_sort_induction'`：bubble_sort_induction' {n : Nat} {α : Type
*} [LinearOrder α] {f : Fin n -> α} {P : (Fin n -> α) -> Prop} (hf : P f) (h : f
orall (σ : Equiv.P…

--- 原说明 ---
*Bubble sort induction*: Prove that the sorted version of `f` has some property 
`P`
if `f` satisfies `P` and `P` is preserved when swapping two antitone values.
-/
theorem bubble_sort_induction {n : ℕ} {α : Type*} [LinearOrder α] {f : Fin n → α}
    {P : (Fin n → α) → Prop} (hf : P f)
    (h : ∀ (g : Fin n → α) (i j : Fin n), i < j → g j < g i → P g → P (g ∘ Equiv.swap i j)) :
    P (f ∘ sort f) :=
  bubble_sort_induction' hf fun _ => h _

end Tuple

