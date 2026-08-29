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

/--
theorem `bubble_sort_induction'` / 定理 `bubble_sort_induction'`

English:
theorem bubble_sort_induction'
  statement: {n : Nat} {α : Type*} [LinearOrder α] {f : Fin n -> α}
  proof: by
  let := @Preorder.lift _ (Lex (Fin n -> α)) _ fun σ : Equiv.Perm (Fin n) => toLex (f ∘ σ)
  refine
    @WellFounded.induction_bot' _ _ _ (IsWellFounded.wf : WellFounded (· < ·))
      (Equiv.refl _) (sort f) P (fun σ => f ∘ σ) (fun σ hσ hfσ => ?_) hf
  obtain ⟨i, j, hij₁, hij₂⟩ := antitone_pair_

中文:
定理 bubble_sort_induction'
  结论: {n : 自然数} {α : 类型} [线性序 α] {f : 有限集 n -> α}
  证明: by
  let := @Preorder.lift _ (Lex (Fin n -> α)) _ fun σ : Equiv.Perm (Fin n) => toLex (f ∘ σ)
  refine
    @WellFounded.induction_bot' _ _ _ (IsWellFounded.wf : WellFounded (· < ·))
      (Equiv.refl _) (sort f) P (fun σ => f ∘ σ) (fun σ hσ hfσ => ?_) hf
  obtain ⟨i, j, hij₁, hij₂⟩ := antitone_pair_

Depends on / 依赖: Equiv.Perm, Equiv.refl, Equiv.swap, IsWellFounded, IsWellFounded.wf, Pi.lex_desc, Preorder, Preorder.lift, WellFounded, WellFounded.induction_bot, antitone_pair_of_not_sorted, induction_bot, lex_desc
-/
theorem bubble_sort_induction' {n : Nat} {α : Type*} [LinearOrder α] {f : Fin n -> α}
    {P : (Fin n -> α) -> Prop} (hf : P f)
    (h : forall (σ : Equiv.Perm (Fin n)) (i j : Fin n),
      i < j -> (f ∘ σ) j < (f ∘ σ) i -> P (f ∘ σ) -> P (f ∘ σ ∘ Equiv.swap i j)) :
    P (f ∘ sort f) := by
  let := @Preorder.lift _ (Lex (Fin n -> α)) _ fun σ : Equiv.Perm (Fin n) => toLex (f ∘ σ)
  refine
    @WellFounded.induction_bot' _ _ _ (IsWellFounded.wf : WellFounded (· < ·))
      (Equiv.refl _) (sort f) P (fun σ => f ∘ σ) (fun σ hσ hfσ => ?_) hf
  obtain ⟨i, j, hij₁, hij₂⟩ := antitone_pair_of_not_sorted' hσ
  exact ⟨σ * Equiv.swap i j, Pi.lex_desc hij₁.le hij₂, h σ i j hij₁ hij₂ hfσ⟩

/--
theorem `bubble_sort_induction` / 定理 `bubble_sort_induction`

English:
theorem bubble_sort_induction
  statement: {n : Nat} {α : Type*} [LinearOrder α] {f : Fin n -> α}
  proof: bubble_sort_induction' hf fun _ => h _

中文:
定理 bubble_sort_induction
  结论: {n : 自然数} {α : 类型} [线性序 α] {f : 有限集 n -> α}
  证明: bubble_sort_induction' hf fun _ => h _

Depends on / 依赖: bubble_sort_induction
-/
theorem bubble_sort_induction {n : Nat} {α : Type*} [LinearOrder α] {f : Fin n -> α}
    {P : (Fin n -> α) -> Prop} (hf : P f)
    (h : forall (g : Fin n -> α) (i j : Fin n), i < j -> g j < g i -> P g -> P (g ∘ Equiv.swap i j)) :
    P (f ∘ sort f) :=
  bubble_sort_induction' hf fun _ => h _

end Tuple
