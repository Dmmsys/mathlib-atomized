/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.Preorder.Chain

/-!
# Range of `f : Fin (n + 1) → α` as a `Flag`

Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.

Then the range of `f` is a maximal chain.

We formulate this result in terms of `IsMaxChain` and `Flag`.
-/

@[expose] public section

open Set

variable {α : Type*} [PartialOrder α] [BoundedOrder α] {n : Nat} {f : Fin (n + 1) -> α}

/--
theorem `IsMaxChain.range_fin_of_covBy` / 定理 `IsMaxChain.range_fin_of_covBy`

English:
theorem IsMaxChain.range_fin_of_covBy
  statement: (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
  proof: by
  have hmono : Monotone f := Fin.monotone_iff_le_succ.2 fun k => (hcovBy k).1
  refine ⟨hmono.isChain_range, fun t htc hbt => hbt.antisymm fun x hx => ?_⟩
  rw [mem_range]; by_contra! h
  suffices forall k, f k < x by simpa [hlast] using this (.last _)
  intro k
  induction k using Fin.induction 

中文:
定理 IsMaxChain.range_fin_of_covBy
  结论: (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
  证明: by
  have hmono : Monotone f := Fin.monotone_iff_le_succ.2 fun k => (hcovBy k).1
  refine ⟨hmono.isChain_range, fun t htc hbt => hbt.antisymm fun x hx => ?_⟩
  rw [mem_range]; by_contra! h
  suffices forall k, f k < x by simpa [hlast] using this (.last _)
  intro k
  induction k using Fin.induction 

Depends on / 依赖: Fin.induction, Fin.monotone_iff_le_succ, Monotone, antisymm, bot_lt_iff_ne_bot, hbt.antisymm, hcovBy, hmono.isChain_range, htc.lt_of_le, isChain_range, k.succ, lt_of_le, mem_range, monotone_iff_le_succ, range_subset_iff, resolve_right
-/
theorem IsMaxChain.range_fin_of_covBy (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
    (hcovBy : forall k : Fin n, f k.castSucc ⩿ f k.succ) :
    IsMaxChain (· <= ·) (range f) := by
  have hmono : Monotone f := Fin.monotone_iff_le_succ.2 fun k => (hcovBy k).1
  refine ⟨hmono.isChain_range, fun t htc hbt => hbt.antisymm fun x hx => ?_⟩
  rw [mem_range]; by_contra! h
  suffices forall k, f k < x by simpa [hlast] using this (.last _)
  intro k
  induction k using Fin.induction with
  | zero => simpa [h0, bot_lt_iff_ne_bot] using (h 0).symm
  | succ k ihk =>
    rw [range_subset_iff] at hbt
    exact (htc.lt_of_le (hbt k.succ) hx (h _)).resolve_right ((hcovBy k).2 ihk)

/-- Let `f : Fin (n + 1) → α` be an `(n + 1)`-tuple `(f₀, …, fₙ)` such that
- `f₀ = ⊥` and `fₙ = ⊤`;
- `fₖ₊₁` weakly covers `fₖ` for all `0 ≤ k < n`;
  this means that `fₖ ≤ fₖ₊₁` and there is no `c` such that `fₖ<c<fₖ₊₁`.

Then the range of `f` is a `Flag α`. -/
@[simps]
/--
Definition of `Flag.rangeFin` / `Flag.rangeFin` 的定义

English:
definition Flag.rangeFin
  signature: (f : Fin (n + 1) -> α) (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
  body: range f
  Chain' := (IsMaxChain.range_fin_of_covBy h0 hlast hcovBy).1
  max_chain' := (IsMaxChain.range_fin_of_covBy h0 hlast hcovBy).2

中文:
定义 Flag.rangeFin
  签名: (f : Fin (n + 1) -> α) (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
  定义体: range f
  Chain' := (IsMaxChain.range_fin_of_covBy h0 hlast hcovBy).1
  max_chain' := (IsMaxChain.range_fin_of_covBy h0 hlast hcovBy).2
-/
def Flag.rangeFin (f : Fin (n + 1) -> α) (h0 : f 0 = ⊥) (hlast : f (.last n) = ⊤)
    (hcovBy : forall k : Fin n, f k.castSucc ⩿ f k.succ) : Flag α where
  carrier := range f
  Chain' := (IsMaxChain.range_fin_of_covBy h0 hlast hcovBy).1
  max_chain' := (IsMaxChain.range_fin_of_covBy h0 hlast hcovBy).2

/--
theorem `Flag.mem_rangeFin` / 定理 `Flag.mem_rangeFin`

English:
theorem Flag.mem_rangeFin
  given: {x h0 hlast hcovBy}
  proof: Iff.rfl

中文:
定理 Flag.mem_rangeFin
  条件: {x h0 hlast hcovBy}
  证明: Iff.rfl
-/
@[simp] theorem Flag.mem_rangeFin {x h0 hlast hcovBy} :
    x in rangeFin f h0 hlast hcovBy ↔ exists k, f k = x :=
  Iff.rfl
