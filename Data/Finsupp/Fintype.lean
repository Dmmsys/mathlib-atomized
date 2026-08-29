/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
module

public import Mathlib.Data.Finsupp.Single
public import Mathlib.Data.Fintype.BigOperators

/-!

# Finiteness and infiniteness of `Finsupp`

Some lemmas on the combination of `Finsupp`, `Fintype` and `Infinite`.

-/

public section

variable {ι α : Type*} [DecidableEq ι] [Fintype ι] [Zero α] [Fintype α]

/--
Instance `Finsupp.fintype` / 实例 `Finsupp.fintype`

English:
instance Finsupp.fintype
  signature: : Fintype (ι ->₀ α)
  body: Fintype.ofEquiv _ Finsupp.equivFunOnFinite.symm

中文:
实例 Finsupp.fintype
  签名: : Fintype (ι ->₀ α)
  定义体: Fintype.ofEquiv _ Finsupp.equivFunOnFinite.symm

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite.symm, Fintype, Fintype.ofEquiv, equivFunOnFinite, ofEquiv
-/
noncomputable instance Finsupp.fintype : Fintype (ι ->₀ α) :=
  Fintype.ofEquiv _ Finsupp.equivFunOnFinite.symm

/--
Instance `Finsupp.infinite_of_left` / 实例 `Finsupp.infinite_of_left`

English:
instance Finsupp.infinite_of_left
  signature: [Nontrivial α] [Infinite ι]
  body: let ⟨_, hm⟩ := exists_ne (0 : α)
Infinite.of_injective _ Finsupp.single_left_injective hm

中文:
实例 Finsupp.infinite_of_left
  签名: [Nontrivial α] [Infinite ι]
  定义体: let ⟨_, hm⟩ := exists_ne (0 : α)
Infinite.of_injective _ Finsupp.single_left_injective hm

Depends on / 依赖: Finsupp, Finsupp.single_left_injective, Infinite, Infinite.of_injective, exists_ne, of_injective, single_left_injective
-/
instance Finsupp.infinite_of_left [Nontrivial α] [Infinite ι] : Infinite (ι ->₀ α) :=
  let ⟨_, hm⟩ := exists_ne (0 : α)
Infinite.of_injective _ Finsupp.single_left_injective hm

/--
Instance `Finsupp.infinite_of_right` / 实例 `Finsupp.infinite_of_right`

English:
instance Finsupp.infinite_of_right
  signature: [Infinite α] [Nonempty ι]
  body: Infinite.of_injective (fun i => Finsupp.single (Classical.arbitrary ι) i)
    (Finsupp.single_injective (Classical.arbitrary ι))

中文:
实例 Finsupp.infinite_of_right
  签名: [Infinite α] [Nonempty ι]
  定义体: Infinite.of_injective (fun i => Finsupp.single (Classical.arbitrary ι) i)
    (Finsupp.single_injective (Classical.arbitrary ι))

Depends on / 依赖: Classical, Classical.arbitrary, Finsupp, Finsupp.single, Finsupp.single_injective, Infinite, Infinite.of_injective, arbitrary, of_injective, single, single_injective
-/
instance Finsupp.infinite_of_right [Infinite α] [Nonempty ι] : Infinite (ι ->₀ α) :=
  Infinite.of_injective (fun i => Finsupp.single (Classical.arbitrary ι) i)
    (Finsupp.single_injective (Classical.arbitrary ι))

variable (ι α) in
/--
lemma `Fintype.card_finsupp` / 引理 `Fintype.card_finsupp`

English:
lemma Fintype.card_finsupp
  statement: card (ι ->₀ α) = card α ^ card ι
  proof: by
  simp [card_congr Finsupp.equivFunOnFinite]

中文:
引理 Fintype.card_finsupp
  结论: card (ι ->₀ α) = card α ^ card ι
  证明: by
  simp [card_congr Finsupp.equivFunOnFinite]
-/
@[simp] lemma Fintype.card_finsupp : card (ι ->₀ α) = card α ^ card ι := by
  simp [card_congr Finsupp.equivFunOnFinite]
