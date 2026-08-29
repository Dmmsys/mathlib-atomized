/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Jovan Gerbscheid
-/
module

public import Mathlib.Tactic.GCongr.Core

/-!
# gcongr attributes for lemmas up in the import chain

In this file we add `gcongr` attribute to lemmas in `Lean.Init`.
We may add lemmas from other files imported by `Mathlib/Tactic/GCongr/Core` later.
-/

public meta section

namespace Mathlib.Tactic.GCongr

variable {a b c d : Prop}

/--
lemma `imp_mono` / 引理 `imp_mono`

English:
lemma imp_mono
  given: (h₁ : c -> a) (h₂ : c -> b -> d)
  statement: (a -> b) -> c -> d
  proof: fun h₃ hc => h₂ hc (h₃ (h₁ hc))

中文:
引理 imp_mono
  条件: (h₁ : c -> a) (h₂ : c -> b -> d)
  结论: (a -> b) -> c -> d
  证明: fun h₃ hc => h₂ hc (h₃ (h₁ hc))

Depends on / 依赖: OrderTopology, OrderTopology.t5Space, T5Space, T5Space.mk, t5Space
-/
lemma imp_mono (h₁ : c -> a) (h₂ : c -> b -> d) : (a -> b) -> c -> d :=
  fun h₃ hc => h₂ hc (h₃ (h₁ hc))

/--
lemma `and_mono` / 引理 `and_mono`

English:
lemma and_mono
  given: (h₁ : a -> c) (h₂ : a -> b -> d)
  statement: (a ∧ b) -> c ∧ d
  proof: fun ⟨ha, hb⟩ => ⟨h₁ ha, h₂ ha hb⟩

中文:
引理 and_mono
  条件: (h₁ : a -> c) (h₂ : a -> b -> d)
  结论: (a ∧ b) -> c ∧ d
  证明: fun ⟨ha, hb⟩ => ⟨h₁ ha, h₂ ha hb⟩
-/
lemma and_mono (h₁ : a -> c) (h₂ : a -> b -> d) : (a ∧ b) -> c ∧ d :=
  fun ⟨ha, hb⟩ => ⟨h₁ ha, h₂ ha hb⟩

attribute [gcongr] mt Or.imp and_mono imp_mono forall_imp Exists.imp
  List.Sublist.append List.Sublist.reverse List.drop_sublist_drop_left List.Sublist.drop
  List.Perm.cons List.Perm.append List.Perm.map
  List.cons_subset_cons
  Nat.sub_le_sub_left Nat.sub_le_sub_right Nat.sub_lt_sub_left Nat.sub_lt_sub_right

end Mathlib.Tactic.GCongr
