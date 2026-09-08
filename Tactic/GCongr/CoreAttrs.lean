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

/-
**Mathlib.Tactic.GCongr.imp_mono** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.GCong
r`。
形式化陈述：imp_mono (h₁ : c -> a) (h₂ : c -> b -> d) : (a -> b) -> c -> d
参数：h₁ : c -> a；h₂ : c -> b -> d。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma imp_mono (h₁ : c → a) (h₂ : c → b → d) : (a → b) → c → d :=
  fun h₃ hc => h₂ hc (h₃ (h₁ hc))
/-
**Mathlib.Tactic.GCongr.and_mono** 是 Mathlib 中的一个引理，位于命名空间 `Mathlib.Tactic.GCong
r`。
形式化陈述：and_mono (h₁ : a -> c) (h₂ : a -> b -> d) : (a ∧ b) -> c ∧ d
参数：h₁ : a -> c；h₂ : a -> b -> d。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma and_mono (h₁ : a → c) (h₂ : a → b → d) : (a ∧ b) → c ∧ d :=
  fun ⟨ha, hb⟩ => ⟨h₁ ha, h₂ ha hb⟩

attribute [gcongr] mt Or.imp and_mono imp_mono forall_imp Exists.imp
  List.Sublist.append List.Sublist.reverse List.drop_sublist_drop_left List.Sublist.drop
  List.Perm.cons List.Perm.append List.Perm.map
  List.cons_subset_cons
  Nat.sub_le_sub_left Nat.sub_le_sub_right Nat.sub_lt_sub_left Nat.sub_lt_sub_right

end Mathlib.Tactic.GCongr

