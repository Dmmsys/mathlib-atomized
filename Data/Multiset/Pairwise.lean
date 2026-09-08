/-
Copyright (c) 2025 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.Multiset.Defs

/-!
# Pairwise relations on a multiset

This file provides basic results about `Multiset.Pairwise` (definitions are in
`Mathlib/Data/Multiset/Defs.lean`).
-/

public section

namespace Multiset

variable {α : Type*} {r : α → α → Prop} {s : Multiset α}

/-
**Multiset.Pairwise.forall** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {s : Multiset α} [Std.Symm r],   Multi
set.Pairwise r s → ∀ ⦃a : α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ s → a ≠ b → r a b
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.forall`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} [
Std.Symm R],   List.Pairwise R l → ∀ ⦃a : α⦄, a ∈ l → ∀ ⦃b : α⦄, b ∈ l → a ≠ b →
 R a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Pairwise.forall [Std.Symm r] (hs : Pairwise r s) :
    ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ≠ b → r a b :=
  let ⟨_, hl₁, hl₂⟩ := hs
  hl₁.symm ▸ hl₂.forall

end Multiset

