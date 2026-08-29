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

variable {α : Type*} {r : α -> α -> Prop} {s : Multiset α}

/--
theorem `Pairwise.forall` / 定理 `Pairwise.forall`

English:
theorem Pairwise.forall
  given: [Std.Symm r] (hs : Pairwise r s)
  proof: let ⟨_, hl₁, hl₂⟩ := hs
  hl₁.symm ▸ hl₂.forall

中文:
定理 Pairwise.forall
  条件: [Std.Symm r] (hs : Pairwise r s)
  证明: let ⟨_, hl₁, hl₂⟩ := hs
  hl₁.symm ▸ hl₂.forall
-/
theorem Pairwise.forall [Std.Symm r] (hs : Pairwise r s) :
    forall ⦃a⦄, a in s -> forall ⦃b⦄, b in s -> a != b -> r a b :=
  let ⟨_, hl₁, hl₂⟩ := hs
  hl₁.symm ▸ hl₂.forall

end Multiset
