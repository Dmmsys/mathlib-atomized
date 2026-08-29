/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Data.Set.Finite.Basic

/-! # Finiteness lemmas for pointwise operations on sets -/

public section

open scoped Pointwise

namespace Set
variable {G α : Type*} [Group G] [MulAction G α] {a : G} {s : Set α}

@[to_additive (attr := simp)]
/--
lemma `finite_smul_set` / 引理 `finite_smul_set`

English:
lemma finite_smul_set
  statement: (a • s).Finite ↔ s.Finite
  proof: finite_image_iff (MulAction.injective _).injOn

@[to_additive (attr := simp)]

中文:
引理 finite_smul_set
  结论: (a • s).有限 ↔ s.有限
  证明: finite_image_iff (MulAction.injective _).injOn

@[to_additive (attr := simp)]

Depends on / 依赖: MulAction, MulAction.injective, finite_image_iff, injective
-/
lemma finite_smul_set : (a • s).Finite ↔ s.Finite := finite_image_iff (MulAction.injective _).injOn

@[to_additive (attr := simp)]
/--
lemma `infinite_smul_set` / 引理 `infinite_smul_set`

English:
lemma infinite_smul_set
  statement: (a • s).Infinite ↔ s.Infinite
  proof: infinite_image_iff (MulAction.injective _).injOn

@[to_additive] alias ⟨Finite.of_smul_set, _⟩ := finite_smul_set
@[to_additive] alias ⟨_, Infinite.smul_set⟩ := infinite_smul_set

中文:
引理 infinite_smul_set
  结论: (a • s).无限 ↔ s.无限
  证明: infinite_image_iff (MulAction.injective _).injOn

@[to_additive] alias ⟨Finite.of_smul_set, _⟩ := finite_smul_set
@[to_additive] alias ⟨_, Infinite.smul_set⟩ := infinite_smul_set

Depends on / 依赖: MulAction, MulAction.injective, infinite_image_iff, injective
-/
lemma infinite_smul_set : (a • s).Infinite ↔ s.Infinite :=
  infinite_image_iff (MulAction.injective _).injOn

@[to_additive] alias ⟨Finite.of_smul_set, _⟩ := finite_smul_set
@[to_additive] alias ⟨_, Infinite.smul_set⟩ := infinite_smul_set

end Set
