/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality of sets under pointwise group with zero operations
-/

public section

assert_not_exists Field

open scoped Cardinal Pointwise

variable {G₀ M₀ : Type*}

namespace Set
variable [GroupWithZero G₀] [Zero M₀] [MulActionWithZero G₀ M₀] {a : G₀}

/--
lemma `_root_.Cardinal.mk_smul_set₀` / 引理 `_root_.Cardinal.mk_smul_set₀`

English:
lemma _root_.Cardinal.mk_smul_set₀
  given: (ha : a != 0) (s : Set M₀)
  statement: #↥(a • s) = #s
  proof: Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective₀ ha).injOn

中文:
引理 _root_.Cardinal.mk_smul_set₀
  条件: (ha : a != 0) (s : Set M₀)
  结论: #↥(a • s) = #s
  证明: Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective₀ ha).injOn

Depends on / 依赖: Cardinal, Cardinal.mk_image_eq_of_injOn, MulAction, MulAction.injective, mk_image_eq_of_injOn
-/
lemma _root_.Cardinal.mk_smul_set₀ (ha : a != 0) (s : Set M₀) : #↥(a • s) = #s :=
  Cardinal.mk_image_eq_of_injOn _ _ (MulAction.injective₀ ha).injOn

/--
lemma `natCard_smul_set₀` / 引理 `natCard_smul_set₀`

English:
lemma natCard_smul_set₀
  given: (ha : a != 0) (s : Set M₀)
  statement: Nat.card ↥(a • s) = Nat.card s
  proof: Nat.card_image_of_injective (MulAction.injective₀ ha) _

中文:
引理 natCard_smul_set₀
  条件: (ha : a != 0) (s : Set M₀)
  结论: 自然数.card ↥(a • s) = 自然数.card s
  证明: Nat.card_image_of_injective (MulAction.injective₀ ha) _

Depends on / 依赖: MulAction, MulAction.injective, Nat.card_image_of_injective, card_image_of_injective
-/
lemma natCard_smul_set₀ (ha : a != 0) (s : Set M₀) : Nat.card ↥(a • s) = Nat.card s :=
  Nat.card_image_of_injective (MulAction.injective₀ ha) _

end Set
