/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Ring.Nat

/-!
# e-transforms

e-transforms are a family of transformations of pairs of finite sets that aim to reduce the size
of the sumset while keeping some invariant the same. This file defines a few of them, to be used
as internals of other proofs.

## Main declarations

* `Finset.mulDysonETransform`: The Dyson e-transform. Replaces `(s, t)` by
  `(s ∪ e • t, t ∩ e⁻¹ • s)`. The additive version preserves `|s ∩ [1, m]| + |t ∩ [1, m - e]|`.
* `Finset.mulETransformLeft`/`Finset.mulETransformRight`: Replace `(s, t)` by
  `(s ∩ s • e, t ∪ e⁻¹ • t)` and `(s ∪ s • e, t ∩ e⁻¹ • t)`. Preserve (together) the sum of
  the cardinalities (see `Finset.MulETransform.card`). In particular, one of the two transforms
  increases the sum of the cardinalities and the other one decreases it. See
  `le_or_lt_of_add_le_add` and around.

## TODO

Prove the invariance property of the Dyson e-transform.
-/

@[expose] public section


open MulOpposite

open scoped Pointwise

variable {α : Type*} [DecidableEq α]

namespace Finset

/-! ### Dyson e-transform -/


section CommGroup

variable [CommGroup α] (e : α) (x : Finset α × Finset α)

/-- The **Dyson e-transform**. Turns `(s, t)` into `(s ∪ e • t, t ∩ e⁻¹ • s)`. This reduces the
product of the two sets. -/
@[to_additive (attr := simps) /-- The **Dyson e-transform**.
Turns `(s, t)` into `(s ∪ e +ᵥ t, t ∩ -e +ᵥ s)`. This reduces the sum of the two sets. -/]
/--
Definition of `mulDysonETransform` / `mulDysonETransform` 的定义

English:
definition mulDysonETransform
  signature: : Finset α × Finset α
  body: (x.1 union e • x.2, x.2 inter e⁻¹ • x.1)

@[to_additive]

中文:
定义 mulDysonETransform
  签名: : Finset α × Finset α
  定义体: (x.1 union e • x.2, x.2 inter e⁻¹ • x.1)

@[to_additive]
-/
def mulDysonETransform : Finset α × Finset α :=
  (x.1 union e • x.2, x.2 inter e⁻¹ • x.1)

@[to_additive]
/--
theorem `mulDysonETransform.subset` / 定理 `mulDysonETransform.subset`

English:
theorem mulDysonETransform.subset
  proof: by
  refine union_mul_inter_subset_union.trans (union_subset Subset.rfl ?_)
  rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [inv_smul_smul]; rw [mul_comm]

中文:
定理 mulDysonETransform.subset
  证明: by
  refine union_mul_inter_subset_union.trans (union_subset Subset.rfl ?_)
  rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [inv_smul_smul]; rw [mul_comm]

Depends on / 依赖: Subset, Subset.rfl, inv_smul_smul, mul_comm, mul_smul_comm, smul_mul_assoc, union_mul_inter_subset_union, union_mul_inter_subset_union.trans, union_subset
-/
theorem mulDysonETransform.subset :
    (mulDysonETransform e x).1 * (mulDysonETransform e x).2 subseteq x.1 * x.2 := by
  refine union_mul_inter_subset_union.trans (union_subset Subset.rfl ?_)
  rw [mul_smul_comm]; rw [smul_mul_assoc]; rw [inv_smul_smul]; rw [mul_comm]

set_option backward.defeqAttrib.useBackward true in
@[to_additive]
/--
theorem `mulDysonETransform.card` / 定理 `mulDysonETransform.card`

English:
theorem mulDysonETransform.card
  proof: by
  dsimp
  rw [← card_smul_finset e (_ inter _)]; rw [smul_finset_inter]; rw [smul_inv_smul]; rw [inter_comm]; rw [card_union_add_card_inter]; rw [card_smul_finset]

中文:
定理 mulDysonETransform.card
  证明: by
  dsimp
  rw [← card_smul_finset e (_ inter _)]; rw [smul_finset_inter]; rw [smul_inv_smul]; rw [inter_comm]; rw [card_union_add_card_inter]; rw [card_smul_finset]

Depends on / 依赖: card_smul_finset, card_union_add_card_inter, inter_comm, smul_finset_inter, smul_inv_smul
-/
theorem mulDysonETransform.card :
    (mulDysonETransform e x).1.card + (mulDysonETransform e x).2.card = x.1.card + x.2.card := by
  dsimp
  rw [← card_smul_finset e (_ inter _)]; rw [smul_finset_inter]; rw [smul_inv_smul]; rw [inter_comm]; rw [card_union_add_card_inter]; rw [card_smul_finset]

set_option backward.defeqAttrib.useBackward true in
@[to_additive (attr := simp)]
/--
theorem `mulDysonETransform_idem` / 定理 `mulDysonETransform_idem`

English:
theorem mulDysonETransform_idem
  proof: by
  ext : 1 <;> dsimp
  · rw [smul_finset_inter, smul_inv_smul, inter_comm, union_eq_left]
    exact inter_subset_union
  · rw [smul_finset_union, inv_smul_smul, union_comm, inter_eq_left]
    exact inter_subset_union

中文:
定理 mulDysonETransform_idem
  证明: by
  ext : 1 <;> dsimp
  · rw [smul_finset_inter, smul_inv_smul, inter_comm, union_eq_left]
    exact inter_subset_union
  · rw [smul_finset_union, inv_smul_smul, union_comm, inter_eq_left]
    exact inter_subset_union

Depends on / 依赖: inter_comm, inter_eq_left, inter_subset_union, inv_smul_smul, smul_finset_inter, smul_finset_union, smul_inv_smul, union_comm, union_eq_left
-/
theorem mulDysonETransform_idem :
    mulDysonETransform e (mulDysonETransform e x) = mulDysonETransform e x := by
  ext : 1 <;> dsimp
  · rw [smul_finset_inter, smul_inv_smul, inter_comm, union_eq_left]
    exact inter_subset_union
  · rw [smul_finset_union, inv_smul_smul, union_comm, inter_eq_left]
    exact inter_subset_union

variable {e x}

set_option backward.defeqAttrib.useBackward true in
@[to_additive]
/--
theorem `mulDysonETransform.smul_finset_snd_subset_fst` / 定理 `mulDysonETransform.smul_finset_snd_subset_fst`

English:
theorem mulDysonETransform.smul_finset_snd_subset_fst
  proof: by
  dsimp
  rw [smul_finset_inter]; rw [smul_inv_smul]; rw [inter_comm]
  exact inter_subset_union

中文:
定理 mulDysonETransform.smul_finset_snd_subset_fst
  证明: by
  dsimp
  rw [smul_finset_inter]; rw [smul_inv_smul]; rw [inter_comm]
  exact inter_subset_union

Depends on / 依赖: inter_comm, inter_subset_union, smul_finset_inter, smul_inv_smul
-/
theorem mulDysonETransform.smul_finset_snd_subset_fst :
    e • (mulDysonETransform e x).2 subseteq (mulDysonETransform e x).1 := by
  dsimp
  rw [smul_finset_inter]; rw [smul_inv_smul]; rw [inter_comm]
  exact inter_subset_union

end CommGroup

/-!
### Two unnamed e-transforms

The following two transforms both reduce the product/sum of the two sets. Further, one of them must
decrease the sum of the size of the sets (and then the other increases it).

This pair of transforms doesn't seem to be named in the literature. It is used by Sanders in his
bound on Roth numbers, and by DeVos in his proof of Cauchy-Davenport.
-/


section Group

variable [Group α] (e : α) (x : Finset α × Finset α)

/-- An **e-transform**. Turns `(s, t)` into `(s ∩ s • e, t ∪ e⁻¹ • t)`. This reduces the
product of the two sets. -/
@[to_additive (attr := simps) /-- An **e-transform**.
Turns `(s, t)` into `(s ∩ s +ᵥ e, t ∪ -e +ᵥ t)`. This reduces the sum of the two sets. -/]
/--
Definition of `mulETransformLeft` / `mulETransformLeft` 的定义

English:
definition mulETransformLeft
  signature: : Finset α × Finset α
  body: (x.1 inter op e • x.1, x.2 union e⁻¹ • x.2)

中文:
定义 mulETransformLeft
  签名: : Finset α × Finset α
  定义体: (x.1 inter op e • x.1, x.2 union e⁻¹ • x.2)
-/
def mulETransformLeft : Finset α × Finset α :=
  (x.1 inter op e • x.1, x.2 union e⁻¹ • x.2)

/-- An **e-transform**. Turns `(s, t)` into `(s ∪ s • e, t ∩ e⁻¹ • t)`. This reduces the
product of the two sets. -/
@[to_additive (attr := simps) /-- An **e-transform**.
Turns `(s, t)` into `(s ∪ s +ᵥ e, t ∩ -e +ᵥ t)`. This reduces the sum of the two sets. -/]
/--
Definition of `mulETransformRight` / `mulETransformRight` 的定义

English:
definition mulETransformRight
  signature: : Finset α × Finset α
  body: (x.1 union op e • x.1, x.2 inter e⁻¹ • x.2)

@[to_additive (attr := simp)]

中文:
定义 mulETransformRight
  签名: : Finset α × Finset α
  定义体: (x.1 union op e • x.1, x.2 inter e⁻¹ • x.2)

@[to_additive (attr := simp)]
-/
def mulETransformRight : Finset α × Finset α :=
  (x.1 union op e • x.1, x.2 inter e⁻¹ • x.2)

@[to_additive (attr := simp)]
/--
theorem `mulETransformLeft_one` / 定理 `mulETransformLeft_one`

English:
theorem mulETransformLeft_one
  statement: mulETransformLeft 1 x = x
  proof: by simp [mulETransformLeft]

@[to_additive (attr := simp)]

中文:
定理 mulETransformLeft_one
  结论: mulETransformLeft 1 x = x
  证明: by simp [mulETransformLeft]

@[to_additive (attr := simp)]

Depends on / 依赖: mulETransformLeft
-/
theorem mulETransformLeft_one : mulETransformLeft 1 x = x := by simp [mulETransformLeft]

@[to_additive (attr := simp)]
/--
theorem `mulETransformRight_one` / 定理 `mulETransformRight_one`

English:
theorem mulETransformRight_one
  statement: mulETransformRight 1 x = x
  proof: by simp [mulETransformRight]

@[to_additive]

中文:
定理 mulETransformRight_one
  结论: mulETransformRight 1 x = x
  证明: by simp [mulETransformRight]

@[to_additive]

Depends on / 依赖: mulETransformRight
-/
theorem mulETransformRight_one : mulETransformRight 1 x = x := by simp [mulETransformRight]

@[to_additive]
/--
theorem `mulETransformLeft.fst_mul_snd_subset` / 定理 `mulETransformLeft.fst_mul_snd_subset`

English:
theorem mulETransformLeft.fst_mul_snd_subset
  proof: by
  refine inter_mul_union_subset_union.trans (union_subset Subset.rfl ?_)
  rw [op_smul_finset_mul_eq_mul_smul_finset]; rw [smul_inv_smul]

@[to_additive]

中文:
定理 mulETransformLeft.fst_mul_snd_subset
  证明: by
  refine inter_mul_union_subset_union.trans (union_subset Subset.rfl ?_)
  rw [op_smul_finset_mul_eq_mul_smul_finset]; rw [smul_inv_smul]

@[to_additive]

Depends on / 依赖: Subset, Subset.rfl, inter_mul_union_subset_union, inter_mul_union_subset_union.trans, op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul, union_subset
-/
theorem mulETransformLeft.fst_mul_snd_subset :
    (mulETransformLeft e x).1 * (mulETransformLeft e x).2 subseteq x.1 * x.2 := by
  refine inter_mul_union_subset_union.trans (union_subset Subset.rfl ?_)
  rw [op_smul_finset_mul_eq_mul_smul_finset]; rw [smul_inv_smul]

@[to_additive]
/--
theorem `mulETransformRight.fst_mul_snd_subset` / 定理 `mulETransformRight.fst_mul_snd_subset`

English:
theorem mulETransformRight.fst_mul_snd_subset
  proof: by
  refine union_mul_inter_subset_union.trans (union_subset Subset.rfl ?_)
  rw [op_smul_finset_mul_eq_mul_smul_finset]; rw [smul_inv_smul]

@[to_additive]

中文:
定理 mulETransformRight.fst_mul_snd_subset
  证明: by
  refine union_mul_inter_subset_union.trans (union_subset Subset.rfl ?_)
  rw [op_smul_finset_mul_eq_mul_smul_finset]; rw [smul_inv_smul]

@[to_additive]

Depends on / 依赖: Subset, Subset.rfl, op_smul_finset_mul_eq_mul_smul_finset, smul_inv_smul, union_mul_inter_subset_union, union_mul_inter_subset_union.trans, union_subset
-/
theorem mulETransformRight.fst_mul_snd_subset :
    (mulETransformRight e x).1 * (mulETransformRight e x).2 subseteq x.1 * x.2 := by
  refine union_mul_inter_subset_union.trans (union_subset Subset.rfl ?_)
  rw [op_smul_finset_mul_eq_mul_smul_finset]; rw [smul_inv_smul]

@[to_additive]
/--
theorem `mulETransformLeft.card` / 定理 `mulETransformLeft.card`

English:
theorem mulETransformLeft.card
  proof: (card_inter_add_card_union _ _).trans by rw [card_smul_finset, two_mul]

@[to_additive]

中文:
定理 mulETransformLeft.card
  证明: (card_inter_add_card_union _ _).trans by rw [card_smul_finset, two_mul]

@[to_additive]

Depends on / 依赖: card_inter_add_card_union, card_smul_finset, two_mul
-/
theorem mulETransformLeft.card :
    (mulETransformLeft e x).1.card + (mulETransformRight e x).1.card = 2 * x.1.card :=
(card_inter_add_card_union _ _).trans by rw [card_smul_finset, two_mul]

@[to_additive]
/--
theorem `mulETransformRight.card` / 定理 `mulETransformRight.card`

English:
theorem mulETransformRight.card
  proof: (card_union_add_card_inter _ _).trans by rw [card_smul_finset, two_mul]

中文:
定理 mulETransformRight.card
  证明: (card_union_add_card_inter _ _).trans by rw [card_smul_finset, two_mul]

Depends on / 依赖: card_smul_finset, card_union_add_card_inter, two_mul
-/
theorem mulETransformRight.card :
    (mulETransformLeft e x).2.card + (mulETransformRight e x).2.card = 2 * x.2.card :=
(card_union_add_card_inter _ _).trans by rw [card_smul_finset, two_mul]

/-- This statement is meant to be combined with `le_or_lt_of_add_le_add` and similar lemmas. -/
@[to_additive AddETransform.card /-- This statement is meant to be combined with
`le_or_lt_of_add_le_add` and similar lemmas. -/]
/--
theorem `MulETransform.card` / 定理 `MulETransform.card`

English:
theorem MulETransform.card
  proof: by
  rw [add_add_add_comm]; rw [mulETransformLeft.card]; rw [mulETransformRight.card]; rw [← mul_add]; rw [two_mul]

中文:
定理 MulETransform.card
  证明: by
  rw [add_add_add_comm]; rw [mulETransformLeft.card]; rw [mulETransformRight.card]; rw [← mul_add]; rw [two_mul]
-/
protected theorem MulETransform.card :
    (mulETransformLeft e x).1.card + (mulETransformLeft e x).2.card +
        ((mulETransformRight e x).1.card + (mulETransformRight e x).2.card) =
      x.1.card + x.2.card + (x.1.card + x.2.card) := by
  rw [add_add_add_comm]; rw [mulETransformLeft.card]; rw [mulETransformRight.card]; rw [← mul_add]; rw [two_mul]

end Group

section CommGroup

variable [CommGroup α] (e : α) (x : Finset α × Finset α)

@[to_additive (attr := simp)]
/--
theorem `mulETransformLeft_inv` / 定理 `mulETransformLeft_inv`

English:
theorem mulETransformLeft_inv
  statement: mulETransformLeft e⁻¹ x = (mulETransformRight e x.swap).swap
  proof: by
  simp [-op_inv, op_smul_eq_smul, mulETransformLeft, mulETransformRight]

@[to_additive (attr := simp)]

中文:
定理 mulETransformLeft_inv
  结论: mulETransformLeft e⁻¹ x = (mulETransformRight e x.swap).swap
  证明: by
  simp [-op_inv, op_smul_eq_smul, mulETransformLeft, mulETransformRight]

@[to_additive (attr := simp)]

Depends on / 依赖: mulETransformLeft, mulETransformRight, op_inv, op_smul_eq_smul
-/
theorem mulETransformLeft_inv : mulETransformLeft e⁻¹ x = (mulETransformRight e x.swap).swap := by
  simp [-op_inv, op_smul_eq_smul, mulETransformLeft, mulETransformRight]

@[to_additive (attr := simp)]
/--
theorem `mulETransformRight_inv` / 定理 `mulETransformRight_inv`

English:
theorem mulETransformRight_inv
  statement: mulETransformRight e⁻¹ x = (mulETransformLeft e x.swap).swap
  proof: by
  simp [-op_inv, op_smul_eq_smul, mulETransformLeft, mulETransformRight]

中文:
定理 mulETransformRight_inv
  结论: mulETransformRight e⁻¹ x = (mulETransformLeft e x.swap).swap
  证明: by
  simp [-op_inv, op_smul_eq_smul, mulETransformLeft, mulETransformRight]

Depends on / 依赖: mulETransformLeft, mulETransformRight, op_inv, op_smul_eq_smul
-/
theorem mulETransformRight_inv : mulETransformRight e⁻¹ x = (mulETransformLeft e x.swap).swap := by
  simp [-op_inv, op_smul_eq_smul, mulETransformLeft, mulETransformRight]

end CommGroup

end Finset
