/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Embedding
public import Mathlib.Algebra.Order.Interval.Set.Monoid
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Algebraic properties of finset intervals

This file provides results about the interaction of algebra with `Finset.Ixx`.
-/

public section

open Function OrderDual

variable {ι α : Type*}

namespace Finset
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedCancelAddMonoid α]
  [ExistsAddOfLE α] [LocallyFiniteOrder α]

/--
lemma `map_add_left_Icc` / 引理 `map_add_left_Icc`

English:
lemma map_add_left_Icc
  given: (a b c : α)
  proof: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.image_const_add_Icc _ _ _

中文:
引理 map_add_left_Icc
  条件: (a b c : α)
  证明: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.image_const_add_Icc _ _ _
-/
@[simp] lemma map_add_left_Icc (a b c : α) :
    (Icc a b).map (addLeftEmbedding c) = Icc (c + a) (c + b) := by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.image_const_add_Icc _ _ _

/--
lemma `map_add_right_Icc` / 引理 `map_add_right_Icc`

English:
lemma map_add_right_Icc
  given: (a b c : α)
  proof: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.image_add_const_Icc _ _ _

中文:
引理 map_add_right_Icc
  条件: (a b c : α)
  证明: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.image_add_const_Icc _ _ _
-/
@[simp] lemma map_add_right_Icc (a b c : α) :
    (Icc a b).map (addRightEmbedding c) = Icc (a + c) (b + c) := by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Icc]; rw [coe_Icc]
  exact Set.image_add_const_Icc _ _ _

/--
lemma `map_add_left_Ico` / 引理 `map_add_left_Ico`

English:
lemma map_add_left_Ico
  given: (a b c : α)
  proof: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ico]; rw [coe_Ico]
  exact Set.image_const_add_Ico _ _ _

中文:
引理 map_add_left_Ico
  条件: (a b c : α)
  证明: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ico]; rw [coe_Ico]
  exact Set.image_const_add_Ico _ _ _
-/
@[simp] lemma map_add_left_Ico (a b c : α) :
    (Ico a b).map (addLeftEmbedding c) = Ico (c + a) (c + b) := by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ico]; rw [coe_Ico]
  exact Set.image_const_add_Ico _ _ _

/--
lemma `map_add_right_Ico` / 引理 `map_add_right_Ico`

English:
lemma map_add_right_Ico
  given: (a b c : α)
  proof: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ico]; rw [coe_Ico]
  exact Set.image_add_const_Ico _ _ _

中文:
引理 map_add_right_Ico
  条件: (a b c : α)
  证明: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ico]; rw [coe_Ico]
  exact Set.image_add_const_Ico _ _ _
-/
@[simp] lemma map_add_right_Ico (a b c : α) :
    (Ico a b).map (addRightEmbedding c) = Ico (a + c) (b + c) := by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ico]; rw [coe_Ico]
  exact Set.image_add_const_Ico _ _ _

/--
lemma `map_add_left_Ioc` / 引理 `map_add_left_Ioc`

English:
lemma map_add_left_Ioc
  given: (a b c : α)
  proof: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioc]; rw [coe_Ioc]
  exact Set.image_const_add_Ioc _ _ _

中文:
引理 map_add_left_Ioc
  条件: (a b c : α)
  证明: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioc]; rw [coe_Ioc]
  exact Set.image_const_add_Ioc _ _ _
-/
@[simp] lemma map_add_left_Ioc (a b c : α) :
    (Ioc a b).map (addLeftEmbedding c) = Ioc (c + a) (c + b) := by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioc]; rw [coe_Ioc]
  exact Set.image_const_add_Ioc _ _ _

/--
lemma `map_add_right_Ioc` / 引理 `map_add_right_Ioc`

English:
lemma map_add_right_Ioc
  given: (a b c : α)
  proof: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioc]; rw [coe_Ioc]
  exact Set.image_add_const_Ioc _ _ _

中文:
引理 map_add_right_Ioc
  条件: (a b c : α)
  证明: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioc]; rw [coe_Ioc]
  exact Set.image_add_const_Ioc _ _ _
-/
@[simp] lemma map_add_right_Ioc (a b c : α) :
    (Ioc a b).map (addRightEmbedding c) = Ioc (a + c) (b + c) := by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioc]; rw [coe_Ioc]
  exact Set.image_add_const_Ioc _ _ _

/--
lemma `map_add_left_Ioo` / 引理 `map_add_left_Ioo`

English:
lemma map_add_left_Ioo
  given: (a b c : α)
  proof: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioo]; rw [coe_Ioo]
  exact Set.image_const_add_Ioo _ _ _

中文:
引理 map_add_left_Ioo
  条件: (a b c : α)
  证明: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioo]; rw [coe_Ioo]
  exact Set.image_const_add_Ioo _ _ _
-/
@[simp] lemma map_add_left_Ioo (a b c : α) :
    (Ioo a b).map (addLeftEmbedding c) = Ioo (c + a) (c + b) := by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioo]; rw [coe_Ioo]
  exact Set.image_const_add_Ioo _ _ _

/--
lemma `map_add_right_Ioo` / 引理 `map_add_right_Ioo`

English:
lemma map_add_right_Ioo
  given: (a b c : α)
  proof: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioo]; rw [coe_Ioo]
  exact Set.image_add_const_Ioo _ _ _

中文:
引理 map_add_right_Ioo
  条件: (a b c : α)
  证明: by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioo]; rw [coe_Ioo]
  exact Set.image_add_const_Ioo _ _ _
-/
@[simp] lemma map_add_right_Ioo (a b c : α) :
    (Ioo a b).map (addRightEmbedding c) = Ioo (a + c) (b + c) := by
  rw [← coe_inj]; rw [coe_map]; rw [coe_Ioo]; rw [coe_Ioo]
  exact Set.image_add_const_Ioo _ _ _

variable [DecidableEq α]

/--
lemma `image_add_left_Icc` / 引理 `image_add_left_Icc`

English:
lemma image_add_left_Icc
  given: (a b c : α)
  statement: (Icc a b).image (c + ·) = Icc (c + a) (c + b)
  proof: by
  rw [← map_add_left_Icc]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]

中文:
引理 image_add_left_Icc
  条件: (a b c : α)
  结论: (Icc a b).image (c + ·) = Icc (c + a) (c + b)
  证明: by
  rw [← map_add_left_Icc]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]
-/
@[simp] lemma image_add_left_Icc (a b c : α) : (Icc a b).image (c + ·) = Icc (c + a) (c + b) := by
  rw [← map_add_left_Icc]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]

/--
lemma `image_add_left_Ico` / 引理 `image_add_left_Ico`

English:
lemma image_add_left_Ico
  given: (a b c : α)
  statement: (Ico a b).image (c + ·) = Ico (c + a) (c + b)
  proof: by
  rw [← map_add_left_Ico]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]

中文:
引理 image_add_left_Ico
  条件: (a b c : α)
  结论: (Ico a b).image (c + ·) = Ico (c + a) (c + b)
  证明: by
  rw [← map_add_left_Ico]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]
-/
@[simp] lemma image_add_left_Ico (a b c : α) : (Ico a b).image (c + ·) = Ico (c + a) (c + b) := by
  rw [← map_add_left_Ico]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]

/--
lemma `image_add_left_Ioc` / 引理 `image_add_left_Ioc`

English:
lemma image_add_left_Ioc
  given: (a b c : α)
  statement: (Ioc a b).image (c + ·) = Ioc (c + a) (c + b)
  proof: by
  rw [← map_add_left_Ioc]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]

中文:
引理 image_add_left_Ioc
  条件: (a b c : α)
  结论: (Ioc a b).image (c + ·) = Ioc (c + a) (c + b)
  证明: by
  rw [← map_add_left_Ioc]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]
-/
@[simp] lemma image_add_left_Ioc (a b c : α) : (Ioc a b).image (c + ·) = Ioc (c + a) (c + b) := by
  rw [← map_add_left_Ioc]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]

/--
lemma `image_add_left_Ioo` / 引理 `image_add_left_Ioo`

English:
lemma image_add_left_Ioo
  given: (a b c : α)
  statement: (Ioo a b).image (c + ·) = Ioo (c + a) (c + b)
  proof: by
  rw [← map_add_left_Ioo]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]

中文:
引理 image_add_left_Ioo
  条件: (a b c : α)
  结论: (Ioo a b).image (c + ·) = Ioo (c + a) (c + b)
  证明: by
  rw [← map_add_left_Ioo]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]
-/
@[simp] lemma image_add_left_Ioo (a b c : α) : (Ioo a b).image (c + ·) = Ioo (c + a) (c + b) := by
  rw [← map_add_left_Ioo]; rw [map_eq_image]; rw [addLeftEmbedding]; rw [Embedding.coeFn_mk]

/--
lemma `image_add_right_Icc` / 引理 `image_add_right_Icc`

English:
lemma image_add_right_Icc
  given: (a b c : α)
  statement: (Icc a b).image (· + c) = Icc (a + c) (b + c)
  proof: by
  rw [← map_add_right_Icc]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]

中文:
引理 image_add_right_Icc
  条件: (a b c : α)
  结论: (Icc a b).image (· + c) = Icc (a + c) (b + c)
  证明: by
  rw [← map_add_right_Icc]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]
-/
@[simp] lemma image_add_right_Icc (a b c : α) : (Icc a b).image (· + c) = Icc (a + c) (b + c) := by
  rw [← map_add_right_Icc]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]

/--
lemma `image_add_right_Ico` / 引理 `image_add_right_Ico`

English:
lemma image_add_right_Ico
  given: (a b c : α)
  statement: (Ico a b).image (· + c) = Ico (a + c) (b + c)
  proof: by
  rw [← map_add_right_Ico]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]

中文:
引理 image_add_right_Ico
  条件: (a b c : α)
  结论: (Ico a b).image (· + c) = Ico (a + c) (b + c)
  证明: by
  rw [← map_add_right_Ico]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]
-/
@[simp] lemma image_add_right_Ico (a b c : α) : (Ico a b).image (· + c) = Ico (a + c) (b + c) := by
  rw [← map_add_right_Ico]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]

/--
lemma `image_add_right_Ioc` / 引理 `image_add_right_Ioc`

English:
lemma image_add_right_Ioc
  given: (a b c : α)
  statement: (Ioc a b).image (· + c) = Ioc (a + c) (b + c)
  proof: by
  rw [← map_add_right_Ioc]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]

中文:
引理 image_add_right_Ioc
  条件: (a b c : α)
  结论: (Ioc a b).image (· + c) = Ioc (a + c) (b + c)
  证明: by
  rw [← map_add_right_Ioc]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]
-/
@[simp] lemma image_add_right_Ioc (a b c : α) : (Ioc a b).image (· + c) = Ioc (a + c) (b + c) := by
  rw [← map_add_right_Ioc]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]

/--
lemma `image_add_right_Ioo` / 引理 `image_add_right_Ioo`

English:
lemma image_add_right_Ioo
  given: (a b c : α)
  statement: (Ioo a b).image (· + c) = Ioo (a + c) (b + c)
  proof: by
  rw [← map_add_right_Ioo]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]

中文:
引理 image_add_right_Ioo
  条件: (a b c : α)
  结论: (Ioo a b).image (· + c) = Ioo (a + c) (b + c)
  证明: by
  rw [← map_add_right_Ioo]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]
-/
@[simp] lemma image_add_right_Ioo (a b c : α) : (Ioo a b).image (· + c) = Ioo (a + c) (b + c) := by
  rw [← map_add_right_Ioo]; rw [map_eq_image]; rw [addRightEmbedding]; rw [Embedding.coeFn_mk]

end Finset
