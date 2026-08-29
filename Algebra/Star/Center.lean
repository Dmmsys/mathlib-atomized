/-
Copyright (c) 2023 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.Algebra.Star.Pointwise
public import Mathlib.Algebra.Group.Center

/-! # `Set.center`, `Set.centralizer` and the `star` operation -/

public section

variable {R : Type*} [Mul R] [StarMul R] {a : R} {s : Set R}

/--
theorem `Set.star_mem_center` / 定理 `Set.star_mem_center`

English:
theorem Set.star_mem_center
  given: (ha : a in Set.center R)
  statement: star a in Set.center R where
  proof: by simpa only [star_mul, star_star] using! fun g =>
    congr_arg star ((mem_center_iff.1 ha).comm <| star g).symm
  left_assoc b c := by
    simpa only [star_mul, star_star] using congr_arg star (ha.right_assoc (star c) (star b))
  right_assoc b c := by
    simpa only [star_mul, star_star] using co

中文:
定理 Set.star_mem_center
  条件: (ha : a in Set.center R)
  结论: star a in Set.center R where
  证明: by simpa only [star_mul, star_star] using! fun g =>
    congr_arg star ((mem_center_iff.1 ha).comm <| star g).symm
  left_assoc b c := by
    simpa only [star_mul, star_star] using congr_arg star (ha.right_assoc (star c) (star b))
  right_assoc b c := by
    simpa only [star_mul, star_star] using co

Depends on / 依赖: congr_arg, ha.left_assoc, ha.right_assoc, left_assoc, mem_center_iff, right_assoc, star_mul, star_star
-/
theorem Set.star_mem_center (ha : a in Set.center R) : star a in Set.center R where
  comm := by simpa only [star_mul, star_star] using! fun g =>
    congr_arg star ((mem_center_iff.1 ha).comm <| star g).symm
  left_assoc b c := by
    simpa only [star_mul, star_star] using congr_arg star (ha.right_assoc (star c) (star b))
  right_assoc b c := by
    simpa only [star_mul, star_star] using congr_arg star (ha.left_assoc (star c) (star b))

/--
theorem `Set.star_centralizer` / 定理 `Set.star_centralizer`

English:
theorem Set.star_centralizer
  statement: star s.centralizer = (star s).centralizer
  proof: by
  simp_rw [centralizer, ← commute_iff_eq]
  conv_lhs => simp only [← star_preimage, preimage_ofPred_eq, ← commute_star_comm]
  conv_rhs => simp only [← image_star, forall_mem_image]

中文:
定理 Set.star_centralizer
  结论: star s.centralizer = (star s).centralizer
  证明: by
  simp_rw [centralizer, ← commute_iff_eq]
  conv_lhs => simp only [← star_preimage, preimage_ofPred_eq, ← commute_star_comm]
  conv_rhs => simp only [← image_star, forall_mem_image]

Depends on / 依赖: centralizer, commute_iff_eq, commute_star_comm, conv_lhs, conv_rhs, forall_mem_image, image_star, preimage_ofPred_eq, simp_rw, star_preimage
-/
theorem Set.star_centralizer : star s.centralizer = (star s).centralizer := by
  simp_rw [centralizer, ← commute_iff_eq]
  conv_lhs => simp only [← star_preimage, preimage_ofPred_eq, ← commute_star_comm]
  conv_rhs => simp only [← image_star, forall_mem_image]

/--
theorem `Set.union_star_self_comm` / 定理 `Set.union_star_self_comm`

English:
theorem Set.union_star_self_comm
  statement: (hcomm : forall x in s, forall y in s, y * x = x * y)
  proof: by
  change s union star s subseteq (s union star s).centralizer
  simp_rw [centralizer_union, ← star_centralizer, union_subset_iff, subset_inter_iff,
    star_subset_star, star_subset]
  exact ⟨⟨hcomm, hcomm_star⟩, ⟨hcomm_star, hcomm⟩⟩

中文:
定理 Set.union_star_self_comm
  结论: (hcomm : 对任意 x in s, 对任意 y in s, y * x = x * y)
  证明: by
  change s union star s subseteq (s union star s).centralizer
  simp_rw [centralizer_union, ← star_centralizer, union_subset_iff, subset_inter_iff,
    star_subset_star, star_subset]
  exact ⟨⟨hcomm, hcomm_star⟩, ⟨hcomm_star, hcomm⟩⟩

Depends on / 依赖: centralizer, centralizer_union, hcomm_star, simp_rw, star_centralizer, star_subset, star_subset_star, subset_inter_iff, subseteq, union_subset_iff
-/
theorem Set.union_star_self_comm (hcomm : forall x in s, forall y in s, y * x = x * y)
    (hcomm_star : forall x in s, forall y in s, y * star x = star x * y) :
    forall x in s union star s, forall y in s union star s, y * x = x * y := by
  change s union star s subseteq (s union star s).centralizer
  simp_rw [centralizer_union, ← star_centralizer, union_subset_iff, subset_inter_iff,
    star_subset_star, star_subset]
  exact ⟨⟨hcomm, hcomm_star⟩, ⟨hcomm_star, hcomm⟩⟩

/--
theorem `Set.star_mem_centralizer'` / 定理 `Set.star_mem_centralizer'`

English:
theorem Set.star_mem_centralizer'
  given: (h : forall a : R, a in s -> star a in s) (ha : a in Set.centralizer s)
  proof: fun y hy => by simpa using congr_arg star (ha _ (h _ hy)).symm

中文:
定理 Set.star_mem_centralizer'
  条件: (h : 对任意 a : R, a in s -> star a in s) (ha : a in Set.centralizer s)
  证明: fun y hy => by simpa using congr_arg star (ha _ (h _ hy)).symm

Depends on / 依赖: congr_arg
-/
theorem Set.star_mem_centralizer' (h : forall a : R, a in s -> star a in s) (ha : a in Set.centralizer s) :
    star a in Set.centralizer s := fun y hy => by simpa using congr_arg star (ha _ (h _ hy)).symm

open scoped Pointwise

/--
theorem `Set.star_mem_centralizer` / 定理 `Set.star_mem_centralizer`

English:
theorem Set.star_mem_centralizer
  given: (ha : a in Set.centralizer (s union star s))
  proof: Set.star_mem_centralizer'
    (fun _x hx => hx.elim (fun hx => Or.inr <| Set.star_mem_star.mpr hx) Or.inl) ha

中文:
定理 Set.star_mem_centralizer
  条件: (ha : a in Set.centralizer (s union star s))
  证明: Set.star_mem_centralizer'
    (fun _x hx => hx.elim (fun hx => Or.inr <| Set.star_mem_star.mpr hx) Or.inl) ha

Depends on / 依赖: Or.inl, Or.inr, Set.star_mem_centralizer, Set.star_mem_star.mpr, hx.elim, star_mem_centralizer, star_mem_star
-/
theorem Set.star_mem_centralizer (ha : a in Set.centralizer (s union star s)) :
    star a in Set.centralizer (s union star s) :=
  Set.star_mem_centralizer'
    (fun _x hx => hx.elim (fun hx => Or.inr <| Set.star_mem_star.mpr hx) Or.inl) ha
