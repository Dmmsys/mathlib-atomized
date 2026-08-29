/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-! # Casting lemmas for rational numbers involving sums and products
-/

public section

variable {ι α : Type*}

namespace Rat

section WithDivRing

variable [DivisionRing α] [CharZero α]

@[simp, norm_cast]
/--
theorem `cast_list_sum` / 定理 `cast_list_sum`

English:
theorem cast_list_sum
  given: (s : List Rat)
  statement: (↑s.sum : α) = (s.map (↑)).sum
  proof: map_list_sum (Rat.castHom α) _

@[simp, norm_cast]

中文:
定理 cast_list_sum
  条件: (s : 列表 有理数)
  结论: (↑s.求和 : α) = (s.map (↑)).求和
  证明: map_list_sum (Rat.castHom α) _

@[simp, norm_cast]

Depends on / 依赖: Rat.castHom, castHom, map_list_sum
-/
theorem cast_list_sum (s : List Rat) : (↑s.sum : α) = (s.map (↑)).sum :=
  map_list_sum (Rat.castHom α) _

@[simp, norm_cast]
/--
theorem `cast_multiset_sum` / 定理 `cast_multiset_sum`

English:
theorem cast_multiset_sum
  given: (s : Multiset Rat)
  statement: (↑s.sum : α) = (s.map (↑)).sum
  proof: map_multiset_sum (Rat.castHom α) _

@[simp, norm_cast]

中文:
定理 cast_multiset_sum
  条件: (s : Multiset 有理数)
  结论: (↑s.求和 : α) = (s.map (↑)).求和
  证明: map_multiset_sum (Rat.castHom α) _

@[simp, norm_cast]

Depends on / 依赖: Rat.castHom, castHom, map_multiset_sum
-/
theorem cast_multiset_sum (s : Multiset Rat) : (↑s.sum : α) = (s.map (↑)).sum :=
  map_multiset_sum (Rat.castHom α) _

@[simp, norm_cast]
/--
theorem `cast_sum` / 定理 `cast_sum`

English:
theorem cast_sum
  given: (s : Finset ι) (f : ι -> Rat)
  statement: ∑ i in s, f i = ∑ i in s, (f i : α)
  proof: map_sum (Rat.castHom α) _ s

@[simp, norm_cast]

中文:
定理 cast_sum
  条件: (s : 有限集 ι) (f : ι -> 有理数)
  结论: ∑ i in s, f i = ∑ i in s, (f i : α)
  证明: map_sum (Rat.castHom α) _ s

@[simp, norm_cast]

Depends on / 依赖: Rat.castHom, castHom, map_sum
-/
theorem cast_sum (s : Finset ι) (f : ι -> Rat) : ∑ i in s, f i = ∑ i in s, (f i : α) :=
  map_sum (Rat.castHom α) _ s

@[simp, norm_cast]
/--
theorem `cast_list_prod` / 定理 `cast_list_prod`

English:
theorem cast_list_prod
  given: (s : List Rat)
  statement: (↑s.prod : α) = (s.map (↑)).prod
  proof: map_list_prod (Rat.castHom α) _

中文:
定理 cast_list_prod
  条件: (s : 列表 有理数)
  结论: (↑s.乘积 : α) = (s.map (↑)).乘积
  证明: map_list_prod (Rat.castHom α) _

Depends on / 依赖: Rat.castHom, castHom, map_list_prod
-/
theorem cast_list_prod (s : List Rat) : (↑s.prod : α) = (s.map (↑)).prod :=
  map_list_prod (Rat.castHom α) _

end WithDivRing

section Field

variable [Field α] [CharZero α]

@[simp, norm_cast]
/--
theorem `cast_multiset_prod` / 定理 `cast_multiset_prod`

English:
theorem cast_multiset_prod
  given: (s : Multiset Rat)
  statement: (↑s.prod : α) = (s.map (↑)).prod
  proof: map_multiset_prod (Rat.castHom α) _

@[simp, norm_cast]

中文:
定理 cast_multiset_prod
  条件: (s : Multiset 有理数)
  结论: (↑s.乘积 : α) = (s.map (↑)).乘积
  证明: map_multiset_prod (Rat.castHom α) _

@[simp, norm_cast]

Depends on / 依赖: Rat.castHom, castHom, map_multiset_prod
-/
theorem cast_multiset_prod (s : Multiset Rat) : (↑s.prod : α) = (s.map (↑)).prod :=
  map_multiset_prod (Rat.castHom α) _

@[simp, norm_cast]
/--
theorem `cast_prod` / 定理 `cast_prod`

English:
theorem cast_prod
  given: (s : Finset ι) (f : ι -> Rat)
  statement: ∏ i in s, f i = ∏ i in s, (f i : α)
  proof: map_prod (Rat.castHom α) _ _

中文:
定理 cast_prod
  条件: (s : 有限集 ι) (f : ι -> 有理数)
  结论: ∏ i in s, f i = ∏ i in s, (f i : α)
  证明: map_prod (Rat.castHom α) _ _

Depends on / 依赖: Rat.castHom, castHom, map_prod
-/
theorem cast_prod (s : Finset ι) (f : ι -> Rat) : ∏ i in s, f i = ∏ i in s, (f i : α) :=
  map_prod (Rat.castHom α) _ _

end Field

end Rat
