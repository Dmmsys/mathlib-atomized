/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.NNRat.Defs

/-! # Casting lemmas for non-negative rational numbers involving sums and products
-/

public section

variable {α : Type*}

namespace NNRat

section DivisionSemiring

variable {K : Type*} [DivisionSemiring K] [CharZero K]

@[norm_cast]
/--
theorem `cast_listSum` / 定理 `cast_listSum`

English:
theorem cast_listSum
  given: (l : List Rat>=0)
  statement: (l.sum : K) = (l.map (↑)).sum
  proof: map_list_sum (castHom _) _

@[norm_cast]

中文:
定理 cast_listSum
  条件: (l : List Rat>=0)
  结论: (l.sum : K) = (l.map (↑)).sum
  证明: map_list_sum (castHom _) _

@[norm_cast]

Depends on / 依赖: castHom, map_list_sum
-/
theorem cast_listSum (l : List Rat>=0) : (l.sum : K) = (l.map (↑)).sum :=
  map_list_sum (castHom _) _

@[norm_cast]
/--
theorem `cast_listProd` / 定理 `cast_listProd`

English:
theorem cast_listProd
  given: (l : List Rat>=0)
  statement: (l.prod : K) = (l.map (↑)).prod
  proof: map_list_prod (castHom _) _

@[norm_cast]

中文:
定理 cast_listProd
  条件: (l : List Rat>=0)
  结论: (l.prod : K) = (l.map (↑)).prod
  证明: map_list_prod (castHom _) _

@[norm_cast]

Depends on / 依赖: castHom, map_list_prod
-/
theorem cast_listProd (l : List Rat>=0) : (l.prod : K) = (l.map (↑)).prod :=
  map_list_prod (castHom _) _

@[norm_cast]
/--
theorem `cast_multisetSum` / 定理 `cast_multisetSum`

English:
theorem cast_multisetSum
  given: (s : Multiset Rat>=0)
  statement: (s.sum : K) = (s.map (↑)).sum
  proof: map_multiset_sum (castHom _) _

@[norm_cast]

中文:
定理 cast_multisetSum
  条件: (s : Multiset Rat>=0)
  结论: (s.sum : K) = (s.map (↑)).sum
  证明: map_multiset_sum (castHom _) _

@[norm_cast]

Depends on / 依赖: castHom, map_multiset_sum
-/
theorem cast_multisetSum (s : Multiset Rat>=0) : (s.sum : K) = (s.map (↑)).sum :=
  map_multiset_sum (castHom _) _

@[norm_cast]
/--
theorem `cast_sum` / 定理 `cast_sum`

English:
theorem cast_sum
  given: (s : Finset α) (f : α -> Rat>=0)
  statement: ↑(∑ a in s, f a) = ∑ a in s, (f a : K)
  proof: map_sum (castHom _) _ _

中文:
定理 cast_sum
  条件: (s : Finset α) (f : α -> Rat>=0)
  结论: ↑(∑ a in s, f a) = ∑ a in s, (f a : K)
  证明: map_sum (castHom _) _ _

Depends on / 依赖: castHom, map_sum
-/
theorem cast_sum (s : Finset α) (f : α -> Rat>=0) : ↑(∑ a in s, f a) = ∑ a in s, (f a : K) :=
  map_sum (castHom _) _ _

end DivisionSemiring

section Semifield

variable {K : Type*} [Semifield K] [CharZero K]

@[norm_cast]
/--
theorem `cast_multisetProd` / 定理 `cast_multisetProd`

English:
theorem cast_multisetProd
  given: (s : Multiset Rat>=0)
  statement: (s.prod : K) = (s.map (↑)).prod
  proof: map_multiset_prod (castHom _) _

@[norm_cast]

中文:
定理 cast_multisetProd
  条件: (s : Multiset Rat>=0)
  结论: (s.prod : K) = (s.map (↑)).prod
  证明: map_multiset_prod (castHom _) _

@[norm_cast]

Depends on / 依赖: castHom, map_multiset_prod
-/
theorem cast_multisetProd (s : Multiset Rat>=0) : (s.prod : K) = (s.map (↑)).prod :=
  map_multiset_prod (castHom _) _

@[norm_cast]
/--
theorem `cast_prod` / 定理 `cast_prod`

English:
theorem cast_prod
  given: (s : Finset α) (f : α -> Rat>=0)
  statement: ↑(∏ a in s, f a) = ∏ a in s, (f a : K)
  proof: map_prod (castHom _) _ _

中文:
定理 cast_prod
  条件: (s : Finset α) (f : α -> Rat>=0)
  结论: ↑(∏ a in s, f a) = ∏ a in s, (f a : K)
  证明: map_prod (castHom _) _ _

Depends on / 依赖: castHom, map_prod
-/
theorem cast_prod (s : Finset α) (f : α -> Rat>=0) : ↑(∏ a in s, f a) = ∏ a in s, (f a : K) :=
  map_prod (castHom _) _ _

end Semifield

section Rat

/--
theorem `toNNRat_sum_of_nonneg` / 定理 `toNNRat_sum_of_nonneg`

English:
theorem toNNRat_sum_of_nonneg
  given: {s : Finset α} {f : α -> Rat} (hf : forall a, a in s -> 0 <= f a)
  proof: by
  rw [← coe_inj]; rw [cast_sum]; rw [Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Rat.coe_toNNRat _ (hf x hxs)]

中文:
定理 toNNRat_sum_of_nonneg
  条件: {s : Finset α} {f : α -> Rat} (hf : 对任意 a, a in s -> 0 <= f a)
  证明: by
  rw [← coe_inj]; rw [cast_sum]; rw [Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Rat.coe_toNNRat _ (hf x hxs)]

Depends on / 依赖: Finset, Finset.sum_congr, Finset.sum_nonneg, Rat.coe_toNNRat, cast_sum, coe_inj, coe_toNNRat, sum_congr, sum_nonneg
-/
theorem toNNRat_sum_of_nonneg {s : Finset α} {f : α -> Rat} (hf : forall a, a in s -> 0 <= f a) :
    (∑ a in s, f a).toNNRat = ∑ a in s, (f a).toNNRat := by
  rw [← coe_inj]; rw [cast_sum]; rw [Rat.coe_toNNRat _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Rat.coe_toNNRat _ (hf x hxs)]

/--
theorem `toNNRat_prod_of_nonneg` / 定理 `toNNRat_prod_of_nonneg`

English:
theorem toNNRat_prod_of_nonneg
  given: {s : Finset α} {f : α -> Rat} (hf : forall a in s, 0 <= f a)
  proof: by
  rw [← coe_inj]; rw [cast_prod]; rw [Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Rat.coe_toNNRat _ (hf x hxs)]

中文:
定理 toNNRat_prod_of_nonneg
  条件: {s : Finset α} {f : α -> Rat} (hf : 对任意 a in s, 0 <= f a)
  证明: by
  rw [← coe_inj]; rw [cast_prod]; rw [Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Rat.coe_toNNRat _ (hf x hxs)]

Depends on / 依赖: Finset, Finset.prod_congr, Finset.prod_nonneg, Rat.coe_toNNRat, cast_prod, coe_inj, coe_toNNRat, prod_congr, prod_nonneg
-/
theorem toNNRat_prod_of_nonneg {s : Finset α} {f : α -> Rat} (hf : forall a in s, 0 <= f a) :
    (∏ a in s, f a).toNNRat = ∏ a in s, (f a).toNNRat := by
  rw [← coe_inj]; rw [cast_prod]; rw [Rat.coe_toNNRat _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Rat.coe_toNNRat _ (hf x hxs)]

end Rat

end NNRat
