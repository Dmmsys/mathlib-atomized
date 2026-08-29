/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Data.Vector.Basic

/-!
# The `zipWith` operation on vectors.
-/

@[expose] public section

namespace List

namespace Vector

section ZipWith

variable {α β γ : Type*} {n : Nat} (f : α -> β -> γ)

/--
Definition of `zipWith` / `zipWith` 的定义

English:
definition zipWith
  signature: : Vector α n -> Vector β n -> Vector γ n
  body: fun x y => ⟨List.zipWith f x.1 y.1, by simp⟩

@[simp]

中文:
定义 zipWith
  签名: : Vector α n -> Vector β n -> Vector γ n
  定义体: fun x y => ⟨List.zipWith f x.1 y.1, by simp⟩

@[simp]

Depends on / 依赖: List.zipWith, zipWith
-/
def zipWith : Vector α n -> Vector β n -> Vector γ n := fun x y => ⟨List.zipWith f x.1 y.1, by simp⟩

@[simp]
/--
theorem `zipWith_toList` / 定理 `zipWith_toList`

English:
theorem zipWith_toList
  given: (x : Vector α n) (y : Vector β n)
  proof: rfl

@[simp]

中文:
定理 zipWith_toList
  条件: (x : Vector α n) (y : Vector β n)
  证明: rfl

@[simp]
-/
theorem zipWith_toList (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).toList = List.zipWith f x.toList y.toList :=
  rfl

@[simp]
/--
theorem `zipWith_get` / 定理 `zipWith_get`

English:
theorem zipWith_get
  given: (x : Vector α n) (y : Vector β n) (i)
  proof: by
  dsimp only [Vector.zipWith, Vector.get]
  simp

@[simp]

中文:
定理 zipWith_get
  条件: (x : Vector α n) (y : Vector β n) (i)
  证明: by
  dsimp only [Vector.zipWith, Vector.get]
  simp

@[simp]

Depends on / 依赖: Vector, Vector.get, Vector.zipWith, zipWith
-/
theorem zipWith_get (x : Vector α n) (y : Vector β n) (i) :
    (Vector.zipWith f x y).get i = f (x.get i) (y.get i) := by
  dsimp only [Vector.zipWith, Vector.get]
  simp

@[simp]
/--
theorem `zipWith_tail` / 定理 `zipWith_tail`

English:
theorem zipWith_tail
  given: (x : Vector α n) (y : Vector β n)
  proof: by
  ext
  simp [get_tail]

@[to_additive]

中文:
定理 zipWith_tail
  条件: (x : Vector α n) (y : Vector β n)
  证明: by
  ext
  simp [get_tail]

@[to_additive]

Depends on / 依赖: get_tail
-/
theorem zipWith_tail (x : Vector α n) (y : Vector β n) :
    (Vector.zipWith f x y).tail = Vector.zipWith f x.tail y.tail := by
  ext
  simp [get_tail]

@[to_additive]
/--
theorem `prod_mul_prod_eq_prod_zipWith` / 定理 `prod_mul_prod_eq_prod_zipWith`

English:
theorem prod_mul_prod_eq_prod_zipWith
  given: [CommMonoid α] (x y : Vector α n)
  proof: List.prod_mul_prod_eq_prod_zipWith_of_length_eq x.toList y.toList
    ((toList_length x).trans (toList_length y).symm)

中文:
定理 prod_mul_prod_eq_prod_zipWith
  条件: [CommMonoid α] (x y : Vector α n)
  证明: List.prod_mul_prod_eq_prod_zipWith_of_length_eq x.toList y.toList
    ((toList_length x).trans (toList_length y).symm)

Depends on / 依赖: List.prod_mul_prod_eq_prod_zipWith_of_length_eq, prod_mul_prod_eq_prod_zipWith_of_length_eq, toList, toList_length, x.toList, y.toList
-/
theorem prod_mul_prod_eq_prod_zipWith [CommMonoid α] (x y : Vector α n) :
    x.toList.prod * y.toList.prod = (Vector.zipWith (· * ·) x y).toList.prod :=
  List.prod_mul_prod_eq_prod_zipWith_of_length_eq x.toList y.toList
    ((toList_length x).trans (toList_length y).symm)

end ZipWith

end Vector

end List
