/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Fintype.Vector

/-!
# Finiteness of vector types
-/

public section

variable {α : Type*}

/--
Instance `List.Vector.finite` / 实例 `List.Vector.finite`

English:
instance List.Vector.finite
  signature: [Finite α] {n : Nat}
  body: by
  have := Fintype.ofFinite α
  infer_instance

中文:
实例 列表.Vector.finite
  签名: [有限 α] {n : 自然数}
  定义体: by
  have := Fintype.ofFinite α
  infer_instance

Depends on / 依赖: Fintype, Fintype.ofFinite, infer_instance, ofFinite
-/
instance List.Vector.finite [Finite α] {n : Nat} : Finite (Vector α n) := by
  have := Fintype.ofFinite α
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] {n
  body: by
  have := Fintype.ofFinite α
  infer_instance

中文:
实例 [有限
  签名: α] {n
  定义体: by
  have := Fintype.ofFinite α
  infer_instance

Depends on / 依赖: Fintype, Fintype.ofFinite, infer_instance, ofFinite
-/
instance [Finite α] {n : Nat} : Finite (Sym α n) := by
  have := Fintype.ofFinite α
  infer_instance
