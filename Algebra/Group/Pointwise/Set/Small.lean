/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Logic.Small.Set

/-!
# Small instances for pointwise operations
-/

public section

universe u

variable {α β : Type*} (s t : Set α)

open scoped Pointwise

/--
Instance `small_set_zero` / 实例 `small_set_zero`

English:
instance small_set_zero
  signature: [Zero α]
  body: small_single _

中文:
实例 small_set_zero
  签名: [零 α]
  定义体: small_single _

Depends on / 依赖: small_single
-/
instance small_set_zero [Zero α] : Small.{u} (0 : Set α) := small_single _
/--
Instance `small_set_one` / 实例 `small_set_one`

English:
instance small_set_one
  signature: [One α]
  body: small_single _

中文:
实例 small_set_one
  签名: [幺 α]
  定义体: small_single _

Depends on / 依赖: small_single
-/
instance small_set_one [One α] : Small.{u} (1 : Set α) := small_single _

/--
Instance `small_neg` / 实例 `small_neg`

English:
instance small_neg
  signature: [InvolutiveNeg α] [Small.{u} s]
  body: by
  rw [← Set.image_neg_eq_neg]
  infer_instance

中文:
实例 small_neg
  签名: [InvolutiveNeg α] [Small.{u} s]
  定义体: by
  rw [← Set.image_neg_eq_neg]
  infer_instance

Depends on / 依赖: Set.image_neg_eq_neg, image_neg_eq_neg, infer_instance
-/
instance small_neg [InvolutiveNeg α] [Small.{u} s] : Small.{u} (-s :) := by
  rw [← Set.image_neg_eq_neg]
  infer_instance

/--
Instance `small_add` / 实例 `small_add`

English:
instance small_add
  signature: [Add α] [Small.{u} s] [Small.{u} t]
  body: small_image2 ..

中文:
实例 small_add
  签名: [加法 α] [Small.{u} s] [Small.{u} t]
  定义体: small_image2 ..

Depends on / 依赖: small_image2
-/
instance small_add [Add α] [Small.{u} s] [Small.{u} t] : Small.{u} (s + t) := small_image2 ..
/--
Instance `small_sub` / 实例 `small_sub`

English:
instance small_sub
  signature: [Sub α] [Small.{u} s] [Small.{u} t]
  body: small_image2 ..

中文:
实例 small_sub
  签名: [减法 α] [Small.{u} s] [Small.{u} t]
  定义体: small_image2 ..

Depends on / 依赖: small_image2
-/
instance small_sub [Sub α] [Small.{u} s] [Small.{u} t] : Small.{u} (s - t) := small_image2 ..
/--
Instance `small_mul` / 实例 `small_mul`

English:
instance small_mul
  signature: [Mul α] [Small.{u} s] [Small.{u} t]
  body: small_image2 ..

中文:
实例 small_mul
  签名: [乘法 α] [Small.{u} s] [Small.{u} t]
  定义体: small_image2 ..

Depends on / 依赖: small_image2
-/
instance small_mul [Mul α] [Small.{u} s] [Small.{u} t] : Small.{u} (s * t) := small_image2 ..
/--
Instance `small_div` / 实例 `small_div`

English:
instance small_div
  signature: [Div α] [Small.{u} s] [Small.{u} t]
  body: small_image2 ..

中文:
实例 small_div
  签名: [除法 α] [Small.{u} s] [Small.{u} t]
  定义体: small_image2 ..

Depends on / 依赖: small_image2
-/
instance small_div [Div α] [Small.{u} s] [Small.{u} t] : Small.{u} (s / t) := small_image2 ..
