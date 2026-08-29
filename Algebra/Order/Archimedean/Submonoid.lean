/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Submonoids of archimedean monoids

This file defines the instances that show that the (mul)archimedean property is retained in a
submonoid of the ambient group.

## Main statements

* `SubmonoidClass.instMulArchimedean`: the submonoid (and similar subobjects) of a mul-archimedean
  group retains the mul-archimedean property when restricted to the submonoid.
* `AddSubmonoidClass.instArchimedean`: the additive submonoid (and similar subobjects) of an
  archimedean additive group retains the archimedean property when restricted to the additive
  submonoid.
-/

public section

assert_not_exists Finset

@[to_additive]
/--
Instance `SubmonoidClass.instMulArchimedean` / 实例 `SubmonoidClass.instMulArchimedean`

English:
instance SubmonoidClass.instMulArchimedean
  signature: {M S : Type*} [SetLike S M]
  body: by
  constructor
  rintro x _
  simp only [← Subtype.coe_lt_coe, OneMemClass.coe_one]
  exact MulArchimedean.arch x.val

中文:
实例 SubmonoidClass.instMulArchimedean
  签名: {M S : 类型} [SetLike S M]
  定义体: by
  constructor
  rintro x _
  simp only [← Subtype.coe_lt_coe, OneMemClass.coe_one]
  exact MulArchimedean.arch x.val

Depends on / 依赖: MulArchimedean, MulArchimedean.arch, OneMemClass, OneMemClass.coe_one, Subtype, Subtype.coe_lt_coe, coe_lt_coe, coe_one, x.val
-/
instance SubmonoidClass.instMulArchimedean {M S : Type*} [SetLike S M]
    [CommMonoid M] [PartialOrder M]
    [SubmonoidClass S M] [MulArchimedean M] (H : S) : MulArchimedean H := by
  constructor
  rintro x _
  simp only [← Subtype.coe_lt_coe, OneMemClass.coe_one]
  exact MulArchimedean.arch x.val
