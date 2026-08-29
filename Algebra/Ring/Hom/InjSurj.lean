/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.Ring.Defs

/-!
# Pulling back rings along injective maps, and pushing them forward along surjective maps
-/

public section

open Function

variable {α β : Type*}

/--
theorem `Function.Injective.isDomain` / 定理 `Function.Injective.isDomain`

English:
theorem Function.Injective.isDomain
  statement: [Semiring α] [IsDomain α] [Semiring β] {F}
  proof: domain_nontrivial f (map_zero _) (map_one _)
  __ := hf.isCancelMulZero f (map_zero _) (map_mul _)

中文:
定理 函数.单射.isDomain
  结论: [半环 α] [是整环 α] [半环 β] {F}
  证明: domain_nontrivial f (map_zero _) (map_one _)
  __ := hf.isCancelMulZero f (map_zero _) (map_mul _)
-/
protected theorem Function.Injective.isDomain [Semiring α] [IsDomain α] [Semiring β] {F}
    [FunLike F β α] [MonoidWithZeroHomClass F β α] (f : F) (hf : Injective f) : IsDomain β where
  __ := domain_nontrivial f (map_zero _) (map_one _)
  __ := hf.isCancelMulZero f (map_zero _) (map_mul _)
