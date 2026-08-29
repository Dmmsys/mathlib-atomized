/-
Copyright (c) 2021 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Algebra.Group.Defs

/-!
# The embedding of a cancellative semigroup into itself by multiplication by a fixed element.
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

variable {G : Type*}

section LeftOrRightCancelSemigroup

/-- If left-multiplication by any element is cancellative, left-multiplication by `g` is an
embedding. -/
@[to_additive (attr := simps (attr := grind =))
/-- If left-addition by any element is cancellative, left-addition by `g` is an embedding. -/]
/--
Definition of `mulLeftEmbedding` / `mulLeftEmbedding` 的定义

English:
definition mulLeftEmbedding
  signature: [Mul G] [IsLeftCancelMul G] (g : G)
  body: g * h
  inj' := mul_right_injective g

中文:
定义 mulLeftEmbedding
  签名: [乘法 G] [左乘消去 G] (g : G)
  定义体: g * h
  inj' := mul_right_injective g
-/
def mulLeftEmbedding [Mul G] [IsLeftCancelMul G] (g : G) : G ↪ G where
  toFun h := g * h
  inj' := mul_right_injective g

/-- If right-multiplication by any element is cancellative, right-multiplication by `g` is an
embedding. -/
@[to_additive (attr := simps (attr := grind =))
/-- If right-addition by any element is cancellative, right-addition by `g` is an embedding. -/]
/--
Definition of `mulRightEmbedding` / `mulRightEmbedding` 的定义

English:
definition mulRightEmbedding
  signature: [Mul G] [IsRightCancelMul G] (g : G)
  body: h * g
  inj' := mul_left_injective g

@[to_additive]

中文:
定义 mulRightEmbedding
  签名: [乘法 G] [右乘消去 G] (g : G)
  定义体: h * g
  inj' := mul_left_injective g

@[to_additive]
-/
def mulRightEmbedding [Mul G] [IsRightCancelMul G] (g : G) : G ↪ G where
  toFun h := h * g
  inj' := mul_left_injective g

@[to_additive]
/--
theorem `mulLeftEmbedding_eq_mulRightEmbedding` / 定理 `mulLeftEmbedding_eq_mulRightEmbedding`

English:
theorem mulLeftEmbedding_eq_mulRightEmbedding
  given: [CommMagma G] [IsCancelMul G] (g : G)
  proof: by
  ext
  exact mul_comm _ _

中文:
定理 mulLeftEmbedding_eq_mulRightEmbedding
  条件: [交换原群 G] [是消去乘法 G] (g : G)
  证明: by
  ext
  exact mul_comm _ _

Depends on / 依赖: mul_comm
-/
theorem mulLeftEmbedding_eq_mulRightEmbedding [CommMagma G] [IsCancelMul G] (g : G) :
    mulLeftEmbedding g = mulRightEmbedding g := by
  ext
  exact mul_comm _ _

end LeftOrRightCancelSemigroup
