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
/-
**mulLeftEmbedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulLeftEmbedding [Mul G] [IsLeftCancelMul G] (g : G) : G ↪ G where toFun h
参数：g : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_injective`：mul_right_injective (a : G) : Injective (a * ·)
-/
def mulLeftEmbedding [Mul G] [IsLeftCancelMul G] (g : G) : G ↪ G where
  toFun h := g * h
  inj' := mul_right_injective g

/-- If right-multiplication by any element is cancellative, right-multiplication by `g` is an
embedding. -/
@[to_additive (attr := simps (attr := grind =))
/-- If right-addition by any element is cancellative, right-addition by `g` is an embedding. -/]
/-
**mulRightEmbedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mulRightEmbedding [Mul G] [IsRightCancelMul G] (g : G) : G ↪ G where toFun
 h
参数：g : G。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_injective`：mul_left_injective (a : G) : Function.Injective (· *
 a)
-/
def mulRightEmbedding [Mul G] [IsRightCancelMul G] (g : G) : G ↪ G where
  toFun h := h * g
  inj' := mul_left_injective g

@[to_additive]
/-
**mulLeftEmbedding_eq_mulRightEmbedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mulLeftEmbedding_eq_mulRightEmbedding [CommMagma G] [IsCancelMul G] (g : G
) : mulLeftEmbedding g = mulRightEmbedding g
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem mulLeftEmbedding_eq_mulRightEmbedding [CommMagma G] [IsCancelMul G] (g : G) :
    mulLeftEmbedding g = mulRightEmbedding g := by
  ext
  exact mul_comm _ _

end LeftOrRightCancelSemigroup

