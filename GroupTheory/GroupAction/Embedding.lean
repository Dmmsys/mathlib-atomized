/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Opposite

/-!
# Group actions on embeddings

This file provides a `MulAction G (α ↪ β)` instance that agrees with the `MulAction G (α → β)`
instances defined by `Pi.mulAction`.

Note that unlike the `Pi` instance, this requires `G` to be a group.
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u v w

variable {G G' α β : Type*}

namespace Function.Embedding

@[to_additive]
/-
**Function.Embedding.smul** 是 Mathlib 中的一个实例，位于命名空间 `Function.Embedding`。
形式化陈述：smul [Group G] [MulAction G β] : SMul G (α ↪ β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul [Group G] [MulAction G β] : SMul G (α ↪ β) :=
  ⟨fun g f => f.trans (MulAction.toPerm g).toEmbedding⟩

@[to_additive]
/-
**Function.Embedding.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：smul_def [Group G] [MulAction G β] (g : G) (f : α ↪ β) : g • f = f.trans (
MulAction.toPerm g).toEmbedding
参数：g : G；f : α ↪ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def [Group G] [MulAction G β] (g : G) (f : α ↪ β) :
    g • f = f.trans (MulAction.toPerm g).toEmbedding :=
  rfl

@[to_additive (attr := simp)]
/-
**Function.Embedding.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：smul_apply [Group G] [MulAction G β] (g : G) (f : α ↪ β) (a : α) : (g • f)
 a = g • f a
参数：g : G；f : α ↪ β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply [Group G] [MulAction G β] (g : G) (f : α ↪ β) (a : α) : (g • f) a = g • f a :=
  rfl

@[to_additive]
/-
**Function.Embedding.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Function.Embedding`。
形式化陈述：coe_smul [Group G] [MulAction G β] (g : G) (f : α ↪ β) : ⇑(g • f) = g • ⇑f
参数：g : G；f : α ↪ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul [Group G] [MulAction G β] (g : G) (f : α ↪ β) : ⇑(g • f) = g • ⇑f :=
  rfl
/-
**Function.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `Function.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group G] [Group G'] [SMul G G'] [MulAction G β] [MulAction G' β]
    [IsScalarTower G G' β] : IsScalarTower G G' (α ↪ β) :=
  ⟨fun x y z => Function.Embedding.ext fun i => smul_assoc x y (z i)⟩

@[to_additive]
/-
**Function.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `Function.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group G] [Group G'] [MulAction G β] [MulAction G' β] [SMulCommClass G G' β] :
    SMulCommClass G G' (α ↪ β) :=
  ⟨fun x y z => Function.Embedding.ext fun i => smul_comm x y (z i)⟩
/-
**Function.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `Function.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group G] [MulAction G β] [MulAction Gᵐᵒᵖ β] [IsCentralScalar G β] :
    IsCentralScalar G (α ↪ β) :=
  ⟨fun _ _ => Function.Embedding.ext fun _ => op_smul_eq_smul _ _⟩

@[to_additive]
/-
**Function.Embedding.** 是 Mathlib 中的一个实例，位于命名空间 `Function.Embedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group G] [MulAction G β] : MulAction G (α ↪ β) :=
  DFunLike.coe_injective.mulAction _ coe_smul

end Function.Embedding

