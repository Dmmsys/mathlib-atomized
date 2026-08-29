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
/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [Group G] [MulAction G β]
  body: ⟨fun g f => f.trans (MulAction.toPerm g).toEmbedding⟩

@[to_additive]

中文:
实例 smul
  签名: [群 G] [乘法作用 G β]
  定义体: ⟨fun g f => f.trans (MulAction.toPerm g).toEmbedding⟩

@[to_additive]

Depends on / 依赖: MulAction, MulAction.toPerm, f.trans, toEmbedding, toPerm
-/
instance smul [Group G] [MulAction G β] : SMul G (α ↪ β) :=
  ⟨fun g f => f.trans (MulAction.toPerm g).toEmbedding⟩

@[to_additive]
/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: [Group G] [MulAction G β] (g : G) (f : α ↪ β)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 smul_def
  条件: [群 G] [乘法作用 G β] (g : G) (f : α ↪ β)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem smul_def [Group G] [MulAction G β] (g : G) (f : α ↪ β) :
    g • f = f.trans (MulAction.toPerm g).toEmbedding :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: [Group G] [MulAction G β] (g : G) (f : α ↪ β) (a : α)
  statement: (g • f) a = g • f a
  proof: rfl

@[to_additive]

中文:
定理 smul_apply
  条件: [群 G] [乘法作用 G β] (g : G) (f : α ↪ β) (a : α)
  结论: (g • f) a = g • f a
  证明: rfl

@[to_additive]
-/
theorem smul_apply [Group G] [MulAction G β] (g : G) (f : α ↪ β) (a : α) : (g • f) a = g • f a :=
  rfl

@[to_additive]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [Group G] [MulAction G β] (g : G) (f : α ↪ β)
  statement: ⇑(g • f) = g • ⇑f
  proof: rfl

中文:
定理 coe_smul
  条件: [群 G] [乘法作用 G β] (g : G) (f : α ↪ β)
  结论: ⇑(g • f) = g • ⇑f
  证明: rfl
-/
theorem coe_smul [Group G] [MulAction G β] (g : G) (f : α ↪ β) : ⇑(g • f) = g • ⇑f :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: G] [Group G'] [SMul G G'] [MulAction G β] [MulAction G' β]
  body: ⟨fun x y z => Function.Embedding.ext fun i => smul_assoc x y (z i)⟩

@[to_additive]

中文:
实例 [群
  签名: G] [群 G'] [标量乘法 G G'] [乘法作用 G β] [乘法作用 G' β]
  定义体: ⟨fun x y z => Function.Embedding.ext fun i => smul_assoc x y (z i)⟩

@[to_additive]

Depends on / 依赖: Embedding, Function, Function.Embedding.ext, smul_assoc
-/
instance [Group G] [Group G'] [SMul G G'] [MulAction G β] [MulAction G' β]
    [IsScalarTower G G' β] : IsScalarTower G G' (α ↪ β) :=
  ⟨fun x y z => Function.Embedding.ext fun i => smul_assoc x y (z i)⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: G] [Group G'] [MulAction G β] [MulAction G' β] [SMulCommClass G G' β] :
  body: ⟨fun x y z => Function.Embedding.ext fun i => smul_comm x y (z i)⟩

中文:
实例 [群
  签名: G] [群 G'] [乘法作用 G β] [乘法作用 G' β] [标量交换类 G G' β] :
  定义体: ⟨fun x y z => Function.Embedding.ext fun i => smul_comm x y (z i)⟩

Depends on / 依赖: Embedding, Function, Function.Embedding.ext, smul_comm
-/
instance [Group G] [Group G'] [MulAction G β] [MulAction G' β] [SMulCommClass G G' β] :
    SMulCommClass G G' (α ↪ β) :=
  ⟨fun x y z => Function.Embedding.ext fun i => smul_comm x y (z i)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: G] [MulAction G β] [MulAction Gᵐᵒᵖ β] [IsCentralScalar G β] :
  body: ⟨fun _ _ => Function.Embedding.ext fun _ => op_smul_eq_smul _ _⟩

@[to_additive]

中文:
实例 [群
  签名: G] [乘法作用 G β] [乘法作用 Gᵐᵒᵖ β] [中心标量 G β] :
  定义体: ⟨fun _ _ => Function.Embedding.ext fun _ => op_smul_eq_smul _ _⟩

@[to_additive]

Depends on / 依赖: Embedding, Function, Function.Embedding.ext, op_smul_eq_smul
-/
instance [Group G] [MulAction G β] [MulAction Gᵐᵒᵖ β] [IsCentralScalar G β] :
    IsCentralScalar G (α ↪ β) :=
  ⟨fun _ _ => Function.Embedding.ext fun _ => op_smul_eq_smul _ _⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: G] [MulAction G β] : MulAction G (α ↪ β)
  body: DFunLike.coe_injective.mulAction _ coe_smul

中文:
实例 [群
  签名: G] [乘法作用 G β] : 乘法作用 G (α ↪ β)
  定义体: DFunLike.coe_injective.mulAction _ coe_smul

Depends on / 依赖: DFunLike, DFunLike.coe_injective.mulAction, coe_injective, coe_smul, mulAction
-/
instance [Group G] [MulAction G β] : MulAction G (α ↪ β) :=
  DFunLike.coe_injective.mulAction _ coe_smul

end Function.Embedding
