/-
Copyright (c) 2025 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Group.Hom.Instances

/-! # Zero-related `•` instances on group-like morphisms -/

public section

variable {M N A B C : Type*}

namespace ZeroHom

section Zero
variable [Zero A] [Zero B] [Zero C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulZeroClass
  signature: M B] : SMulZeroClass M (ZeroHom A B) where
  body: { toFun a := r • f a
      map_zero' := by simp only [map_zero, smul_zero] }
  smul_zero _ := ext fun _ => smul_zero _

中文:
实例 [SMulZeroClass
  签名: M B] : SMulZeroClass M (ZeroHom A B) where
  定义体: { toFun a := r • f a
      map_zero' := by simp only [map_zero, smul_zero] }
  smul_zero _ := ext fun _ => smul_zero _

Depends on / 依赖: map_zero, smul_zero
-/
instance [SMulZeroClass M B] : SMulZeroClass M (ZeroHom A B) where
  smul r f :=
    { toFun a := r • f a
      map_zero' := by simp only [map_zero, smul_zero] }
  smul_zero _ := ext fun _ => smul_zero _

/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [SMulZeroClass M B] (m : M) (f : ZeroHom A B)
  statement: ⇑(m • f) = m • f
  proof: rfl

中文:
定理 coe_smul
  条件: [SMulZeroClass M B] (m : M) (f : ZeroHom A B)
  结论: ⇑(m • f) = m • f
  证明: rfl
-/
@[norm_cast] theorem coe_smul [SMulZeroClass M B] (m : M) (f : ZeroHom A B) : ⇑(m • f) = m • f :=
  rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: [SMulZeroClass M B] (m : M) (f : ZeroHom A B) (a : A)
  proof: rfl

中文:
定理 smul_apply
  条件: [SMulZeroClass M B] (m : M) (f : ZeroHom A B) (a : A)
  证明: rfl
-/
@[simp] theorem smul_apply [SMulZeroClass M B] (m : M) (f : ZeroHom A B) (a : A) :
    (m • f) a = m • f a := rfl

/--
theorem `smul_comp` / 定理 `smul_comp`

English:
theorem smul_comp
  given: [SMulZeroClass M C] (m : M) (g : ZeroHom B C) (f : ZeroHom A B)
  proof: rfl

中文:
定理 smul_comp
  条件: [SMulZeroClass M C] (m : M) (g : ZeroHom B C) (f : ZeroHom A B)
  证明: rfl
-/
theorem smul_comp [SMulZeroClass M C] (m : M) (g : ZeroHom B C) (f : ZeroHom A B) :
    (m • g).comp f = m • g.comp f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulZeroClass
  signature: M B] [SMulZeroClass N B] [SMulCommClass M N B] :
  body: ext fun _ => smul_comm _ _ _

中文:
实例 [SMulZeroClass
  签名: M B] [SMulZeroClass N B] [SMulCommClass M N B] :
  定义体: ext fun _ => smul_comm _ _ _

Depends on / 依赖: smul_comm
-/
instance [SMulZeroClass M B] [SMulZeroClass N B] [SMulCommClass M N B] :
    SMulCommClass M N (ZeroHom A B) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M N] [SMulZeroClass M B] [SMulZeroClass N B] [IsScalarTower M N B] :
  body: ext fun _ => smul_assoc _ _ _

中文:
实例 [SMul
  签名: M N] [SMulZeroClass M B] [SMulZeroClass N B] [IsScalarTower M N B] :
  定义体: ext fun _ => smul_assoc _ _ _

Depends on / 依赖: smul_assoc
-/
instance [SMul M N] [SMulZeroClass M B] [SMulZeroClass N B] [IsScalarTower M N B] :
    IsScalarTower M N (ZeroHom A B) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMulZeroClass
  signature: M B] [SMulZeroClass Mᵐᵒᵖ B] [IsCentralScalar M B] :
  body: ext fun _ => op_smul_eq_smul _ _

中文:
实例 [SMulZeroClass
  签名: M B] [SMulZeroClass Mᵐᵒᵖ B] [IsCentralScalar M B] :
  定义体: ext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul
-/
instance [SMulZeroClass M B] [SMulZeroClass Mᵐᵒᵖ B] [IsCentralScalar M B] :
    IsCentralScalar M (ZeroHom A B) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: M] [SMulWithZero M B] : SMulWithZero M (ZeroHom A B) where
  body: ext fun _ => zero_smul _ _

中文:
实例 [Zero
  签名: M] [SMulWithZero M B] : SMulWithZero M (ZeroHom A B) where
  定义体: ext fun _ => zero_smul _ _

Depends on / 依赖: zero_smul
-/
instance [Zero M] [SMulWithZero M B] : SMulWithZero M (ZeroHom A B) where
  zero_smul _ := ext fun _ => zero_smul _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MonoidWithZero
  signature: M] [MulActionWithZero M B] : MulActionWithZero M (ZeroHom A B) where
  body: inferInstance
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

中文:
实例 [MonoidWithZero
  签名: M] [MulActionWithZero M B] : MulActionWithZero M (ZeroHom A B) where
  定义体: inferInstance
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
-/
instance [MonoidWithZero M] [MulActionWithZero M B] : MulActionWithZero M (ZeroHom A B) where
  __ : SMulWithZero _ _ := inferInstance
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

end Zero

end ZeroHom

namespace AddMonoidHom

section
variable [AddZeroClass A] [AddZeroClass B] [AddZeroClass C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: M B] : SMulZeroClass M (A ->+ B) where
  body: { toFun a := r • f a
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' _ _ := by simp only [map_add, smul_add] }
  smul_zero _ := ext fun _ => smul_zero _

中文:
实例 [DistribSMul
  签名: M B] : SMulZeroClass M (A ->+ B) where
  定义体: { toFun a := r • f a
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' _ _ := by simp only [map_add, smul_add] }
  smul_zero _ := ext fun _ => smul_zero _

Depends on / 依赖: map_add, map_zero, smul_add, smul_zero
-/
instance [DistribSMul M B] : SMulZeroClass M (A ->+ B) where
  smul r f :=
    { toFun a := r • f a
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' _ _ := by simp only [map_add, smul_add] }
  smul_zero _ := ext fun _ => smul_zero _

/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [DistribSMul M B] (m : M) (f : A ->+ B)
  statement: ⇑(m • f) = m • f
  proof: rfl

中文:
定理 coe_smul
  条件: [DistribSMul M B] (m : M) (f : A ->+ B)
  结论: ⇑(m • f) = m • f
  证明: rfl
-/
@[norm_cast] theorem coe_smul [DistribSMul M B] (m : M) (f : A ->+ B) : ⇑(m • f) = m • f := rfl

/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: [DistribSMul M B] (m : M) (f : A ->+ B) (a : A)
  statement: (m • f) a = m • f a
  proof: rfl

中文:
定理 smul_apply
  条件: [DistribSMul M B] (m : M) (f : A ->+ B) (a : A)
  结论: (m • f) a = m • f a
  证明: rfl
-/
@[simp] theorem smul_apply [DistribSMul M B] (m : M) (f : A ->+ B) (a : A) : (m • f) a = m • f a :=
  rfl

/--
theorem `smul_comp` / 定理 `smul_comp`

English:
theorem smul_comp
  given: [DistribSMul M C] (m : M) (g : B ->+ C) (f : A ->+ B)
  proof: rfl

中文:
定理 smul_comp
  条件: [DistribSMul M C] (m : M) (g : B ->+ C) (f : A ->+ B)
  证明: rfl
-/
theorem smul_comp [DistribSMul M C] (m : M) (g : B ->+ C) (f : A ->+ B) :
    (m • g).comp f = m • g.comp f := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: M B] [DistribSMul N B] [SMulCommClass M N B] :
  body: ext fun _ => smul_comm _ _ _

中文:
实例 [DistribSMul
  签名: M B] [DistribSMul N B] [SMulCommClass M N B] :
  定义体: ext fun _ => smul_comm _ _ _

Depends on / 依赖: smul_comm
-/
instance [DistribSMul M B] [DistribSMul N B] [SMulCommClass M N B] :
    SMulCommClass M N (A ->+ B) where
  smul_comm _ _ _ := ext fun _ => smul_comm _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: M N] [DistribSMul M B] [DistribSMul N B] [IsScalarTower M N B] :
  body: ext fun _ => smul_assoc _ _ _

中文:
实例 [SMul
  签名: M N] [DistribSMul M B] [DistribSMul N B] [IsScalarTower M N B] :
  定义体: ext fun _ => smul_assoc _ _ _

Depends on / 依赖: smul_assoc
-/
instance [SMul M N] [DistribSMul M B] [DistribSMul N B] [IsScalarTower M N B] :
    IsScalarTower M N (A ->+ B) where
  smul_assoc _ _ _ := ext fun _ => smul_assoc _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: M B] [DistribSMul Mᵐᵒᵖ B] [IsCentralScalar M B] :
  body: ext fun _ => op_smul_eq_smul _ _

中文:
实例 [DistribSMul
  签名: M B] [DistribSMul Mᵐᵒᵖ B] [IsCentralScalar M B] :
  定义体: ext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: op_smul_eq_smul
-/
instance [DistribSMul M B] [DistribSMul Mᵐᵒᵖ B] [IsCentralScalar M B] :
    IsCentralScalar M (A ->+ B) where
  op_smul_eq_smul _ _ := ext fun _ => op_smul_eq_smul _ _

end

variable [AddZeroClass A] [AddCommMonoid B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DistribSMul
  signature: M B] : DistribSMul M (A ->+ B) where
  body: ext fun _ => smul_add _ _ _

中文:
实例 [DistribSMul
  签名: M B] : DistribSMul M (A ->+ B) where
  定义体: ext fun _ => smul_add _ _ _

Depends on / 依赖: smul_add
-/
instance [DistribSMul M B] : DistribSMul M (A ->+ B) where
  smul_add _ _ _ := ext fun _ => smul_add _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: M] [DistribMulAction M B] : DistribMulAction M (A ->+ B) where
  body: inferInstance
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

中文:
实例 [Monoid
  签名: M] [DistribMulAction M B] : DistribMulAction M (A ->+ B) where
  定义体: inferInstance
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _
-/
instance [Monoid M] [DistribMulAction M B] : DistribMulAction M (A ->+ B) where
  __ : DistribSMul _ _ := inferInstance
  one_smul _ := ext fun _ => one_smul _ _
  mul_smul _ _ _ := ext fun _ => mul_smul _ _ _

end AddMonoidHom
