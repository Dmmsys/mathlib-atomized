/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl, Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Product of normed groups and other constructions

This file constructs the infinity norm on finite products of normed groups and provides instances
for type synonyms.
-/

@[expose] public section

open NNReal

variable {ι E F : Type*} {G : ι -> Type*}

/-! ### `PUnit` -/

namespace PUnit

/--
Instance `normedAddCommGroup` / 实例 `normedAddCommGroup`

English:
instance normedAddCommGroup
  signature: : NormedAddCommGroup PUnit where
  body: Function.const _ 0
  dist_eq _ _ := rfl

中文:
实例 normedAddCommGroup
  签名: : 赋范交换加群 命题单元 where
  定义体: Function.const _ 0
  dist_eq _ _ := rfl

Depends on / 依赖: Function, Function.const
-/
instance normedAddCommGroup : NormedAddCommGroup PUnit where
  norm := Function.const _ 0
  dist_eq _ _ := rfl

/--
lemma `norm_eq_zero` / 引理 `norm_eq_zero`

English:
lemma norm_eq_zero
  given: (x : PUnit)
  statement: ‖x‖ = 0
  proof: rfl

中文:
引理 norm_eq_zero
  条件: (x : 命题单元)
  结论: ‖x‖ = 0
  证明: rfl
-/
@[simp] lemma norm_eq_zero (x : PUnit) : ‖x‖ = 0 := rfl

end PUnit

/-! ### `ULift` -/

namespace ULift
section Norm
variable [Norm E]

/--
Instance `norm` / 实例 `norm`

English:
instance norm
  signature: : Norm (ULift E) where norm x
  body: ‖x.down‖

中文:
实例 norm
  签名: : 范数 (类型层提升 E) where norm x
  定义体: ‖x.down‖

Depends on / 依赖: x.down
-/
instance norm : Norm (ULift E) where norm x := ‖x.down‖

/--
lemma `norm_def` / 引理 `norm_def`

English:
lemma norm_def
  given: (x : ULift E)
  statement: ‖x‖ = ‖x.down‖
  proof: rfl

中文:
引理 norm_def
  条件: (x : 类型层提升 E)
  结论: ‖x‖ = ‖x.down‖
  证明: rfl
-/
lemma norm_def (x : ULift E) : ‖x‖ = ‖x.down‖ := rfl

/--
lemma `norm_up` / 引理 `norm_up`

English:
lemma norm_up
  given: (x : E)
  statement: ‖ULift.up x‖ = ‖x‖
  proof: rfl

中文:
引理 norm_up
  条件: (x : E)
  结论: ‖类型层提升.up x‖ = ‖x‖
  证明: rfl
-/
@[simp] lemma norm_up (x : E) : ‖ULift.up x‖ = ‖x‖ := rfl

/--
lemma `norm_down` / 引理 `norm_down`

English:
lemma norm_down
  given: (x : ULift E)
  statement: ‖x.down‖ = ‖x‖
  proof: rfl

中文:
引理 norm_down
  条件: (x : 类型层提升 E)
  结论: ‖x.down‖ = ‖x‖
  证明: rfl
-/
@[simp] lemma norm_down (x : ULift E) : ‖x.down‖ = ‖x‖ := rfl

end Norm

section NNNorm
variable [NNNorm E]

/--
Instance `nnnorm` / 实例 `nnnorm`

English:
instance nnnorm
  signature: : NNNorm (ULift E) where nnnorm x
  body: ‖x.down‖₊

中文:
实例 nnnorm
  签名: : NN范数 (类型层提升 E) where nnnorm x
  定义体: ‖x.down‖₊

Depends on / 依赖: x.down
-/
instance nnnorm : NNNorm (ULift E) where nnnorm x := ‖x.down‖₊

/--
lemma `nnnorm_def` / 引理 `nnnorm_def`

English:
lemma nnnorm_def
  given: (x : ULift E)
  statement: ‖x‖₊ = ‖x.down‖₊
  proof: rfl

中文:
引理 nnnorm_def
  条件: (x : 类型层提升 E)
  结论: ‖x‖₊ = ‖x.down‖₊
  证明: rfl
-/
lemma nnnorm_def (x : ULift E) : ‖x‖₊ = ‖x.down‖₊ := rfl

/--
lemma `nnnorm_up` / 引理 `nnnorm_up`

English:
lemma nnnorm_up
  given: (x : E)
  statement: ‖ULift.up x‖₊ = ‖x‖₊
  proof: rfl

中文:
引理 nnnorm_up
  条件: (x : E)
  结论: ‖类型层提升.up x‖₊ = ‖x‖₊
  证明: rfl
-/
@[simp] lemma nnnorm_up (x : E) : ‖ULift.up x‖₊ = ‖x‖₊ := rfl

/--
lemma `nnnorm_down` / 引理 `nnnorm_down`

English:
lemma nnnorm_down
  given: (x : ULift E)
  statement: ‖x.down‖₊ = ‖x‖₊
  proof: rfl

中文:
引理 nnnorm_down
  条件: (x : 类型层提升 E)
  结论: ‖x.down‖₊ = ‖x‖₊
  证明: rfl
-/
@[simp] lemma nnnorm_down (x : ULift E) : ‖x.down‖₊ = ‖x‖₊ := rfl

end NNNorm

@[to_additive]
/--
Instance `seminormedGroup` / 实例 `seminormedGroup`

English:
instance seminormedGroup
  signature: [SeminormedGroup E]
  body: SeminormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }

@[to_additive]

中文:
实例 seminormedGroup
  签名: [半赋范群 E]
  定义体: SeminormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }

@[to_additive]

Depends on / 依赖: SeminormedGroup, SeminormedGroup.induced, ULift.down, induced, map_mul, map_one
-/
instance seminormedGroup [SeminormedGroup E] : SeminormedGroup (ULift E) :=
  SeminormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }

@[to_additive]
/--
Instance `seminormedCommGroup` / 实例 `seminormedCommGroup`

English:
instance seminormedCommGroup
  signature: [SeminormedCommGroup E]
  body: SeminormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }

@[to_additive]

中文:
实例 seminormedCommGroup
  签名: [SeminormedComm群 E]
  定义体: SeminormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }

@[to_additive]

Depends on / 依赖: SeminormedCommGroup, SeminormedCommGroup.induced, ULift.down, induced, map_mul, map_one
-/
instance seminormedCommGroup [SeminormedCommGroup E] : SeminormedCommGroup (ULift E) :=
  SeminormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }

@[to_additive]
/--
Instance `normedGroup` / 实例 `normedGroup`

English:
instance normedGroup
  signature: [NormedGroup E]
  body: NormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }
  down_injective

@[to_additive]

中文:
实例 normedGroup
  签名: [赋范群 E]
  定义体: NormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }
  down_injective

@[to_additive]

Depends on / 依赖: NormedGroup, NormedGroup.induced, ULift.down, down_injective, induced, map_mul, map_one
-/
instance normedGroup [NormedGroup E] : NormedGroup (ULift E) :=
  NormedGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }
  down_injective

@[to_additive]
/--
Instance `normedCommGroup` / 实例 `normedCommGroup`

English:
instance normedCommGroup
  signature: [NormedCommGroup E]
  body: NormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }
  down_injective

中文:
实例 normedCommGroup
  签名: [NormedComm群 E]
  定义体: NormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }
  down_injective

Depends on / 依赖: NormedCommGroup, NormedCommGroup.induced, ULift.down, down_injective, induced, map_mul, map_one
-/
instance normedCommGroup [NormedCommGroup E] : NormedCommGroup (ULift E) :=
  NormedCommGroup.induced _ _
  { toFun := ULift.down,
    map_one' := rfl,
    map_mul' := fun _ _ => rfl : ULift E ->* E }
  down_injective

end ULift

/-! ### `Additive`, `Multiplicative` -/

section AdditiveMultiplicative

open Additive Multiplicative

section Norm
variable [Norm E]

/--
Instance `Additive.toNorm` / 实例 `Additive.toNorm`

English:
instance Additive.toNorm
  signature: : Norm (Additive E)
  body: ‹Norm E›

中文:
实例 加性.toNorm
  签名: : 范数 (加性 E)
  定义体: ‹Norm E›
-/
instance Additive.toNorm : Norm (Additive E) := ‹Norm E›
/--
Instance `Multiplicative.toNorm` / 实例 `Multiplicative.toNorm`

English:
instance Multiplicative.toNorm
  signature: : Norm (Multiplicative E)
  body: ‹Norm E›

中文:
实例 Multiplicative.toNorm
  签名: : 范数 (Multiplicative E)
  定义体: ‹Norm E›
-/
instance Multiplicative.toNorm : Norm (Multiplicative E) := ‹Norm E›

/--
lemma `norm_toMul` / 引理 `norm_toMul`

English:
lemma norm_toMul
  given: (x : Additive E)
  statement: ‖(x.toMul : E)‖ = ‖x‖
  proof: rfl

中文:
引理 norm_toMul
  条件: (x : 加性 E)
  结论: ‖(x.toMul : E)‖ = ‖x‖
  证明: rfl
-/
@[simp] lemma norm_toMul (x : Additive E) : ‖(x.toMul : E)‖ = ‖x‖ := rfl

/--
lemma `norm_ofMul` / 引理 `norm_ofMul`

English:
lemma norm_ofMul
  given: (x : E)
  statement: ‖ofMul x‖ = ‖x‖
  proof: rfl

中文:
引理 norm_ofMul
  条件: (x : E)
  结论: ‖ofMul x‖ = ‖x‖
  证明: rfl
-/
@[simp] lemma norm_ofMul (x : E) : ‖ofMul x‖ = ‖x‖ := rfl

/--
lemma `norm_toAdd` / 引理 `norm_toAdd`

English:
lemma norm_toAdd
  given: (x : Multiplicative E)
  statement: ‖(x.toAdd : E)‖ = ‖x‖
  proof: rfl

中文:
引理 norm_toAdd
  条件: (x : Multiplicative E)
  结论: ‖(x.toAdd : E)‖ = ‖x‖
  证明: rfl
-/
@[simp] lemma norm_toAdd (x : Multiplicative E) : ‖(x.toAdd : E)‖ = ‖x‖ := rfl

/--
lemma `norm_ofAdd` / 引理 `norm_ofAdd`

English:
lemma norm_ofAdd
  given: (x : E)
  statement: ‖ofAdd x‖ = ‖x‖
  proof: rfl

中文:
引理 norm_ofAdd
  条件: (x : E)
  结论: ‖ofAdd x‖ = ‖x‖
  证明: rfl
-/
@[simp] lemma norm_ofAdd (x : E) : ‖ofAdd x‖ = ‖x‖ := rfl

end Norm

section NNNorm
variable [NNNorm E]

/--
Instance `Additive.toNNNorm` / 实例 `Additive.toNNNorm`

English:
instance Additive.toNNNorm
  signature: : NNNorm (Additive E)
  body: ‹NNNorm E›

中文:
实例 加性.toNNNorm
  签名: : NN范数 (加性 E)
  定义体: ‹NNNorm E›

Depends on / 依赖: NNNorm
-/
instance Additive.toNNNorm : NNNorm (Additive E) := ‹NNNorm E›

/--
Instance `Multiplicative.toNNNorm` / 实例 `Multiplicative.toNNNorm`

English:
instance Multiplicative.toNNNorm
  signature: : NNNorm (Multiplicative E)
  body: ‹NNNorm E›

中文:
实例 Multiplicative.toNNNorm
  签名: : NN范数 (Multiplicative E)
  定义体: ‹NNNorm E›

Depends on / 依赖: NNNorm
-/
instance Multiplicative.toNNNorm : NNNorm (Multiplicative E) := ‹NNNorm E›

/--
lemma `nnnorm_toMul` / 引理 `nnnorm_toMul`

English:
lemma nnnorm_toMul
  given: (x : Additive E)
  statement: ‖(x.toMul : E)‖₊ = ‖x‖₊
  proof: rfl

中文:
引理 nnnorm_toMul
  条件: (x : 加性 E)
  结论: ‖(x.toMul : E)‖₊ = ‖x‖₊
  证明: rfl
-/
@[simp] lemma nnnorm_toMul (x : Additive E) : ‖(x.toMul : E)‖₊ = ‖x‖₊ := rfl

/--
lemma `nnnorm_ofMul` / 引理 `nnnorm_ofMul`

English:
lemma nnnorm_ofMul
  given: (x : E)
  statement: ‖ofMul x‖₊ = ‖x‖₊
  proof: rfl

中文:
引理 nnnorm_ofMul
  条件: (x : E)
  结论: ‖ofMul x‖₊ = ‖x‖₊
  证明: rfl
-/
@[simp] lemma nnnorm_ofMul (x : E) : ‖ofMul x‖₊ = ‖x‖₊ := rfl

/--
lemma `nnnorm_toAdd` / 引理 `nnnorm_toAdd`

English:
lemma nnnorm_toAdd
  given: (x : Multiplicative E)
  statement: ‖(x.toAdd : E)‖₊ = ‖x‖₊
  proof: rfl

中文:
引理 nnnorm_toAdd
  条件: (x : Multiplicative E)
  结论: ‖(x.toAdd : E)‖₊ = ‖x‖₊
  证明: rfl
-/
@[simp] lemma nnnorm_toAdd (x : Multiplicative E) : ‖(x.toAdd : E)‖₊ = ‖x‖₊ := rfl

/--
lemma `nnnorm_ofAdd` / 引理 `nnnorm_ofAdd`

English:
lemma nnnorm_ofAdd
  given: (x : E)
  statement: ‖ofAdd x‖₊ = ‖x‖₊
  proof: rfl

中文:
引理 nnnorm_ofAdd
  条件: (x : E)
  结论: ‖ofAdd x‖₊ = ‖x‖₊
  证明: rfl
-/
@[simp] lemma nnnorm_ofAdd (x : E) : ‖ofAdd x‖₊ = ‖x‖₊ := rfl

end NNNorm

/--
Instance `Additive.seminormedAddGroup` / 实例 `Additive.seminormedAddGroup`

English:
instance Additive.seminormedAddGroup
  signature: [SeminormedGroup E]
  body: dist_eq_norm_inv_mul x.toMul y.toMul

中文:
实例 加性.seminormedAddGroup
  签名: [半赋范群 E]
  定义体: dist_eq_norm_inv_mul x.toMul y.toMul

Depends on / 依赖: dist_eq_norm_inv_mul, x.toMul, y.toMul
-/
instance Additive.seminormedAddGroup [SeminormedGroup E] : SeminormedAddGroup (Additive E) where
  dist_eq x y := dist_eq_norm_inv_mul x.toMul y.toMul


/--
Instance `Multiplicative.seminormedGroup` / 实例 `Multiplicative.seminormedGroup`

English:
instance Multiplicative.seminormedGroup
  signature: [SeminormedAddGroup E]
  body: dist_eq_norm_neg_add x.toAdd y.toAdd

中文:
实例 Multiplicative.seminormedGroup
  签名: [半赋范加群 E]
  定义体: dist_eq_norm_neg_add x.toAdd y.toAdd

Depends on / 依赖: dist_eq_norm_neg_add, x.toAdd, y.toAdd
-/
instance Multiplicative.seminormedGroup [SeminormedAddGroup E] :
    SeminormedGroup (Multiplicative E) where
  dist_eq x y := dist_eq_norm_neg_add x.toAdd y.toAdd

/--
Instance `Additive.seminormedCommGroup` / 实例 `Additive.seminormedCommGroup`

English:
instance Additive.seminormedCommGroup
  signature: [SeminormedCommGroup E]
  body: { Additive.seminormedAddGroup with
    add_comm := add_comm }

中文:
实例 加性.seminormedCommGroup
  签名: [SeminormedComm群 E]
  定义体: { Additive.seminormedAddGroup with
    add_comm := add_comm }

Depends on / 依赖: Additive, Additive.seminormedAddGroup, add_comm, seminormedAddGroup
-/
instance Additive.seminormedCommGroup [SeminormedCommGroup E] :
    SeminormedAddCommGroup (Additive E) :=
  { Additive.seminormedAddGroup with
    add_comm := add_comm }

/--
Instance `Multiplicative.seminormedAddCommGroup` / 实例 `Multiplicative.seminormedAddCommGroup`

English:
instance Multiplicative.seminormedAddCommGroup
  signature: [SeminormedAddCommGroup E]
  body: { Multiplicative.seminormedGroup with
    mul_comm := mul_comm }

中文:
实例 Multiplicative.seminormedAddCommGroup
  签名: [SeminormedAddComm群 E]
  定义体: { Multiplicative.seminormedGroup with
    mul_comm := mul_comm }

Depends on / 依赖: Multiplicative, Multiplicative.seminormedGroup, _pos, exp_pos, le_log_iff_exp_le, log_stirlingSeq_bounded_by_constant, mul_comm, seminormedGroup, stirlingSeq
-/
instance Multiplicative.seminormedAddCommGroup [SeminormedAddCommGroup E] :
    SeminormedCommGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with
    mul_comm := mul_comm }

/--
Instance `Additive.normedAddGroup` / 实例 `Additive.normedAddGroup`

English:
instance Additive.normedAddGroup
  signature: [NormedGroup E]
  body: { Additive.seminormedAddGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 加性.normedAddGroup
  签名: [赋范群 E]
  定义体: { Additive.seminormedAddGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: Additive, Additive.seminormedAddGroup, eq_of_dist_eq_zero, seminormedAddGroup
-/
instance Additive.normedAddGroup [NormedGroup E] : NormedAddGroup (Additive E) :=
  { Additive.seminormedAddGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/--
Instance `Multiplicative.normedGroup` / 实例 `Multiplicative.normedGroup`

English:
instance Multiplicative.normedGroup
  signature: [NormedAddGroup E]
  body: { Multiplicative.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 Multiplicative.normedGroup
  签名: [赋范加群 E]
  定义体: { Multiplicative.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: Multiplicative, Multiplicative.seminormedGroup, eq_of_dist_eq_zero, seminormedGroup
-/
instance Multiplicative.normedGroup [NormedAddGroup E] : NormedGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/--
Instance `Additive.normedAddCommGroup` / 实例 `Additive.normedAddCommGroup`

English:
instance Additive.normedAddCommGroup
  signature: [NormedCommGroup E]
  body: { Additive.seminormedAddGroup with
    add_comm := add_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 加性.normedAddCommGroup
  签名: [NormedComm群 E]
  定义体: { Additive.seminormedAddGroup with
    add_comm := add_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: Additive, Additive.seminormedAddGroup, add_comm, eq_of_dist_eq_zero, seminormedAddGroup
-/
instance Additive.normedAddCommGroup [NormedCommGroup E] : NormedAddCommGroup (Additive E) :=
  { Additive.seminormedAddGroup with
    add_comm := add_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/--
Instance `Multiplicative.normedCommGroup` / 实例 `Multiplicative.normedCommGroup`

English:
instance Multiplicative.normedCommGroup
  signature: [NormedAddCommGroup E]
  body: { Multiplicative.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 Multiplicative.normedCommGroup
  签名: [赋范交换加群 E]
  定义体: { Multiplicative.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: Multiplicative, Multiplicative.seminormedGroup, eq_of_dist_eq_zero, mul_comm, seminormedGroup
-/
instance Multiplicative.normedCommGroup [NormedAddCommGroup E] :
    NormedCommGroup (Multiplicative E) :=
  { Multiplicative.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end AdditiveMultiplicative

/-! ### Order dual -/

section OrderDual
open OrderDual

section Norm
variable [Norm E]

/--
Instance `OrderDual.toNorm` / 实例 `OrderDual.toNorm`

English:
instance OrderDual.toNorm
  signature: : Norm Eᵒᵈ where
  body: ‖ofDual x‖

中文:
实例 OrderDual.toNorm
  签名: : 范数 Eᵒᵈ where
  定义体: ‖ofDual x‖

Depends on / 依赖: ofDual
-/
instance OrderDual.toNorm : Norm Eᵒᵈ where
  norm x := ‖ofDual x‖

/--
lemma `norm_toDual` / 引理 `norm_toDual`

English:
lemma norm_toDual
  given: (x : E)
  statement: ‖toDual x‖ = ‖x‖
  proof: rfl

中文:
引理 norm_toDual
  条件: (x : E)
  结论: ‖toDual x‖ = ‖x‖
  证明: rfl
-/
@[simp] lemma norm_toDual (x : E) : ‖toDual x‖ = ‖x‖ := rfl

/--
lemma `norm_ofDual` / 引理 `norm_ofDual`

English:
lemma norm_ofDual
  given: (x : Eᵒᵈ)
  statement: ‖ofDual x‖ = ‖x‖
  proof: rfl

中文:
引理 norm_ofDual
  条件: (x : Eᵒᵈ)
  结论: ‖ofDual x‖ = ‖x‖
  证明: rfl
-/
@[simp] lemma norm_ofDual (x : Eᵒᵈ) : ‖ofDual x‖ = ‖x‖ := rfl

end Norm

section NNNorm
variable [NNNorm E]

/--
Instance `OrderDual.toNNNorm` / 实例 `OrderDual.toNNNorm`

English:
instance OrderDual.toNNNorm
  signature: : NNNorm Eᵒᵈ where
  body: ‖ofDual x‖₊

中文:
实例 OrderDual.toNNNorm
  签名: : NN范数 Eᵒᵈ where
  定义体: ‖ofDual x‖₊

Depends on / 依赖: ofDual
-/
instance OrderDual.toNNNorm : NNNorm Eᵒᵈ where
  nnnorm x := ‖ofDual x‖₊

/--
lemma `nnnorm_toDual` / 引理 `nnnorm_toDual`

English:
lemma nnnorm_toDual
  given: (x : E)
  statement: ‖toDual x‖₊ = ‖x‖₊
  proof: rfl

中文:
引理 nnnorm_toDual
  条件: (x : E)
  结论: ‖toDual x‖₊ = ‖x‖₊
  证明: rfl
-/
@[simp] lemma nnnorm_toDual (x : E) : ‖toDual x‖₊ = ‖x‖₊ := rfl

/--
lemma `nnnorm_ofDual` / 引理 `nnnorm_ofDual`

English:
lemma nnnorm_ofDual
  given: (x : Eᵒᵈ)
  statement: ‖ofDual x‖₊ = ‖x‖₊
  proof: rfl

中文:
引理 nnnorm_ofDual
  条件: (x : Eᵒᵈ)
  结论: ‖ofDual x‖₊ = ‖x‖₊
  证明: rfl
-/
@[simp] lemma nnnorm_ofDual (x : Eᵒᵈ) : ‖ofDual x‖₊ = ‖x‖₊ := rfl

end NNNorm

namespace OrderDual

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) seminormedGroup [SeminormedGroup E] : SeminormedGroup Eᵒᵈ :=
inferInstanceAs SeminormedGroup E

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) seminormedCommGroup [SeminormedCommGroup E] : SeminormedCommGroup Eᵒᵈ :=
inferInstanceAs SeminormedCommGroup E

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) normedGroup [NormedGroup E] : NormedGroup Eᵒᵈ :=
inferInstanceAs NormedGroup E

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) normedCommGroup [NormedCommGroup E] : NormedCommGroup Eᵒᵈ :=
inferInstanceAs NormedCommGroup E

end OrderDual
end OrderDual

/-! ### Binary product of normed groups -/

section Norm
variable [Norm E] [Norm F] {x : E × F} {r : Real}

/--
Instance `Prod.toNorm` / 实例 `Prod.toNorm`

English:
instance Prod.toNorm
  signature: : Norm (E × F) where norm x
  body: ‖x.1‖ ⊔ ‖x.2‖

中文:
实例 积类型.toNorm
  签名: : 范数 (E × F) where norm x
  定义体: ‖x.1‖ ⊔ ‖x.2‖
-/
instance Prod.toNorm : Norm (E × F) where norm x := ‖x.1‖ ⊔ ‖x.2‖

/--
lemma `Prod.norm_def` / 引理 `Prod.norm_def`

English:
lemma Prod.norm_def
  given: (x : E × F)
  statement: ‖x‖ = max ‖x.1‖ ‖x.2‖
  proof: rfl

中文:
引理 积类型.norm_def
  条件: (x : E × F)
  结论: ‖x‖ = 最大值 ‖x.1‖ ‖x.2‖
  证明: rfl
-/
lemma Prod.norm_def (x : E × F) : ‖x‖ = max ‖x.1‖ ‖x.2‖ := rfl

/--
lemma `Prod.norm_mk` / 引理 `Prod.norm_mk`

English:
lemma Prod.norm_mk
  given: (x : E) (y : F)
  statement: ‖(x, y)‖ = max ‖x‖ ‖y‖
  proof: rfl

中文:
引理 积类型.norm_mk
  条件: (x : E) (y : F)
  结论: ‖(x, y)‖ = 最大值 ‖x‖ ‖y‖
  证明: rfl
-/
@[simp] lemma Prod.norm_mk (x : E) (y : F) : ‖(x, y)‖ = max ‖x‖ ‖y‖ := rfl

/--
lemma `norm_fst_le` / 引理 `norm_fst_le`

English:
lemma norm_fst_le
  given: (x : E × F)
  statement: ‖x.1‖ <= ‖x‖
  proof: le_max_left _ _

中文:
引理 norm_fst_le
  条件: (x : E × F)
  结论: ‖x.1‖ <= ‖x‖
  证明: le_max_left _ _

Depends on / 依赖: le_max_left
-/
lemma norm_fst_le (x : E × F) : ‖x.1‖ <= ‖x‖ := le_max_left _ _

/--
lemma `norm_snd_le` / 引理 `norm_snd_le`

English:
lemma norm_snd_le
  given: (x : E × F)
  statement: ‖x.2‖ <= ‖x‖
  proof: le_max_right _ _

中文:
引理 norm_snd_le
  条件: (x : E × F)
  结论: ‖x.2‖ <= ‖x‖
  证明: le_max_right _ _

Depends on / 依赖: le_max_right
-/
lemma norm_snd_le (x : E × F) : ‖x.2‖ <= ‖x‖ := le_max_right _ _

/--
lemma `norm_prod_le_iff` / 引理 `norm_prod_le_iff`

English:
lemma norm_prod_le_iff
  statement: ‖x‖ <= r ↔ ‖x.1‖ <= r ∧ ‖x.2‖ <= r
  proof: max_le_iff

中文:
引理 norm_prod_le_iff
  结论: ‖x‖ <= r ↔ ‖x.1‖ <= r ∧ ‖x.2‖ <= r
  证明: max_le_iff

Depends on / 依赖: max_le_iff
-/
lemma norm_prod_le_iff : ‖x‖ <= r ↔ ‖x.1‖ <= r ∧ ‖x.2‖ <= r := max_le_iff

end Norm

section SeminormedGroup
variable [SeminormedGroup E] [SeminormedGroup F]

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive /-- Product of seminormed groups, using the sup norm. -/]
/--
Instance `Prod.seminormedGroup` / 实例 `Prod.seminormedGroup`

English:
instance Prod.seminormedGroup
  signature: : SeminormedGroup (E × F) where
  body: by simp [Prod.norm_def, Prod.dist_eq, dist_eq_norm_inv_mul]

中文:
实例 积类型.seminormedGroup
  签名: : 半赋范群 (E × F) where
  定义体: by simp [Prod.norm_def, Prod.dist_eq, dist_eq_norm_inv_mul]

Depends on / 依赖: Prod.dist_eq, Prod.norm_def, dist_eq, dist_eq_norm_inv_mul, norm_def
-/
instance Prod.seminormedGroup : SeminormedGroup (E × F) where
  dist_eq x y := by simp [Prod.norm_def, Prod.dist_eq, dist_eq_norm_inv_mul]

/-- Multiplicative version of `Prod.nnnorm_def`.
Earlier, this name was used for the additive version. -/
@[to_additive Prod.nnnorm_def /-- Additive version of `Prod.nnnorm_def'`.
Earlier, this name was used for the multiplicative version. -/]
/--
lemma `Prod.nnnorm_def'` / 引理 `Prod.nnnorm_def'`

English:
lemma Prod.nnnorm_def'
  given: (x : E × F)
  statement: ‖x‖₊ = max ‖x.1‖₊ ‖x.2‖₊
  proof: rfl

中文:
引理 积类型.nnnorm_def'
  条件: (x : E × F)
  结论: ‖x‖₊ = 最大值 ‖x.1‖₊ ‖x.2‖₊
  证明: rfl
-/
lemma Prod.nnnorm_def' (x : E × F) : ‖x‖₊ = max ‖x.1‖₊ ‖x.2‖₊ := rfl

/-- Multiplicative version of `Prod.nnnorm_mk`. -/
@[to_additive (attr := simp) Prod.nnnorm_mk /-- Additive version of `Prod.nnnorm_mk'`. -/]
/--
lemma `Prod.nnnorm_mk'` / 引理 `Prod.nnnorm_mk'`

English:
lemma Prod.nnnorm_mk'
  given: (x : E) (y : F)
  statement: ‖(x, y)‖₊ = max ‖x‖₊ ‖y‖₊
  proof: rfl

中文:
引理 积类型.nnnorm_mk'
  条件: (x : E) (y : F)
  结论: ‖(x, y)‖₊ = 最大值 ‖x‖₊ ‖y‖₊
  证明: rfl
-/
lemma Prod.nnnorm_mk' (x : E) (y : F) : ‖(x, y)‖₊ = max ‖x‖₊ ‖y‖₊ := rfl

end SeminormedGroup

namespace Prod

/-- Product of seminormed groups, using the sup norm. -/
@[to_additive /-- Product of seminormed groups, using the sup norm. -/]
/--
Instance `seminormedCommGroup` / 实例 `seminormedCommGroup`

English:
instance seminormedCommGroup
  signature: [SeminormedCommGroup E] [SeminormedCommGroup F]
  body: { Prod.seminormedGroup with
    mul_comm := mul_comm }

中文:
实例 seminormedCommGroup
  签名: [SeminormedComm群 E] [SeminormedComm群 F]
  定义体: { Prod.seminormedGroup with
    mul_comm := mul_comm }

Depends on / 依赖: Prod.seminormedGroup, mul_comm, seminormedGroup
-/
instance seminormedCommGroup [SeminormedCommGroup E] [SeminormedCommGroup F] :
    SeminormedCommGroup (E × F) :=
  { Prod.seminormedGroup with
    mul_comm := mul_comm }

/-- Product of normed groups, using the sup norm. -/
@[to_additive /-- Product of normed groups, using the sup norm. -/]
/--
Instance `normedGroup` / 实例 `normedGroup`

English:
instance normedGroup
  signature: [NormedGroup E] [NormedGroup F]
  body: { Prod.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 normedGroup
  签名: [赋范群 E] [赋范群 F]
  定义体: { Prod.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: Prod.seminormedGroup, eq_of_dist_eq_zero, seminormedGroup
-/
instance normedGroup [NormedGroup E] [NormedGroup F] : NormedGroup (E × F) :=
  { Prod.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Product of normed groups, using the sup norm. -/
@[to_additive /-- Product of normed groups, using the sup norm. -/]
/--
Instance `normedCommGroup` / 实例 `normedCommGroup`

English:
instance normedCommGroup
  signature: [NormedCommGroup E] [NormedCommGroup F]
  body: { Prod.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 normedCommGroup
  签名: [NormedComm群 E] [NormedComm群 F]
  定义体: { Prod.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: Prod.seminormedGroup, eq_of_dist_eq_zero, mul_comm, seminormedGroup
-/
instance normedCommGroup [NormedCommGroup E] [NormedCommGroup F] : NormedCommGroup (E × F) :=
  { Prod.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

end Prod

/-! ### Finite product of normed groups -/

section Pi
variable [Fintype ι]

section SeminormedGroup
variable [forall i, SeminormedGroup (G i)] [SeminormedGroup E] (f : forall i, G i) {x : forall i, G i} {r : Real}

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive /-- Finite product of seminormed groups, using the sup norm. -/]
/--
Instance `Pi.seminormedGroup` / 实例 `Pi.seminormedGroup`

English:
instance Pi.seminormedGroup
  signature: : SeminormedGroup (forall i, G i) where
  body: ↑(Finset.univ.sup fun b => ‖f b‖₊)
  dist_eq x y :=
congr_arg (toReal : Real>=0 -> Real)
congr_arg (Finset.sup Finset.univ) funext fun a =>
        show nndist (x a) (y a) = ‖(x a)⁻¹ * y a‖₊ from nndist_eq_nnnorm_inv_mul (x a) (y a)

@[to_additive Pi.norm_def]

中文:
实例 依赖函数类型.seminormedGroup
  签名: : 半赋范群 (对任意 i, G i) where
  定义体: ↑(Finset.univ.sup fun b => ‖f b‖₊)
  dist_eq x y :=
congr_arg (toReal : Real>=0 -> Real)
congr_arg (Finset.sup Finset.univ) funext fun a =>
        show nndist (x a) (y a) = ‖(x a)⁻¹ * y a‖₊ from nndist_eq_nnnorm_inv_mul (x a) (y a)

@[to_additive Pi.norm_def]

Depends on / 依赖: Finset, Finset.univ.sup
-/
instance Pi.seminormedGroup : SeminormedGroup (forall i, G i) where
  norm f := ↑(Finset.univ.sup fun b => ‖f b‖₊)
  dist_eq x y :=
congr_arg (toReal : Real>=0 -> Real)
congr_arg (Finset.sup Finset.univ) funext fun a =>
        show nndist (x a) (y a) = ‖(x a)⁻¹ * y a‖₊ from nndist_eq_nnnorm_inv_mul (x a) (y a)

@[to_additive Pi.norm_def]
/--
lemma `Pi.norm_def'` / 引理 `Pi.norm_def'`

English:
lemma Pi.norm_def'
  statement: ‖f‖ = ↑(Finset.univ.sup fun b => ‖f b‖₊)
  proof: rfl

@[to_additive Pi.nnnorm_def]

中文:
引理 依赖函数类型.norm_def'
  结论: ‖f‖ = ↑(有限集.univ.上确界 fun b => ‖f b‖₊)
  证明: rfl

@[to_additive Pi.nnnorm_def]
-/
lemma Pi.norm_def' : ‖f‖ = ↑(Finset.univ.sup fun b => ‖f b‖₊) := rfl

@[to_additive Pi.nnnorm_def]
/--
lemma `Pi.nnnorm_def'` / 引理 `Pi.nnnorm_def'`

English:
lemma Pi.nnnorm_def'
  statement: ‖f‖₊ = Finset.univ.sup fun b => ‖f b‖₊
  proof: Subtype.eta _ _

中文:
引理 依赖函数类型.nnnorm_def'
  结论: ‖f‖₊ = 有限集.univ.上确界 fun b => ‖f b‖₊
  证明: Subtype.eta _ _

Depends on / 依赖: Subtype, Subtype.eta
-/
lemma Pi.nnnorm_def' : ‖f‖₊ = Finset.univ.sup fun b => ‖f b‖₊ := Subtype.eta _ _

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_le_iff_of_nonneg /-- The seminorm of an element in a product space is `≤ r` if
and only if the norm of each component is. -/]
/--
lemma `pi_norm_le_iff_of_nonneg'` / 引理 `pi_norm_le_iff_of_nonneg'`

English:
lemma pi_norm_le_iff_of_nonneg'
  given: (hr : 0 <= r)
  statement: ‖x‖ <= r ↔ forall i, ‖x i‖ <= r
  proof: by
  simp only [← dist_one_right, dist_pi_le_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_le_iff]

中文:
引理 pi_norm_le_iff_of_nonneg'
  条件: (hr : 0 <= r)
  结论: ‖x‖ <= r ↔ 对任意 i, ‖x i‖ <= r
  证明: by
  simp only [← dist_one_right, dist_pi_le_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_le_iff]

Depends on / 依赖: Pi.one_apply, dist_one_right, dist_pi_le_iff, one_apply
-/
lemma pi_norm_le_iff_of_nonneg' (hr : 0 <= r) : ‖x‖ <= r ↔ forall i, ‖x i‖ <= r := by
  simp only [← dist_one_right, dist_pi_le_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_le_iff]
/--
lemma `pi_nnnorm_le_iff'` / 引理 `pi_nnnorm_le_iff'`

English:
lemma pi_nnnorm_le_iff'
  given: {r : Real>=0}
  statement: ‖x‖₊ <= r ↔ forall i, ‖x i‖₊ <= r
  proof: pi_norm_le_iff_of_nonneg' r.coe_nonneg

@[to_additive pi_norm_le_iff_of_nonempty]

中文:
引理 pi_nnnorm_le_iff'
  条件: {r : 实数>=0}
  结论: ‖x‖₊ <= r ↔ 对任意 i, ‖x i‖₊ <= r
  证明: pi_norm_le_iff_of_nonneg' r.coe_nonneg

@[to_additive pi_norm_le_iff_of_nonempty]

Depends on / 依赖: coe_nonneg, pi_norm_le_iff_of_nonneg, r.coe_nonneg
-/
lemma pi_nnnorm_le_iff' {r : Real>=0} : ‖x‖₊ <= r ↔ forall i, ‖x i‖₊ <= r :=
  pi_norm_le_iff_of_nonneg' r.coe_nonneg

@[to_additive pi_norm_le_iff_of_nonempty]
/--
lemma `pi_norm_le_iff_of_nonempty'` / 引理 `pi_norm_le_iff_of_nonempty'`

English:
lemma pi_norm_le_iff_of_nonempty'
  given: [Nonempty ι]
  statement: ‖f‖ <= r ↔ forall b, ‖f b‖ <= r
  proof: by
  by_cases hr : 0 <= r
  · exact pi_norm_le_iff_of_nonneg' hr
  · exact
      iff_of_false (fun h => hr <| (norm_nonneg' _).trans h) fun h =>
hr (norm_nonneg' _).trans h Classical.arbitrary _

中文:
引理 pi_norm_le_iff_of_nonempty'
  条件: [非空 ι]
  结论: ‖f‖ <= r ↔ 对任意 b, ‖f b‖ <= r
  证明: by
  by_cases hr : 0 <= r
  · exact pi_norm_le_iff_of_nonneg' hr
  · exact
      iff_of_false (fun h => hr <| (norm_nonneg' _).trans h) fun h =>
hr (norm_nonneg' _).trans h Classical.arbitrary _

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, iff_of_false, norm_nonneg, pi_norm_le_iff_of_nonneg
-/
lemma pi_norm_le_iff_of_nonempty' [Nonempty ι] : ‖f‖ <= r ↔ forall b, ‖f b‖ <= r := by
  by_cases hr : 0 <= r
  · exact pi_norm_le_iff_of_nonneg' hr
  · exact
      iff_of_false (fun h => hr <| (norm_nonneg' _).trans h) fun h =>
hr (norm_nonneg' _).trans h Classical.arbitrary _

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
@[to_additive pi_norm_lt_iff /-- The seminorm of an element in a product space is `< r` if and only
if the norm of each component is. -/]
/--
lemma `pi_norm_lt_iff'` / 引理 `pi_norm_lt_iff'`

English:
lemma pi_norm_lt_iff'
  given: (hr : 0 < r)
  statement: ‖x‖ < r ↔ forall i, ‖x i‖ < r
  proof: by
  simp only [← dist_one_right, dist_pi_lt_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_lt_iff]

中文:
引理 pi_norm_lt_iff'
  条件: (hr : 0 < r)
  结论: ‖x‖ < r ↔ 对任意 i, ‖x i‖ < r
  证明: by
  simp only [← dist_one_right, dist_pi_lt_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_lt_iff]

Depends on / 依赖: Pi.one_apply, dist_one_right, dist_pi_lt_iff, one_apply
-/
lemma pi_norm_lt_iff' (hr : 0 < r) : ‖x‖ < r ↔ forall i, ‖x i‖ < r := by
  simp only [← dist_one_right, dist_pi_lt_iff hr, Pi.one_apply]

@[to_additive pi_nnnorm_lt_iff]
/--
lemma `pi_nnnorm_lt_iff'` / 引理 `pi_nnnorm_lt_iff'`

English:
lemma pi_nnnorm_lt_iff'
  given: {r : Real>=0} (hr : 0 < r)
  statement: ‖x‖₊ < r ↔ forall i, ‖x i‖₊ < r
  proof: pi_norm_lt_iff' hr

@[to_additive norm_le_pi_norm]

中文:
引理 pi_nnnorm_lt_iff'
  条件: {r : 实数>=0} (hr : 0 < r)
  结论: ‖x‖₊ < r ↔ 对任意 i, ‖x i‖₊ < r
  证明: pi_norm_lt_iff' hr

@[to_additive norm_le_pi_norm]

Depends on / 依赖: pi_norm_lt_iff
-/
lemma pi_nnnorm_lt_iff' {r : Real>=0} (hr : 0 < r) : ‖x‖₊ < r ↔ forall i, ‖x i‖₊ < r :=
  pi_norm_lt_iff' hr

@[to_additive norm_le_pi_norm]
/--
lemma `norm_le_pi_norm'` / 引理 `norm_le_pi_norm'`

English:
lemma norm_le_pi_norm'
  given: (i : ι)
  statement: ‖f i‖ <= ‖f‖
  proof: (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).1 le_rfl i

@[to_additive nnnorm_le_pi_nnnorm]

中文:
引理 norm_le_pi_norm'
  条件: (i : ι)
  结论: ‖f i‖ <= ‖f‖
  证明: (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).1 le_rfl i

@[to_additive nnnorm_le_pi_nnnorm]

Depends on / 依赖: le_rfl, norm_nonneg, pi_norm_le_iff_of_nonneg
-/
lemma norm_le_pi_norm' (i : ι) : ‖f i‖ <= ‖f‖ :=
  (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).1 le_rfl i

@[to_additive nnnorm_le_pi_nnnorm]
/--
lemma `nnnorm_le_pi_nnnorm'` / 引理 `nnnorm_le_pi_nnnorm'`

English:
lemma nnnorm_le_pi_nnnorm'
  given: (i : ι)
  statement: ‖f i‖₊ <= ‖f‖₊
  proof: norm_le_pi_norm' _ i

@[to_additive pi_norm_const_le]

中文:
引理 nnnorm_le_pi_nnnorm'
  条件: (i : ι)
  结论: ‖f i‖₊ <= ‖f‖₊
  证明: norm_le_pi_norm' _ i

@[to_additive pi_norm_const_le]

Depends on / 依赖: norm_le_pi_norm
-/
lemma nnnorm_le_pi_nnnorm' (i : ι) : ‖f i‖₊ <= ‖f‖₊ :=
  norm_le_pi_norm' _ i

@[to_additive pi_norm_const_le]
/--
lemma `pi_norm_const_le'` / 引理 `pi_norm_const_le'`

English:
lemma pi_norm_const_le'
  given: (a : E)
  statement: ‖fun _ : ι => a‖ <= ‖a‖
  proof: (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).2 fun _ => le_rfl

@[to_additive pi_nnnorm_const_le]

中文:
引理 pi_norm_const_le'
  条件: (a : E)
  结论: ‖fun _ : ι => a‖ <= ‖a‖
  证明: (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).2 fun _ => le_rfl

@[to_additive pi_nnnorm_const_le]

Depends on / 依赖: le_rfl, norm_nonneg, pi_norm_le_iff_of_nonneg
-/
lemma pi_norm_const_le' (a : E) : ‖fun _ : ι => a‖ <= ‖a‖ :=
  (pi_norm_le_iff_of_nonneg' <| norm_nonneg' _).2 fun _ => le_rfl

@[to_additive pi_nnnorm_const_le]
/--
lemma `pi_nnnorm_const_le'` / 引理 `pi_nnnorm_const_le'`

English:
lemma pi_nnnorm_const_le'
  given: (a : E)
  statement: ‖fun _ : ι => a‖₊ <= ‖a‖₊
  proof: pi_norm_const_le' _

@[to_additive (attr := simp) pi_norm_const]

中文:
引理 pi_nnnorm_const_le'
  条件: (a : E)
  结论: ‖fun _ : ι => a‖₊ <= ‖a‖₊
  证明: pi_norm_const_le' _

@[to_additive (attr := simp) pi_norm_const]

Depends on / 依赖: pi_norm_const_le
-/
lemma pi_nnnorm_const_le' (a : E) : ‖fun _ : ι => a‖₊ <= ‖a‖₊ :=
  pi_norm_const_le' _

@[to_additive (attr := simp) pi_norm_const]
/--
lemma `pi_norm_const'` / 引理 `pi_norm_const'`

English:
lemma pi_norm_const'
  given: [Nonempty ι] (a : E)
  statement: ‖fun _i : ι => a‖ = ‖a‖
  proof: by
  simpa only [← dist_one_right] using! dist_pi_const a 1

@[to_additive (attr := simp) pi_nnnorm_const]

中文:
引理 pi_norm_const'
  条件: [非空 ι] (a : E)
  结论: ‖fun _i : ι => a‖ = ‖a‖
  证明: by
  simpa only [← dist_one_right] using! dist_pi_const a 1

@[to_additive (attr := simp) pi_nnnorm_const]

Depends on / 依赖: dist_one_right, dist_pi_const
-/
lemma pi_norm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖ = ‖a‖ := by
  simpa only [← dist_one_right] using! dist_pi_const a 1

@[to_additive (attr := simp) pi_nnnorm_const]
/--
lemma `pi_nnnorm_const'` / 引理 `pi_nnnorm_const'`

English:
lemma pi_nnnorm_const'
  given: [Nonempty ι] (a : E)
  statement: ‖fun _i : ι => a‖₊ = ‖a‖₊
  proof: NNReal.eq pi_norm_const' a

@[to_additive pi_norm_comp_le]

中文:
引理 pi_nnnorm_const'
  条件: [非空 ι] (a : E)
  结论: ‖fun _i : ι => a‖₊ = ‖a‖₊
  证明: NNReal.eq pi_norm_const' a

@[to_additive pi_norm_comp_le]

Depends on / 依赖: NNReal, NNReal.eq, pi_norm_const
-/
lemma pi_nnnorm_const' [Nonempty ι] (a : E) : ‖fun _i : ι => a‖₊ = ‖a‖₊ :=
NNReal.eq pi_norm_const' a

@[to_additive pi_norm_comp_le]
/--
lemma `pi_norm_comp_le'` / 引理 `pi_norm_comp_le'`

English:
lemma pi_norm_comp_le'
  given: [Fintype F] (g : ι -> E) (f : F -> ι)
  statement: ‖g ∘ f‖ <= ‖g‖
  proof: by
  rw [pi_norm_le_iff_of_nonneg' (by positivity)]
  exact fun x => norm_le_pi_norm' g (f x)

@[to_additive IsGreatest.pi_norm]

中文:
引理 pi_norm_comp_le'
  条件: [有限类型 F] (g : ι -> E) (f : F -> ι)
  结论: ‖g ∘ f‖ <= ‖g‖
  证明: by
  rw [pi_norm_le_iff_of_nonneg' (by positivity)]
  exact fun x => norm_le_pi_norm' g (f x)

@[to_additive IsGreatest.pi_norm]

Depends on / 依赖: norm_le_pi_norm, pi_norm_le_iff_of_nonneg
-/
lemma pi_norm_comp_le' [Fintype F] (g : ι -> E) (f : F -> ι) : ‖g ∘ f‖ <= ‖g‖ := by
  rw [pi_norm_le_iff_of_nonneg' (by positivity)]
  exact fun x => norm_le_pi_norm' g (f x)

@[to_additive IsGreatest.pi_norm]
/--
lemma `IsGreatest.pi_norm'` / 引理 `IsGreatest.pi_norm'`

English:
lemma IsGreatest.pi_norm'
  given: [Nonempty ι] (f : ι -> E)
  statement: IsGreatest (Set.range (‖f ·‖)) ‖f‖
  proof: by
  constructor
  · rw [Pi.norm_def' f]
    obtain ⟨x, -, hx⟩ := (Finset.univ (α := ι)).exists_mem_eq_sup (by simp) (‖f ·‖₊)
    simp [hx]
  · rintro - ⟨x, rfl⟩
    exact norm_le_pi_norm' f x

@[to_additive Function.Surjective.pi_norm_comp]

中文:
引理 IsGreatest.pi_norm'
  条件: [非空 ι] (f : ι -> E)
  结论: IsGreatest (集合.range (‖f ·‖)) ‖f‖
  证明: by
  constructor
  · rw [Pi.norm_def' f]
    obtain ⟨x, -, hx⟩ := (Finset.univ (α := ι)).exists_mem_eq_sup (by simp) (‖f ·‖₊)
    simp [hx]
  · rintro - ⟨x, rfl⟩
    exact norm_le_pi_norm' f x

@[to_additive Function.Surjective.pi_norm_comp]

Depends on / 依赖: Finset, Finset.univ, Pi.norm_def, exists_mem_eq_sup, norm_def, norm_le_pi_norm
-/
lemma IsGreatest.pi_norm' [Nonempty ι] (f : ι -> E) : IsGreatest (Set.range (‖f ·‖)) ‖f‖ := by
  constructor
  · rw [Pi.norm_def' f]
    obtain ⟨x, -, hx⟩ := (Finset.univ (α := ι)).exists_mem_eq_sup (by simp) (‖f ·‖₊)
    simp [hx]
  · rintro - ⟨x, rfl⟩
    exact norm_le_pi_norm' f x

@[to_additive Function.Surjective.pi_norm_comp]
/--
lemma `Function.Surjective.pi_norm_comp'` / 引理 `Function.Surjective.pi_norm_comp'`

English:
lemma Function.Surjective.pi_norm_comp'
  statement: [Fintype F] {f : ι -> F} (hf : Function.Surjective f)
  proof: by
  obtain (h | h) := isEmpty_or_nonempty F
  · have : IsEmpty ι := f.isEmpty
    simp [Subsingleton.elim g 1]
  apply le_antisymm (pi_norm_comp_le' g f)
  obtain ⟨⟨x, h⟩, -⟩ := IsGreatest.pi_norm' g
  obtain ⟨y, rfl⟩ := hf x
  exact h ▸ norm_le_pi_norm' (g ∘ f) y

中文:
引理 函数.满射.pi_norm_comp'
  结论: [有限类型 F] {f : ι -> F} (hf : 函数.满射 f)
  证明: by
  obtain (h | h) := isEmpty_or_nonempty F
  · have : IsEmpty ι := f.isEmpty
    simp [Subsingleton.elim g 1]
  apply le_antisymm (pi_norm_comp_le' g f)
  obtain ⟨⟨x, h⟩, -⟩ := IsGreatest.pi_norm' g
  obtain ⟨y, rfl⟩ := hf x
  exact h ▸ norm_le_pi_norm' (g ∘ f) y

Depends on / 依赖: IsEmpty, IsGreatest, IsGreatest.pi_norm, Subsingleton, Subsingleton.elim, f.isEmpty, isEmpty, isEmpty_or_nonempty, le_antisymm, norm_le_pi_norm, pi_norm, pi_norm_comp_le
-/
lemma Function.Surjective.pi_norm_comp' [Fintype F] {f : ι -> F} (hf : Function.Surjective f)
    (g : F -> E) : ‖g ∘ f‖ = ‖g‖ := by
  obtain (h | h) := isEmpty_or_nonempty F
  · have : IsEmpty ι := f.isEmpty
    simp [Subsingleton.elim g 1]
  apply le_antisymm (pi_norm_comp_le' g f)
  obtain ⟨⟨x, h⟩, -⟩ := IsGreatest.pi_norm' g
  obtain ⟨y, rfl⟩ := hf x
  exact h ▸ norm_le_pi_norm' (g ∘ f) y

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_norm_apply_le_norm /-- The $L^1$ norm is less than the $L^\infty$ norm scaled
by the cardinality. -/]
/--
lemma `Pi.sum_norm_apply_le_norm'` / 引理 `Pi.sum_norm_apply_le_norm'`

English:
lemma Pi.sum_norm_apply_le_norm'
  statement: ∑ i, ‖f i‖ <= Fintype.card ι • ‖f‖
  proof: Finset.sum_le_card_nsmul _ _ _ fun i _hi => norm_le_pi_norm' _ i

中文:
引理 依赖函数类型.sum_norm_apply_le_norm'
  结论: ∑ i, ‖f i‖ <= 有限类型.card ι • ‖f‖
  证明: Finset.sum_le_card_nsmul _ _ _ fun i _hi => norm_le_pi_norm' _ i

Depends on / 依赖: Finset, Finset.sum_le_card_nsmul, norm_le_pi_norm, sum_le_card_nsmul
-/
lemma Pi.sum_norm_apply_le_norm' : ∑ i, ‖f i‖ <= Fintype.card ι • ‖f‖ :=
  Finset.sum_le_card_nsmul _ _ _ fun i _hi => norm_le_pi_norm' _ i

/-- The $L^1$ norm is less than the $L^\infty$ norm scaled by the cardinality. -/
@[to_additive Pi.sum_nnnorm_apply_le_nnnorm /-- The $L^1$ norm is less than the $L^\infty$ norm
scaled by the cardinality. -/]
/--
lemma `Pi.sum_nnnorm_apply_le_nnnorm'` / 引理 `Pi.sum_nnnorm_apply_le_nnnorm'`

English:
lemma Pi.sum_nnnorm_apply_le_nnnorm'
  statement: ∑ i, ‖f i‖₊ <= Fintype.card ι • ‖f‖₊
  proof: (NNReal.coe_sum ..).trans_le Pi.sum_norm_apply_le_norm' _

中文:
引理 依赖函数类型.sum_nnnorm_apply_le_nnnorm'
  结论: ∑ i, ‖f i‖₊ <= 有限类型.card ι • ‖f‖₊
  证明: (NNReal.coe_sum ..).trans_le Pi.sum_norm_apply_le_norm' _

Depends on / 依赖: NNReal, NNReal.coe_sum, Pi.sum_norm_apply_le_norm, coe_sum, sum_norm_apply_le_norm, trans_le
-/
lemma Pi.sum_nnnorm_apply_le_nnnorm' : ∑ i, ‖f i‖₊ <= Fintype.card ι • ‖f‖₊ :=
(NNReal.coe_sum ..).trans_le Pi.sum_norm_apply_le_norm' _

end SeminormedGroup

/-- Finite product of seminormed groups, using the sup norm. -/
@[to_additive /-- Finite product of seminormed groups, using the sup norm. -/]
/--
Instance `Pi.seminormedCommGroup` / 实例 `Pi.seminormedCommGroup`

English:
instance Pi.seminormedCommGroup
  signature: [forall i, SeminormedCommGroup (G i)]
  body: { Pi.seminormedGroup with
    mul_comm := mul_comm }

中文:
实例 依赖函数类型.seminormedCommGroup
  签名: [对任意 i, SeminormedComm群 (G i)]
  定义体: { Pi.seminormedGroup with
    mul_comm := mul_comm }

Depends on / 依赖: Pi.seminormedGroup, mul_comm, seminormedGroup
-/
instance Pi.seminormedCommGroup [forall i, SeminormedCommGroup (G i)] : SeminormedCommGroup (forall i, G i) :=
  { Pi.seminormedGroup with
    mul_comm := mul_comm }

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive /-- Finite product of seminormed groups, using the sup norm. -/]
/--
Instance `Pi.normedGroup` / 实例 `Pi.normedGroup`

English:
instance Pi.normedGroup
  signature: [forall i, NormedGroup (G i)]
  body: { Pi.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 依赖函数类型.normedGroup
  签名: [对任意 i, 赋范群 (G i)]
  定义体: { Pi.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: Pi.seminormedGroup, eq_of_dist_eq_zero, seminormedGroup
-/
instance Pi.normedGroup [forall i, NormedGroup (G i)] : NormedGroup (forall i, G i) :=
  { Pi.seminormedGroup with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Finite product of normed groups, using the sup norm. -/
@[to_additive /-- Finite product of seminormed groups, using the sup norm. -/]
/--
Instance `Pi.normedCommGroup` / 实例 `Pi.normedCommGroup`

English:
instance Pi.normedCommGroup
  signature: [forall i, NormedCommGroup (G i)]
  body: { Pi.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

中文:
实例 依赖函数类型.normedCommGroup
  签名: [对任意 i, NormedComm群 (G i)]
  定义体: { Pi.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

Depends on / 依赖: Pi.seminormedGroup, eq_of_dist_eq_zero, mul_comm, seminormedGroup
-/
instance Pi.normedCommGroup [forall i, NormedCommGroup (G i)] : NormedCommGroup (forall i, G i) :=
  { Pi.seminormedGroup with
    mul_comm := mul_comm
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/--
theorem `Pi.nnnorm_single` / 定理 `Pi.nnnorm_single`

English:
theorem Pi.nnnorm_single
  given: [DecidableEq ι] [forall i, NormedAddCommGroup (G i)] {i : ι} (y : G i)
  proof: by
  have H : forall b, ‖single i y b‖₊ = single (M := fun _ => Real>=0) i ‖y‖₊ b := by
    intro b
    refine Pi.apply_single (fun i (x : G i) => ‖x‖₊) ?_ i y b
    simp
  simp [Pi.nnnorm_def, H, Pi.single_apply, Finset.sup_ite, Finset.filter_eq']

中文:
定理 依赖函数类型.nnnorm_single
  条件: [DecidableEq ι] [对任意 i, 赋范交换加群 (G i)] {i : ι} (y : G i)
  证明: by
  have H : forall b, ‖single i y b‖₊ = single (M := fun _ => Real>=0) i ‖y‖₊ b := by
    intro b
    refine Pi.apply_single (fun i (x : G i) => ‖x‖₊) ?_ i y b
    simp
  simp [Pi.nnnorm_def, H, Pi.single_apply, Finset.sup_ite, Finset.filter_eq']

Depends on / 依赖: Finset, Finset.filter_eq, Finset.sup_ite, Pi.apply_single, Pi.nnnorm_def, Pi.single_apply, apply_single, filter_eq, nnnorm_def, single, single_apply, sup_ite
-/
theorem Pi.nnnorm_single [DecidableEq ι] [forall i, NormedAddCommGroup (G i)] {i : ι} (y : G i) :
    ‖Pi.single i y‖₊ = ‖y‖₊ := by
  have H : forall b, ‖single i y b‖₊ = single (M := fun _ => Real>=0) i ‖y‖₊ b := by
    intro b
    refine Pi.apply_single (fun i (x : G i) => ‖x‖₊) ?_ i y b
    simp
  simp [Pi.nnnorm_def, H, Pi.single_apply, Finset.sup_ite, Finset.filter_eq']

/--
lemma `Pi.enorm_single` / 引理 `Pi.enorm_single`

English:
lemma Pi.enorm_single
  given: [DecidableEq ι] [forall i, NormedAddCommGroup (G i)] {i : ι} (y : G i)
  proof: by simp [enorm, Pi.nnnorm_single]

中文:
引理 依赖函数类型.enorm_single
  条件: [DecidableEq ι] [对任意 i, 赋范交换加群 (G i)] {i : ι} (y : G i)
  证明: by simp [enorm, Pi.nnnorm_single]

Depends on / 依赖: Pi.nnnorm_single, nnnorm_single
-/
lemma Pi.enorm_single [DecidableEq ι] [forall i, NormedAddCommGroup (G i)] {i : ι} (y : G i) :
    ‖Pi.single i y‖ₑ = ‖y‖ₑ := by simp [enorm, Pi.nnnorm_single]

/--
theorem `Pi.norm_single` / 定理 `Pi.norm_single`

English:
theorem Pi.norm_single
  given: [DecidableEq ι] [forall i, NormedAddCommGroup (G i)] {i : ι} (y : G i)
  proof: congr_arg Subtype.val Pi.nnnorm_single y

中文:
定理 依赖函数类型.norm_single
  条件: [DecidableEq ι] [对任意 i, 赋范交换加群 (G i)] {i : ι} (y : G i)
  证明: congr_arg Subtype.val Pi.nnnorm_single y

Depends on / 依赖: Pi.nnnorm_single, Subtype, Subtype.val, congr_arg, nnnorm_single
-/
theorem Pi.norm_single [DecidableEq ι] [forall i, NormedAddCommGroup (G i)] {i : ι} (y : G i) :
    ‖Pi.single i y‖ = ‖y‖ :=
congr_arg Subtype.val Pi.nnnorm_single y

end Pi

/-! ### Multiplicative opposite -/

namespace MulOpposite

/--
Instance `instSeminormedAddGroup` / 实例 `instSeminormedAddGroup`

English:
instance instSeminormedAddGroup
  signature: [SeminormedAddGroup E]
  body: instPseudoMetricSpace
  norm x := ‖x.unop‖
  dist_eq _ _ := dist_eq_norm_neg_add _ _

中文:
实例 instSeminormedAddGroup
  签名: [半赋范加群 E]
  定义体: instPseudoMetricSpace
  norm x := ‖x.unop‖
  dist_eq _ _ := dist_eq_norm_neg_add _ _

Depends on / 依赖: instPseudoMetricSpace
-/
instance instSeminormedAddGroup [SeminormedAddGroup E] : SeminormedAddGroup Eᵐᵒᵖ where
  __ := instPseudoMetricSpace
  norm x := ‖x.unop‖
  dist_eq _ _ := dist_eq_norm_neg_add _ _

/--
lemma `norm_op` / 引理 `norm_op`

English:
lemma norm_op
  given: [SeminormedAddGroup E] (a : E)
  statement: ‖MulOpposite.op a‖ = ‖a‖
  proof: rfl

中文:
引理 norm_op
  条件: [半赋范加群 E] (a : E)
  结论: ‖MulOpposite.op a‖ = ‖a‖
  证明: rfl
-/
lemma norm_op [SeminormedAddGroup E] (a : E) : ‖MulOpposite.op a‖ = ‖a‖ := rfl

/--
lemma `norm_unop` / 引理 `norm_unop`

English:
lemma norm_unop
  given: [SeminormedAddGroup E] (a : Eᵐᵒᵖ)
  statement: ‖MulOpposite.unop a‖ = ‖a‖
  proof: rfl

中文:
引理 norm_unop
  条件: [半赋范加群 E] (a : Eᵐᵒᵖ)
  结论: ‖MulOpposite.unop a‖ = ‖a‖
  证明: rfl
-/
lemma norm_unop [SeminormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖ = ‖a‖ := rfl

/--
lemma `nnnorm_op` / 引理 `nnnorm_op`

English:
lemma nnnorm_op
  given: [SeminormedAddGroup E] (a : E)
  statement: ‖MulOpposite.op a‖₊ = ‖a‖₊
  proof: rfl

中文:
引理 nnnorm_op
  条件: [半赋范加群 E] (a : E)
  结论: ‖MulOpposite.op a‖₊ = ‖a‖₊
  证明: rfl
-/
lemma nnnorm_op [SeminormedAddGroup E] (a : E) : ‖MulOpposite.op a‖₊ = ‖a‖₊ := rfl

/--
lemma `nnnorm_unop` / 引理 `nnnorm_unop`

English:
lemma nnnorm_unop
  given: [SeminormedAddGroup E] (a : Eᵐᵒᵖ)
  statement: ‖MulOpposite.unop a‖₊ = ‖a‖₊
  proof: rfl

中文:
引理 nnnorm_unop
  条件: [半赋范加群 E] (a : Eᵐᵒᵖ)
  结论: ‖MulOpposite.unop a‖₊ = ‖a‖₊
  证明: rfl
-/
lemma nnnorm_unop [SeminormedAddGroup E] (a : Eᵐᵒᵖ) : ‖MulOpposite.unop a‖₊ = ‖a‖₊ := rfl

/--
Instance `instNormedAddGroup` / 实例 `instNormedAddGroup`

English:
instance instNormedAddGroup
  signature: [NormedAddGroup E]
  body: instMetricSpace
  __ := instSeminormedAddGroup

中文:
实例 instNormedAddGroup
  签名: [赋范加群 E]
  定义体: instMetricSpace
  __ := instSeminormedAddGroup

Depends on / 依赖: instMetricSpace
-/
instance instNormedAddGroup [NormedAddGroup E] : NormedAddGroup Eᵐᵒᵖ where
  __ := instMetricSpace
  __ := instSeminormedAddGroup

/--
Instance `instSeminormedAddCommGroup` / 实例 `instSeminormedAddCommGroup`

English:
instance instSeminormedAddCommGroup
  signature: [SeminormedAddCommGroup E]
  body: dist_eq_norm_neg_add _ _

中文:
实例 instSeminormedAddCommGroup
  签名: [SeminormedAddComm群 E]
  定义体: dist_eq_norm_neg_add _ _

Depends on / 依赖: dist_eq_norm_neg_add
-/
instance instSeminormedAddCommGroup [SeminormedAddCommGroup E] : SeminormedAddCommGroup Eᵐᵒᵖ where
  dist_eq _ _ := dist_eq_norm_neg_add _ _

/--
Instance `instNormedAddCommGroup` / 实例 `instNormedAddCommGroup`

English:
instance instNormedAddCommGroup
  signature: [NormedAddCommGroup E]
  body: instSeminormedAddCommGroup
  __ := instNormedAddGroup

中文:
实例 instNormedAddCommGroup
  签名: [赋范交换加群 E]
  定义体: instSeminormedAddCommGroup
  __ := instNormedAddGroup

Depends on / 依赖: instSeminormedAddCommGroup
-/
instance instNormedAddCommGroup [NormedAddCommGroup E] : NormedAddCommGroup Eᵐᵒᵖ where
  __ := instSeminormedAddCommGroup
  __ := instNormedAddGroup

end MulOpposite
